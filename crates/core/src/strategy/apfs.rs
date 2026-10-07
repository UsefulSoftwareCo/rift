use super::{Strategy, create_destination};
use crate::{CopyMode, Error, Result, filter::CopyFilter};
use std::fs;
use std::path::Path;
use walkdir::WalkDir;

pub(super) struct ApfsStrategy;

impl Strategy for ApfsStrategy {
    fn copy_directory(&self, from: &Path, to: &Path, mode: CopyMode) -> Result<()> {
        match mode {
            CopyMode::All => clone_tree_apfs(from, to),
            CopyMode::Filtered => clone_filtered_directory_apfs(from, to),
        }
    }
}

fn clone_filtered_directory_apfs(from: &Path, to: &Path) -> Result<()> {
    use std::collections::HashMap;
    use std::os::unix::fs::MetadataExt;

    let filter = CopyFilter;
    let mut hard_links = HashMap::new();
    let mut directories = Vec::new();
    create_destination(to)?;
    for entry in WalkDir::new(from)
        .min_depth(1)
        .follow_links(false)
        .into_iter()
        .filter_entry(|entry| {
            entry
                .path()
                .strip_prefix(from)
                .map_or(true, |path| !filter.excludes(path))
        })
    {
        let entry = entry?;
        let source = entry.path();
        let destination = to.join(
            source
                .strip_prefix(from)
                .map_err(|error| Error::Path(error.to_string()))?,
        );
        let metadata = fs::symlink_metadata(source)?;
        let file_type = metadata.file_type();
        if file_type.is_dir() {
            fs::create_dir(&destination)?;
            directories.push((source.to_path_buf(), destination));
        } else if file_type.is_file() {
            let key = (metadata.dev(), metadata.ino());
            if metadata.nlink() > 1 {
                if let Some(existing) = hard_links.get(&key) {
                    fs::hard_link(existing, &destination)?;
                } else {
                    clone_path_apfs(source, &destination)?;
                    hard_links.insert(key, destination.clone());
                }
            } else {
                clone_path_apfs(source, &destination)?;
            }
            // `clonefile` reproduces ownership, timestamps, and extended
            // attributes but drops setuid and setgid, so only the mode needs
            // reapplying. Replaying the rest fails on entries the caller
            // cannot rewrite.
            fs::set_permissions(&destination, metadata.permissions())
                .map_err(|error| io_at("set permissions", &destination, error))?;
        } else if file_type.is_symlink() {
            std::os::unix::fs::symlink(fs::read_link(source)?, &destination)?;
            copy_metadata_apfs(source, &destination)?;
        } else {
            return Err(Error::UnsupportedEntry(source.to_path_buf()));
        }
    }
    for (source, destination) in directories.into_iter().rev() {
        copy_metadata_apfs(&source, &destination)?;
    }
    copy_metadata_apfs(from, to)?;
    Ok(())
}

/// Clones a directory tree in one `clonefile` call. The kernel refuses the
/// whole call with `EACCES` when any file inside is unreadable or any directory
/// inside is unreadable or unsearchable, even one the caller owns, and the
/// error names only the root. A refused call leaves nothing behind, so the
/// source is scanned for a likely culprit. The source is not changed.
fn clone_tree_apfs(from: &Path, to: &Path) -> Result<()> {
    clonefile(&c_path(from)?, &c_path(to)?).map_err(|error| refused_clone_error(from, to, error))
}

/// Keeps the kernel's error and adds an entry that blocks whole-tree cloning
/// when one is found. The source is blamed only when the destination parent
/// looks writable and the scan finds an entry the caller is denied. Any other
/// scan failure is inconclusive.
fn refused_clone_error(from: &Path, to: &Path, error: std::io::Error) -> Error {
    if !is_denied(&error) || destination_refuses(to) {
        return clone_error(from, to, error);
    }
    match find_blocked_entry(from) {
        Ok(Some(blocked)) => Error::BlockedEntry {
            root: from.to_path_buf(),
            path: blocked.path,
            problem: blocked.problem,
            permission: blocked.permission,
            source: error,
        },
        Ok(None) | Err(_) => clone_error(from, to, error),
    }
}

/// The kernel also refuses a clone with `EACCES` or `EPERM` when the
/// destination parent is not writable or is immutable. An append-only parent
/// still accepts a new entry, so it does not refuse the clone.
fn destination_refuses(to: &Path) -> bool {
    use std::os::macos::fs::MetadataExt;

    let parent = match to.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent,
        _ => Path::new("."),
    };
    if !matches!(accessible(parent, libc::W_OK | libc::X_OK), Ok(true)) {
        return true;
    }
    let flags = libc::UF_IMMUTABLE | libc::SF_IMMUTABLE;
    fs::metadata(parent).map_or(true, |metadata| metadata.st_flags() & flags != 0)
}

struct Blocked {
    path: std::path::PathBuf,
    problem: &'static str,
    permission: &'static str,
}

/// Finds the first entry the caller is denied, which makes a whole-tree clone
/// of `root` fail. `node_modules` directories are large and rarely the cause,
/// so they are searched only after the rest of the tree comes up clean. An
/// `Err` means the scan could not finish, so nothing can be blamed.
fn find_blocked_entry(root: &Path) -> std::io::Result<Option<Blocked>> {
    let mut deferred = Vec::new();
    if let Some(blocked) = scan_for_blocked_entry(root, Some(&mut deferred))? {
        return Ok(Some(blocked));
    }
    for path in &deferred {
        if let Some(blocked) = scan_for_blocked_entry(path, None)? {
            return Ok(Some(blocked));
        }
    }
    Ok(None)
}

fn scan_for_blocked_entry(
    from: &Path,
    mut deferred: Option<&mut Vec<std::path::PathBuf>>,
) -> std::io::Result<Option<Blocked>> {
    let mut entries = WalkDir::new(from).follow_links(false).into_iter();
    while let Some(entry) = entries.next() {
        let entry = match entry {
            Ok(entry) => entry,
            Err(error) => {
                let denied = error.io_error().is_some_and(is_denied);
                return match error.path() {
                    Some(path) if denied => Ok(Some(blocked(path, "an unreadable entry", "u+r"))),
                    _ => Err(error
                        .into_io_error()
                        .unwrap_or_else(|| std::io::Error::other("filesystem loop"))),
                };
            }
        };
        let path = entry.path();
        let file_type = entry.file_type();
        if file_type.is_dir() {
            match (accessible(path, libc::R_OK)?, accessible(path, libc::X_OK)?) {
                (true, true) => {}
                (true, false) => {
                    return Ok(Some(blocked(
                        path,
                        "a directory without search permission",
                        "u+x",
                    )));
                }
                (false, true) => {
                    return Ok(Some(blocked(path, "an unreadable directory", "u+r")));
                }
                (false, false) => {
                    return Ok(Some(blocked(
                        path,
                        "an unreadable directory without search permission",
                        "u+rx",
                    )));
                }
            }
            if entry.depth() > 0
                && entry.file_name() == "node_modules"
                && let Some(deferred) = deferred.as_deref_mut()
            {
                deferred.push(path.to_path_buf());
                entries.skip_current_dir();
            }
        } else if file_type.is_file() && !accessible(path, libc::R_OK)? {
            return Ok(Some(blocked(path, "an unreadable file", "u+r")));
        }
    }
    Ok(None)
}

fn is_denied(error: &std::io::Error) -> bool {
    matches!(error.raw_os_error(), Some(libc::EACCES | libc::EPERM))
}

/// Returns whether the caller has `mode` access to `path`. Only `EACCES` and
/// `EPERM` mean access is denied; any other failure is returned as an error.
fn accessible(path: &Path, mode: libc::c_int) -> std::io::Result<bool> {
    let path = c_path(path).map_err(|error| {
        std::io::Error::new(std::io::ErrorKind::InvalidInput, error.to_string())
    })?;
    // SAFETY: `path` is a null-terminated C string that lives for the call.
    if unsafe { libc::access(path.as_ptr(), mode) } == 0 {
        return Ok(true);
    }
    let error = std::io::Error::last_os_error();
    if is_denied(&error) {
        return Ok(false);
    }
    Err(error)
}

fn blocked(path: &Path, problem: &'static str, permission: &'static str) -> Blocked {
    Blocked {
        path: path.to_path_buf(),
        problem,
        permission,
    }
}

fn clone_path_apfs(from: &Path, to: &Path) -> Result<()> {
    clonefile(&c_path(from)?, &c_path(to)?).map_err(|error| clone_error(from, to, error))
}

fn clonefile(source: &std::ffi::CStr, destination: &std::ffi::CStr) -> std::io::Result<()> {
    // SAFETY: `source` and `destination` are null-terminated C strings that
    // live for the duration of the call.
    if unsafe { libc::clonefile(source.as_ptr(), destination.as_ptr(), 0) } == 0 {
        return Ok(());
    }
    Err(std::io::Error::last_os_error())
}

/// Only a filesystem or volume that cannot clone means copy-on-write is
/// unavailable. Other errors, such as permissions, `ENOSPC` or `EIO`, are
/// reported as a failed clone of `from`.
fn clone_error(from: &Path, to: &Path, error: std::io::Error) -> Error {
    if error.kind() == std::io::ErrorKind::AlreadyExists {
        return Error::AlreadyExists(to.to_path_buf());
    }
    match error.raw_os_error() {
        Some(libc::ENOTSUP | libc::EOPNOTSUPP | libc::EXDEV) => {
            Error::CowUnavailable(format!("failed to clone {}: {}", from.display(), error))
        }
        _ => io_at("clone", from, error),
    }
}

/// Replays metadata onto a directory or symlink created fresh at `to`. Cloned
/// files never come through here; `clonefile` already carries their metadata.
fn copy_metadata_apfs(from: &Path, to: &Path) -> Result<()> {
    use std::os::unix::fs::MetadataExt;

    let metadata =
        fs::symlink_metadata(from).map_err(|error| io_at("read metadata", from, error))?;
    let destination = c_path(to)?;

    // Ownership is preserved on a best-effort basis. Only a privileged caller
    // can assign a uid it does not own or a gid it does not belong to, and a
    // copy owned by the caller is still a correct copy.
    // SAFETY: `destination` is a valid null-terminated path, and uid/gid come
    // from filesystem metadata for `from`.
    if unsafe { libc::lchown(destination.as_ptr(), metadata.uid(), metadata.gid()) } != 0 {
        let error = std::io::Error::last_os_error();
        if error.raw_os_error() != Some(libc::EPERM) {
            return Err(io_at("change ownership", to, error));
        }
    }
    // Extended attributes must be copied before the mode is applied. `setxattr`
    // requires write access, so a read-only entry would otherwise lock its own
    // copy.
    copy_xattrs_apfs(from, to)?;
    if !metadata.file_type().is_symlink() {
        fs::set_permissions(to, metadata.permissions())
            .map_err(|error| io_at("set permissions", to, error))?;
    }
    let times = [
        libc::timespec {
            tv_sec: metadata.atime(),
            tv_nsec: metadata.atime_nsec(),
        },
        libc::timespec {
            tv_sec: metadata.mtime(),
            tv_nsec: metadata.mtime_nsec(),
        },
    ];
    // SAFETY: `destination` is a live C string and `times` contains exactly the
    // two timestamps expected by `utimensat`.
    if unsafe {
        libc::utimensat(
            libc::AT_FDCWD,
            destination.as_ptr(),
            times.as_ptr(),
            libc::AT_SYMLINK_NOFOLLOW,
        )
    } != 0
    {
        return Err(io_at("set timestamps", to, std::io::Error::last_os_error()));
    }
    Ok(())
}

fn copy_xattrs_apfs(from: &Path, to: &Path) -> Result<()> {
    let source = c_path(from)?;
    let destination = c_path(to)?;
    let read_failed = || {
        io_at(
            "read extended attribute",
            from,
            std::io::Error::last_os_error(),
        )
    };
    let write_failed = || {
        io_at(
            "set extended attribute",
            to,
            std::io::Error::last_os_error(),
        )
    };
    // SAFETY: `source` is a valid C path. A null buffer with size 0 asks the
    // kernel for the required list size.
    let size = unsafe {
        libc::listxattr(
            source.as_ptr(),
            std::ptr::null_mut(),
            0,
            libc::XATTR_NOFOLLOW,
        )
    };
    if size < 0 {
        return Err(read_failed());
    }
    let mut names = vec![0_u8; size as usize];
    // SAFETY: `names` was allocated with the size reported by the previous
    // `listxattr` call, and its pointer is valid for writes of that length.
    if size > 0
        && unsafe {
            libc::listxattr(
                source.as_ptr(),
                names.as_mut_ptr().cast(),
                names.len(),
                libc::XATTR_NOFOLLOW,
            )
        } < 0
    {
        return Err(read_failed());
    }
    for name in names
        .split(|byte| *byte == 0)
        .filter(|name| !name.is_empty())
    {
        let name = std::ffi::CString::new(name)
            .map_err(|_| Error::Path("extended attribute name contains a null byte".into()))?;
        // SAFETY: `source` and `name` are valid C strings. A null buffer with
        // size 0 asks the kernel for this attribute's value length.
        let size = unsafe {
            libc::getxattr(
                source.as_ptr(),
                name.as_ptr(),
                std::ptr::null_mut(),
                0,
                0,
                libc::XATTR_NOFOLLOW,
            )
        };
        if size < 0 {
            return Err(read_failed());
        }
        let mut value = vec![0_u8; size as usize];
        // SAFETY: `value` was allocated with the exact size reported by
        // `getxattr`, and the path and attribute name are valid C strings.
        if size > 0
            && unsafe {
                libc::getxattr(
                    source.as_ptr(),
                    name.as_ptr(),
                    value.as_mut_ptr().cast(),
                    value.len(),
                    0,
                    libc::XATTR_NOFOLLOW,
                )
            } < 0
        {
            return Err(read_failed());
        }
        // SAFETY: `destination`, `name`, and `value` are valid for the duration
        // of the call. `XATTR_NOFOLLOW` keeps symlink behavior consistent.
        if unsafe {
            libc::setxattr(
                destination.as_ptr(),
                name.as_ptr(),
                value.as_ptr().cast(),
                value.len(),
                0,
                libc::XATTR_NOFOLLOW,
            )
        } != 0
        {
            return Err(write_failed());
        }
    }
    Ok(())
}

fn io_at(operation: &'static str, path: &Path, source: std::io::Error) -> Error {
    Error::IoAt {
        operation,
        path: path.to_path_buf(),
        source,
    }
}

fn c_path(path: &Path) -> Result<std::ffi::CString> {
    use std::os::unix::ffi::OsStrExt;

    std::ffi::CString::new(path.as_os_str().as_bytes())
        .map_err(|_| Error::Path(format!("path contains a null byte: {}", path.display())))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    use tempfile::TempDir;

    #[test]
    fn strategy_clones_and_removes_a_workspace() {
        let temp = TempDir::new().unwrap();
        let source = temp.path().join("source");
        let destination = temp.path().join("destination");
        fs::create_dir(&source).unwrap();
        fs::create_dir(source.join("nested")).unwrap();
        fs::write(source.join("nested/file.txt"), "hello").unwrap();
        let strategy = ApfsStrategy;

        strategy
            .copy_directory(&source, &destination, CopyMode::All)
            .unwrap();
        assert_eq!(
            fs::read_to_string(destination.join("nested/file.txt")).unwrap(),
            "hello"
        );
        strategy.remove_directory(&destination).unwrap();
        assert!(!destination.exists());
    }

    /// Regression: the kernel refuses a whole-tree `clonefile` with `EACCES`
    /// when any directory inside lacks the search bit, even one the caller
    /// owns. Two empty `0644` directories in a checkout made every
    /// `rift create --copy-all` from it fail with an error that named only the
    /// root and blamed copy-on-write support.
    #[test]
    fn full_copy_names_a_directory_without_search_permission() {
        if unsafe { libc::geteuid() } == 0 {
            return;
        }
        let temp = TempDir::new().unwrap();
        let source = temp.path().join("source");
        let destination = temp.path().join("destination");
        let unsearchable = source.join("lib");
        fs::create_dir_all(source.join("node_modules/pkg")).unwrap();
        fs::write(source.join("node_modules/pkg/index.js"), "module").unwrap();
        fs::create_dir(&unsearchable).unwrap();
        fs::set_permissions(&unsearchable, fs::Permissions::from_mode(0o644)).unwrap();

        let error = ApfsStrategy
            .copy_directory(&source, &destination, CopyMode::All)
            .unwrap_err();

        assert!(
            matches!(&error, Error::BlockedEntry { path, permission: "u+x", .. } if path == &unsearchable),
            "{error:?}"
        );
        let message = error.to_string();
        assert!(
            message.contains(&format!("chmod u+x {}", unsearchable.display())),
            "{message}"
        );
        assert!(!message.contains("copy-on-write"), "{message}");
        assert!(!destination.exists());
        assert_eq!(
            fs::metadata(&unsearchable).unwrap().permissions().mode() & 0o777,
            0o644
        );
        fs::set_permissions(&unsearchable, fs::Permissions::from_mode(0o755)).unwrap();
        assert_eq!(
            fs::read_to_string(source.join("node_modules/pkg/index.js")).unwrap(),
            "module"
        );
    }

    /// `node_modules` is searched last, but a blocked entry inside it is still
    /// named.
    #[test]
    fn full_copy_names_a_blocked_entry_inside_node_modules() {
        if unsafe { libc::geteuid() } == 0 {
            return;
        }
        let temp = TempDir::new().unwrap();
        let source = temp.path().join("source");
        let destination = temp.path().join("destination");
        let unreadable = source.join("node_modules/pkg/index.js");
        fs::create_dir_all(source.join("node_modules/pkg")).unwrap();
        fs::write(&unreadable, "module").unwrap();
        fs::write(source.join("file.txt"), "hello").unwrap();
        fs::set_permissions(&unreadable, fs::Permissions::from_mode(0o200)).unwrap();

        let result = ApfsStrategy.copy_directory(&source, &destination, CopyMode::All);

        fs::set_permissions(&unreadable, fs::Permissions::from_mode(0o644)).unwrap();
        let error = result.unwrap_err();
        assert!(
            matches!(&error, Error::BlockedEntry { path, permission: "u+r", .. } if path == &unreadable),
            "{error:?}"
        );
        assert!(!destination.exists());
    }

    /// Only a filesystem that cannot clone means copy-on-write is unavailable.
    #[test]
    fn clone_errors_name_copy_on_write_only_when_it_is_unavailable() {
        let from = Path::new("/source");
        let to = Path::new("/destination");
        for errno in [libc::ENOSPC, libc::EIO, libc::EACCES] {
            let message =
                clone_error(from, to, std::io::Error::from_raw_os_error(errno)).to_string();
            assert!(
                message.starts_with("clone failed for /source: "),
                "{message}"
            );
        }
        for errno in [libc::EXDEV, libc::ENOTSUP] {
            assert!(matches!(
                clone_error(from, to, std::io::Error::from_raw_os_error(errno)),
                Error::CowUnavailable(_)
            ));
        }
    }

    #[test]
    fn integration_environment_is_required_by_ci() {
        if std::env::var_os("RIFT_REQUIRE_APFS_TESTS").is_some() {
            let temp = TempDir::new().unwrap();
            let source = temp.path().join("source");
            let destination = temp.path().join("destination");
            fs::create_dir(&source).unwrap();
            assert!(
                ApfsStrategy
                    .copy_directory(&source, &destination, CopyMode::All)
                    .is_ok()
            );
        }
    }

    fn caller_groups() -> Vec<u32> {
        let mut groups = vec![0_u32; 64];
        // SAFETY: the buffer is sized by `groups.len()` and valid for writes.
        let count = unsafe { libc::getgroups(groups.len() as i32, groups.as_mut_ptr()) };
        if count < 0 {
            return Vec::new();
        }
        groups.truncate(count as usize);
        groups
    }

    fn read_xattr(path: &Path, name: &str) -> Option<Vec<u8>> {
        let path = c_path(path).unwrap();
        let name = std::ffi::CString::new(name).unwrap();
        // SAFETY: both C strings are live, and a null buffer asks for the size.
        let size = unsafe {
            libc::getxattr(
                path.as_ptr(),
                name.as_ptr(),
                std::ptr::null_mut(),
                0,
                0,
                libc::XATTR_NOFOLLOW,
            )
        };
        if size < 0 {
            return None;
        }
        let mut value = vec![0_u8; size as usize];
        // SAFETY: `value` is sized by the probe above and valid for writes.
        let read = unsafe {
            libc::getxattr(
                path.as_ptr(),
                name.as_ptr(),
                value.as_mut_ptr().cast(),
                value.len(),
                0,
                libc::XATTR_NOFOLLOW,
            )
        };
        if read < 0 { None } else { Some(value) }
    }

    fn write_xattr(path: &Path, name: &str, value: &[u8]) {
        let path = c_path(path).unwrap();
        let name = std::ffi::CString::new(name).unwrap();
        // SAFETY: all three pointers are live for the duration of the call.
        let result = unsafe {
            libc::setxattr(
                path.as_ptr(),
                name.as_ptr(),
                value.as_ptr().cast(),
                value.len(),
                0,
                libc::XATTR_NOFOLLOW,
            )
        };
        assert_eq!(result, 0, "failed to seed an extended attribute");
    }

    /// Regression: Git object files are `0444`, and every file on recent macOS
    /// carries `com.apple.provenance`. Applying the mode before the extended
    /// attributes made `setxattr` fail with `EACCES`, so `rift create` could not
    /// copy any Git repository.
    #[test]
    fn filtered_strategy_copies_read_only_files() {
        let temp = TempDir::new().unwrap();
        let source = temp.path().join("source");
        let destination = temp.path().join("destination");
        let objects = source.join(".git/objects/0d");
        fs::create_dir_all(&objects).unwrap();
        let object = objects.join("8a474f");
        fs::write(&object, "object").unwrap();
        write_xattr(&object, "user.rift", b"marked");
        fs::set_permissions(&object, fs::Permissions::from_mode(0o444)).unwrap();

        ApfsStrategy
            .copy_directory(&source, &destination, CopyMode::Filtered)
            .unwrap();

        let copied = destination.join(".git/objects/0d/8a474f");
        assert_eq!(fs::read_to_string(&copied).unwrap(), "object");
        assert_eq!(
            fs::metadata(&copied).unwrap().permissions().mode() & 0o777,
            0o444
        );
        assert_eq!(
            read_xattr(&copied, "user.rift").as_deref(),
            Some(&b"marked"[..])
        );
    }

    /// Regression: a source file may belong to a group the caller is not a
    /// member of, such as `wheel`. An unprivileged `lchown` then fails with
    /// `EPERM`, which must not abort the copy: preserving ownership is a
    /// privileged operation, and a copy owned by the caller is still correct.
    #[test]
    fn filtered_strategy_copies_entries_owned_by_another_group() {
        // `/private/tmp` belongs to `wheel`, and a new entry inherits its
        // parent's group, so this yields a source the caller does not share a
        // group with — without needing privilege to set it up.
        let Ok(source_root) = TempDir::new_in("/private/tmp") else {
            return;
        };
        let source = source_root.path().join("source");
        let nested = source.join("nested");
        fs::create_dir_all(&nested).unwrap();
        fs::write(nested.join("file.txt"), "hello").unwrap();

        let foreign = fs::metadata(&nested).unwrap().gid();
        if caller_groups().contains(&foreign) {
            // The caller shares the group after all; nothing to prove.
            assert!(
                std::env::var_os("RIFT_REQUIRE_APFS_TESTS").is_none(),
                "the environment cannot produce an entry owned by a foreign group"
            );
            return;
        }

        // The destination inherits a different group, so reproducing the source
        // group here is the privileged operation that must not be fatal.
        let destination_root = TempDir::new().unwrap();
        let destination = destination_root.path().join("destination");
        ApfsStrategy
            .copy_directory(&source, &destination, CopyMode::Filtered)
            .unwrap();

        assert_eq!(
            fs::read_to_string(destination.join("nested/file.txt")).unwrap(),
            "hello"
        );
    }

    /// Regression: a directory that the owner cannot write must still receive
    /// its extended attributes, which requires copying them before the mode.
    #[test]
    fn filtered_strategy_copies_read_only_directories() {
        let temp = TempDir::new().unwrap();
        let source = temp.path().join("source");
        let destination = temp.path().join("destination");
        let locked = source.join("locked");
        fs::create_dir_all(&locked).unwrap();
        fs::write(locked.join("file.txt"), "hello").unwrap();
        write_xattr(&locked, "user.rift", b"dir");
        fs::set_permissions(&locked, fs::Permissions::from_mode(0o555)).unwrap();

        let result = ApfsStrategy.copy_directory(&source, &destination, CopyMode::Filtered);

        // Restore write access so the temporary directory can be cleaned up.
        fs::set_permissions(&locked, fs::Permissions::from_mode(0o755)).unwrap();
        result.unwrap();

        let copied = destination.join("locked");
        assert_eq!(
            fs::metadata(&copied).unwrap().permissions().mode() & 0o777,
            0o555
        );
        assert_eq!(
            read_xattr(&copied, "user.rift").as_deref(),
            Some(&b"dir"[..])
        );
        fs::set_permissions(&copied, fs::Permissions::from_mode(0o755)).unwrap();
    }

    #[test]
    fn filtered_strategy_preserves_included_metadata_and_hard_links() {
        let temp = TempDir::new().unwrap();
        let source = temp.path().join("source");
        let destination = temp.path().join("destination");
        let nested = source.join("nested");
        fs::create_dir(&source).unwrap();
        fs::set_permissions(&source, fs::Permissions::from_mode(0o750)).unwrap();
        fs::create_dir(&nested).unwrap();
        fs::set_permissions(&nested, fs::Permissions::from_mode(0o710)).unwrap();
        let file = nested.join("file.txt");
        fs::write(&file, "hello").unwrap();
        write_xattr(&file, "com.rift.test", b"preserved");
        // `clonefile` drops setuid and setgid, so the special bits verify that
        // the mode is reapplied.
        fs::set_permissions(&file, fs::Permissions::from_mode(0o6555)).unwrap();
        fs::hard_link(&file, nested.join("hard.txt")).unwrap();
        std::os::unix::fs::symlink("file.txt", nested.join("link.txt")).unwrap();
        fs::create_dir_all(source.join("node_modules/pkg")).unwrap();
        fs::write(source.join("node_modules/pkg/index.js"), "module").unwrap();

        ApfsStrategy
            .copy_directory(&source, &destination, CopyMode::Filtered)
            .unwrap();

        assert!(!destination.join("node_modules").exists());
        assert_eq!(
            fs::read_to_string(destination.join("nested/file.txt")).unwrap(),
            "hello"
        );
        assert_eq!(
            fs::read_link(destination.join("nested/link.txt")).unwrap(),
            Path::new("file.txt")
        );
        assert_eq!(
            fs::metadata(destination.join("nested/file.txt"))
                .unwrap()
                .ino(),
            fs::metadata(destination.join("nested/hard.txt"))
                .unwrap()
                .ino()
        );
        assert_eq!(
            fs::metadata(destination.join("nested/file.txt"))
                .unwrap()
                .permissions()
                .mode()
                & 0o7777,
            0o6555
        );
        assert_eq!(
            read_xattr(&destination.join("nested/file.txt"), "com.rift.test").as_deref(),
            Some(&b"preserved"[..])
        );
        assert_eq!(
            fs::metadata(destination.join("nested"))
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o710
        );
        assert_eq!(
            fs::metadata(&destination).unwrap().permissions().mode() & 0o777,
            0o750
        );
    }
}
