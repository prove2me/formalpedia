-- Prove2me | Definitions.Def_Arm64_Syscalls_Fs_ReadWrite
-- name    : Arm64_Syscalls_Fs_ReadWrite
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:05:31.413434+00:00
-- url     : https://prove2.me/theorems/0170f141-7b0b-4eb8-a743-773f5abad152
-- title:
--   Arm64.Trusted.Syscalls.Fs.ReadWrite — Linux VFS Read, Write, and Seek Syscalls
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Fs/ReadWrite.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Fs/ReadWrite.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Fs/ReadWrite.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Fs/ReadWrite.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Fs/ReadWrite.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Syscalls_Common

/-!
# Linux VFS Read, Write, and Seek Syscalls

Trusted Computing Base model of Linux `lseek` (`__NR_lseek = 62`), `read` (`__NR_read = 63`),
`write` (`__NR_write = 64`), and `pread64` (`__NR_pread64 = 67`) over `FsState` (`fs/read_write.c`
in Linux 7.3).
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `lseek` syscall number (`__NR_lseek = 62`, `include/uapi/asm-generic/unistd.h:204`, `fs/read_write.c:324`). -/
def SYS_LSEEK : BitVec 64 := 62#64

/-- Linux AArch64 `read` syscall number (`__NR_read = 63`, `include/uapi/asm-generic/unistd.h:206`, `fs/read_write.c:709`). -/
def SYS_READ : BitVec 64 := 63#64

/-- Linux AArch64 `write` syscall number (`__NR_write = 64`, `include/uapi/asm-generic/unistd.h:208`, `fs/read_write.c:733`). -/
def SYS_WRITE : BitVec 64 := 64#64

/-- Linux AArch64 `pread64` syscall number (`__NR_pread64 = 67`, `include/uapi/asm-generic/unistd.h:214`, `fs/read_write.c:756`). -/
def SYS_PREAD64 : BitVec 64 := 67#64

/-- Current byte contents of regular file `path` in `fs` (`[]` if absent or a directory). -/
def FsState.fileBytes (fs : FsState) (path : String) : List (BitVec 8) :=
  match fs.files path with
  | some (.file bs) => bs
  | _ => []

/-- Effective starting byte offset for `write` on `desc` in `fs` (`(fs.fileBytes desc.path).length`
    when `O_APPEND` is set, otherwise `desc.offset`; `fs/read_write.c:1735` `generic_write_checks`). -/
def FsState.writePos (fs : FsState) (desc : FdEntry) : Nat :=
  if desc.append then (fs.fileBytes desc.path).length else desc.offset

/-- Overwrite or extend `old` starting at byte offset `pos` with `src`, zero-padding any gap
    (`fs/read_write.c:588` `vfs_write`). -/
def writeFileBytes (old : List (BitVec 8)) (pos : Nat) (src : List (BitVec 8)) : List (BitVec 8) :=
  let pre := if pos ≤ old.length then old.take pos else old ++ List.replicate (pos - old.length) 0#8
  pre ++ src ++ old.drop (pos + src.length)

/-- Conservative cross-filesystem regular-file offset/size bound (`0xffffffff = 4,294,967,295`
    bytes, `4 GiB - 1`): lies at or below `s_maxbytes` across `tmpfs` (`MAX_LFS_FILESIZE = 2 ^ 63 - 1`),
    1 KiB/2 KiB/4 KiB-block and non-extent `ext4` (`≥ ~2 TiB`, `fs/ext4/super.c` `ext4_max_size`),
    and `vfat` (`4 GiB - 1`). Failing closed at `newOff ≥ FS_SAFE_MAX_FILESIZE` on `lseek`
    (note `vfs_setpos` checks `offset > maxsize`, so failing closed at `≥` is sound) and
    `pos + count.toNat > FS_SAFE_MAX_FILESIZE` on `write` keeps the model sound across common
    host filesystems. -/
def FS_SAFE_MAX_FILESIZE : Nat := 0xffffffff

/-- Cooperative full-slice `read` (`__NR_read = 63`, `fs/read_write.c:709` `ksys_read`) and
    `pread64` (`__NR_pread64 = 67`, `fs/read_write.c:756` `ksys_pread64`):
    - `[INTENTIONAL_SCOPE]`: Models complete reads clamped to `MAX_RW_COUNT = 0x7ffff000`
      (`count' := min count.toNat MAX_RW_COUNT`, `fs/read_write.c:568-569` `vfs_read`) on
      `.localFile` descriptors (with `rw_verify_area` returning `-EINVAL` when
      `pos + count.toNat > MAX_LFS_FILESIZE`, matching `fs/read_write.c:458-472, 565-567`),
      sequential `.stdio` `stdin` (`fd = 0`, `useExplicitPos = false`), and `read`
      (`!useExplicitPos`) on `.localDir` descriptors (`-EISDIR`, `fs/libfs.c:223`
      `generic_read_dir`, assuming `getdents`/`getdents64` is unmodeled so directory `f_pos`
      remains `0`); fails closed with `.Exception` when `chunk` faults after a writable prefix
      (`canWrite buf 1` && `!canWrite buf chunk.length`), or on `pread64` (`useExplicitPos = true`)
      on `.localDir`, closed `fd < 3`, or other non-file FDs.
    - `[OVERPINNED_BEHAVIOR]`: Checks `posR < 0` (`-EINVAL`) before `fd` on `pread64`
      (`fs/read_write.c:756-761`), checks `accMode.canRead` (`FMODE_READ`) and `access_ok`
      (`buf.toNat + count.toNat > USER_VA_LIMIT -> -EFAULT`) before `rw_verify_area`
      (`pos + count.toNat > MAX_LFS_FILESIZE -> -EINVAL`) and the `MAX_RW_COUNT` clamp, and checks
      user buffer writability only on the `chunk.length` bytes actually copied (`mm/filemap.c`
      `copy_page_to_iter`, so `chunk.length = 0` at EOF returns `0` without faulting). -/
def execReadCommon (s : State) (useExplicitPos : Bool) : State :=
  let rawFd := s.readReg32 Reg.x0
  let buf   := s.readReg64 Reg.x1
  let count := s.readReg64 Reg.x2
  let posR  := s.readReg64 Reg.x3
  if useExplicitPos && posR.slt 0#64 then (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if rawFd.slt 0#32 then (s.writeReg64 Reg.x0 (-EBADF)).advancePC
  else
    let fd := rawFd.zeroExtend 64
    match s.fs.fds fd with
    | none =>
      if fd < 3#64 then s.setStatus (.Exception "unmodeled stdio fd")
      else (s.writeReg64 Reg.x0 (-EBADF)).advancePC
    | some desc =>
      if !useExplicitPos && desc.kind == .localDir then
        if !desc.accMode.canRead then (s.writeReg64 Reg.x0 (-EBADF)).advancePC
        else if buf.toNat + count.toNat > USER_VA_LIMIT then (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
        else if decide (desc.offset + count.toNat > MAX_LFS_FILESIZE) then
          (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
        else (s.writeReg64 Reg.x0 (-EISDIR)).advancePC
      else if !(desc.kind == .localFile || (!useExplicitPos && desc.kind == .stdio)) then
        s.setStatus (.Exception "unmodeled non-file fd")
      else if !desc.accMode.canRead then (s.writeReg64 Reg.x0 (-EBADF)).advancePC
      else if decide (buf.toNat + count.toNat > USER_VA_LIMIT) then
        (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
      else
        let pos := if useExplicitPos then posR.toNat else desc.offset
        if desc.kind == .localFile && decide (pos + count.toNat > MAX_LFS_FILESIZE) then
          (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
        else
          let count' := min count.toNat MAX_RW_COUNT
          let fileBytes := s.fs.fdBytes desc
          let chunk := (fileBytes.drop pos).take count'
          if s.mem.canWrite buf chunk.length then
            let s1 := s.setMem (s.mem.writeBytes buf chunk)
            let s2 := if useExplicitPos then s1 else s1.setFs (s1.fs.setFd fd (some { desc with offset := pos + chunk.length }))
            (s2.writeReg64 Reg.x0 (BitVec.ofNat 64 chunk.length)).advancePC
          else if !s.mem.canWrite buf 1 then
            (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
          else
            s.setStatus (.Exception "unmodeled partial-fault short read")

/-- `read(fd, buf, count)` (`__NR_read = 63`, `fs/read_write.c:709` `SYSCALL_DEFINE3(read)`). -/
def execRead (s : State) : State :=
  execReadCommon s false

/-- `write(fd, buf, count)` (`__NR_write = 64`, `fs/read_write.c:733` `SYSCALL_DEFINE3(write)`):
    stream trace output for `fd ∈ {1, 2}`; file update otherwise.
    - `[INTENTIONAL_SCOPE]`: Models complete writes clamped to `MAX_RW_COUNT = 0x7ffff000`
      (`count' := min count.toNat MAX_RW_COUNT`, `fs/read_write.c:681-682` `vfs_write`) on
      `stdout`/`stderr` (`fd ∈ {1, 2}`) and open `.localFile` descriptors (returning `-EINVAL`
      when `count > 0` and `desc.offset + count.toNat > MAX_LFS_FILESIZE`, matching
      `fs/read_write.c:458-472` `rw_verify_area` on `file->f_pos`), and returns `-EBADF` on
      `.localDir` descriptors; fails closed with `.Exception` when `buf` faults after a readable
      prefix (`allPerm (·.r) buf 1` && `!allPerm (·.r) buf count'`), when a file write exceeds
      `FS_SAFE_MAX_FILESIZE` (`0xffffffff`) or `MAX_LFS_FILESIZE`, or on closed `fd = 0` or custom FDs.
    - `[OVERPINNED_BEHAVIOR]`: Checks `fd`, `accMode.canWrite` (`FMODE_WRITE`), `access_ok`
      (`buf.toNat + count.toNat > USER_VA_LIMIT -> -EFAULT`, including `count = 0`), `count == 0`
      (`0`), and `rw_verify_area` (`desc.offset + count.toNat > MAX_LFS_FILESIZE -> -EINVAL`) on
      the unclamped `count` before clamping to `MAX_RW_COUNT` and reading `buf`, returning `-EFAULT`
      only when the first byte is not readable (`!allPerm (·.r) buf 1`, matching `mm/filemap.c`
      `generic_perform_write`). -/
def execWrite (s : State) : State :=
  let rawFd := s.readReg32 Reg.x0
  let buf   := s.readReg64 Reg.x1
  let count := s.readReg64 Reg.x2
  if rawFd.slt 0#32 then
    (s.writeReg64 Reg.x0 (-EBADF)).advancePC
  else
    let fd32 := rawFd.zeroExtend 64
    if fd32 == 1#64 || fd32 == 2#64 then
      if decide (buf.toNat + count.toNat > USER_VA_LIMIT) then
        (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
      else if count == 0#64 then
        (s.writeReg64 Reg.x0 0#64).advancePC
      else
        let count' := min count.toNat MAX_RW_COUNT
        if s.mem.canRead buf count' then
          let events := TraceEvent.ofBytes (OutputStream.ofFd fd32) (s.mem.readBytes buf count')
          ((s.appendTrace events).writeReg64 Reg.x0 (BitVec.ofNat 64 count')).advancePC
        else if !s.mem.allPerm (·.r) buf 1 then
          (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
        else if !s.mem.allPerm (·.r) buf count' then
          s.setStatus (.Exception "unmodeled partial-fault short write")
        else
          s.setStatus (.Exception "write from lazy-free memory")
    else
      match s.fs.fds fd32 with
      | none =>
        if fd32 < 3#64 then s.setStatus (.Exception "unmodeled stdio fd")
        else (s.writeReg64 Reg.x0 (-EBADF)).advancePC
      | some desc =>
        if desc.kind == .localDir then
          (s.writeReg64 Reg.x0 (-EBADF)).advancePC
        else if desc.kind != .localFile then s.setStatus (.Exception "unmodeled non-file fd")
        else if !desc.accMode.canWrite then (s.writeReg64 Reg.x0 (-EBADF)).advancePC
        else if decide (buf.toNat + count.toNat > USER_VA_LIMIT) then
          (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
        else if desc.offset + count.toNat > MAX_LFS_FILESIZE then
          (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
        else if count == 0#64 then
          (s.writeReg64 Reg.x0 0#64).advancePC
        else
          let count' := min count.toNat MAX_RW_COUNT
          let oldBytes := s.fs.fileBytes desc.path
          let pos := s.fs.writePos desc
          if pos + count' > MAX_LFS_FILESIZE then
            s.setStatus (.Exception "append write exceeds MAX_LFS_FILESIZE")
          else if decide (pos + count' > FS_SAFE_MAX_FILESIZE) then
            s.setStatus (.Exception "unmodeled file write past FS_SAFE_MAX_FILESIZE")
          else if s.mem.canRead buf count' then
            let data := s.mem.readBytes buf count'
            let newBytes := writeFileBytes oldBytes pos data
            let fs' := (s.fs.setFile desc.path (some (.file newBytes))).setFd fd32
              (some { desc with offset := pos + count' })
            let events := TraceEvent.ofBytes (OutputStream.ofFd fd32) data
            (((s.setFs fs').appendTrace events).writeReg64 Reg.x0 (BitVec.ofNat 64 count')).advancePC
          else if !s.mem.allPerm (·.r) buf 1 then
            (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
          else if !s.mem.allPerm (·.r) buf count' then
            s.setStatus (.Exception "unmodeled partial-fault short write")
          else
            s.setStatus (.Exception "write from lazy-free memory")

/-- `lseek(fd, offset, whence)` (`__NR_lseek = 62`, `fs/read_write.c:412` `SYSCALL_DEFINE3(lseek)` ->
    `ksys_lseek` -> `generic_file_llseek_size`, `include/uapi/linux/fs.h:52-57`
    `SEEK_SET = 0`, `SEEK_CUR = 1`, `SEEK_END = 2`, `SEEK_DATA = 3`, `SEEK_HOLE = 4`):
    - `[INTENTIONAL_SCOPE]`: Models `SEEK_SET`/`SEEK_CUR`/`SEEK_END` below `FS_SAFE_MAX_FILESIZE`
      (`0xffffffff`) and past-EOF `SEEK_DATA`/`SEEK_HOLE` (`offS ≥ fileLen` -> `-ENXIO`, matching
      `fs/read_write.c:122-138`, `mm/shmem.c:3606`, and `fs/ext4/file.c`) on `.localFile`
      descriptors; fails closed with `.Exception` on `newOff ≥ FS_SAFE_MAX_FILESIZE`, negative or
      in-bounds `SEEK_DATA`/`SEEK_HOLE` (`offS < fileLen`), non-seekable `.stdio` (`fd < 3`), and
      `.localDir` descriptors. -/
def execLseek (s : State) : State :=
  let rawFd  := s.readReg32 Reg.x0
  let offS   := (s.readReg64 Reg.x1).toInt
  let whence := s.readReg32 Reg.x2
  if rawFd.slt 0#32 then (s.writeReg64 Reg.x0 (-EBADF)).advancePC
  else
    let fd := rawFd.zeroExtend 64
    match s.fs.fds fd with
    | none =>
      if fd < 3#64 then s.setStatus (.Exception "unmodeled stdio fd")
      else (s.writeReg64 Reg.x0 (-EBADF)).advancePC
    | some desc =>
      if desc.kind != .localFile then s.setStatus (.Exception "unmodeled non-file fd")
      else
        let fileLen : Int := match s.fs.files desc.path with | some (.file bs) => bs.length | _ => 0
        if whence == 3#32 || whence == 4#32 then
          if decide (offS ≥ fileLen) then
            (s.writeReg64 Reg.x0 (-ENXIO)).advancePC
          else
            s.setStatus (.Exception "unmodeled SEEK_DATA/SEEK_HOLE in-bounds offset")
        else
          let baseOff? : Option Int :=
            if whence == 0#32 then some 0
            else if whence == 1#32 then some (Int.ofNat desc.offset)
            else if whence == 2#32 then some fileLen
            else none
          match baseOff? with
          | none => (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
          | some base =>
            let newOff := base + offS
            if newOff < 0 || newOff ≥ 2 ^ 63 then (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
            else if decide (newOff ≥ Int.ofNat FS_SAFE_MAX_FILESIZE) then
              s.setStatus (.Exception "unmodeled lseek offset >= FS_SAFE_MAX_FILESIZE")
            else
              let n := newOff.toNat
              let fs' := s.fs.setFd fd (some { desc with offset := n })
              ((s.setFs fs').writeReg64 Reg.x0 (BitVec.ofNat 64 n)).advancePC

/-- `pread64(fd, buf, count, pos)` (`__NR_pread64 = 67`, `fs/read_write.c:756` `SYSCALL_DEFINE4(pread64)`). -/
def execPread64 (s : State) : State :=
  execReadCommon s true

end Arm64


