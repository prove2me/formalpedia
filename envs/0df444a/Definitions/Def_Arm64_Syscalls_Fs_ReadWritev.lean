-- Prove2me | Definitions.Def_Arm64_Syscalls_Fs_ReadWritev
-- name    : Arm64_Syscalls_Fs_ReadWritev
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:05:46.758257+00:00
-- url     : https://prove2.me/theorems/0a0248f3-64ec-4441-b0c9-e160ff7023ac
-- title:
--   Arm64.Trusted.Syscalls.Fs.ReadWritev — Linux Vectored Read and Write Syscalls
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Fs/ReadWritev.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Fs/ReadWritev.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Fs/ReadWritev.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Fs/ReadWritev.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Fs/ReadWritev.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Syscalls_Fs_ReadWrite

/-!
# Linux Vectored Read and Write Syscalls

Models AArch64 Linux `readv` (`__NR_readv = 65`) and `writev` (`__NR_writev = 66`), following
`fs/read_write.c` (`do_readv`, `do_writev`, `vfs_readv`, `vfs_writev`, `do_loop_readv_writev`)
and `lib/iov_iter.c` (`import_iovec`, `copy_iovec_from_user`). Vectored transfers execute
`execRead` or `execWrite` sequentially across the validated `struct iovec` segments.
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `readv` syscall number (`__NR_readv = 65`, `include/uapi/asm-generic/unistd.h:176`, `fs/read_write.c:1163`). -/
def SYS_READV : BitVec 64 := 65#64

/-- Linux AArch64 `writev` syscall number (`__NR_writev = 66`, `include/uapi/asm-generic/unistd.h:178`, `fs/read_write.c:1169`). -/
def SYS_WRITEV : BitVec 64 := 66#64

/-- Maximum number of `struct iovec` segments per call (`UIO_MAXIOV = 1024`,
    `include/uapi/linux/uio.h:46`). -/
def UIO_MAXIOV : Nat := 1024

/-- Copy `n` 16-byte `struct iovec { void *iov_base; size_t iov_len; }` entries
    (`include/uapi/linux/uio.h:17-21`) starting at user address `vec`, in order, as `(base, len)`
    pairs (`lib/iov_iter.c` `copy_iovec_from_user`). On failure returns the final state `s`
    with `X0` set and `PC` advanced:
    - `-EFAULT` if an entry is not readable (`unsafe_get_user` fault);
    - `.Exception` if an entry is readable but lazily freed (see `Memory.canRead`);
    - `-EINVAL` if `iov_len` has its sign bit set (`(ssize_t)len < 0`).
    Entries are checked one at a time, so an earlier bad length wins over a later fault. -/
def readIovecs (s : State) (vec : BitVec 64) : Nat → Except State (List (BitVec 64 × BitVec 64))
  | 0 => .ok []
  | n + 1 =>
    if !s.mem.allPerm (·.r) vec 16 then .error (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
    else if !s.mem.canRead vec 16 then .error (s.setStatus (.Exception "iovec read from lazy-free memory"))
    else
      let base := s.mem.read64 vec
      let len := s.mem.read64 (vec + 8#64)
      if len.slt 0#64 then .error (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
      else (readIovecs s (vec + 16#64) n).map ((base, len) :: ·)

/-- Transfer segments in order with `step` (`execRead` or `execWrite`), matching
    `fs/read_write.c:837-865` `do_loop_readv_writev`: each segment is one `step` call on a state
    whose `X1`/`X2` hold the segment's `(base, len)` and whose registers and `PC` are otherwise
    those of the syscall entry state `s0`. The loop stops after a short transfer (`r < len`,
    returning `acc + r`) or a negative result `r` in the first segment (returning `r`). A `step`
    that leaves `.Running` ends the syscall in that state. On return, the registers are those of
    `s0` except `X0 := result`, and `PC` is advanced past the `svc`.
    - `[INTENTIONAL_SCOPE]`: A negative result after earlier segments transferred `acc > 0`
      bytes fails closed with `.Exception` (Linux `read_iter`/`write_iter` may return `acc`
      plus a partial count of the failing segment). -/
def execIovLoop (step : State → State) (s0 : State) :
    State → Nat → List (BitVec 64 × BitVec 64) → State
  | s, acc, [] => ({ s with regs := s0.regs, pc := s0.pc }.writeReg64 Reg.x0 (BitVec.ofNat 64 acc)).advancePC
  | s, acc, (base, len) :: rest =>
    let s' := step (({ s with regs := s0.regs, pc := s0.pc }.writeReg64 Reg.x1 base).writeReg64 Reg.x2 len)
    match s'.status with
    | .Running =>
      let r := s'.readReg64 Reg.x0
      if r.slt 0#64 then
        if acc = 0 then ({ s' with regs := s0.regs, pc := s0.pc }.writeReg64 Reg.x0 r).advancePC
        else s'.setStatus (.Exception "vectored transfer failed after partial progress")
      else if r.toNat < len.toNat then
        ({ s' with regs := s0.regs, pc := s0.pc }.writeReg64 Reg.x0
          (BitVec.ofNat 64 (acc + r.toNat))).advancePC
      else execIovLoop step s0 s' (acc + r.toNat) rest
    | _ => s'

/-- Shared `readv(fd, vec, vlen)` (`isRead = true`, `step = execRead`) and
    `writev(fd, vec, vlen)` (`isRead = false`, `step = execWrite`) semantics
    (`fs/read_write.c:991` `vfs_readv`, `fs/read_write.c:1029` `vfs_writev`). Checks, in Linux
    order:
    1. Descriptor (`fdget_pos` `-EBADF`, `FMODE_READ`/`FMODE_WRITE` `-EBADF`): runs `step`
       with `X1 = X2 = 0` as a zero-length probe and keeps only its verdict; a non-`.Running`
       status fails closed with that status, and a negative `X0` is returned except `-EISDIR` from
       a readable directory (`generic_read_dir` runs only in the transfer loop below).
    2. Segment count: `vlen` is truncated to `unsigned int` (`import_iovec`'s `nr_segs`);
       `nr_segs > UIO_MAXIOV` returns `-EINVAL`; `nr_segs = 0` returns `0`.
    3. iovec array: `vec + 16 * nr_segs > USER_VA_LIMIT` returns `-EFAULT`
       (`user_access_begin` `access_ok`), then entries are copied by `readIovecs`.
    4. Segment buffers: any `base + len > USER_VA_LIMIT` returns `-EFAULT` (`access_ok`).
    5. Zero total: returns `0` without a transfer (`if (!tot_len) goto out`).
    6. File position: on a `.localFile`, `offset + total > MAX_LFS_FILESIZE` returns
       `-EINVAL` (`rw_verify_area`: `(loff_t)(pos + count) < 0`).
    7. Transfer: `execIovLoop`.
    - `[INTENTIONAL_SCOPE]`: Fails closed with `.Exception` when the total length exceeds
      `MAX_RW_COUNT` (Linux silently truncates the iovecs to `MAX_RW_COUNT` bytes), and on any
      descriptor `step` itself does not model. -/
def execRwvCommon (step : State → State) (isRead : Bool) (s : State) : State :=
  let vec := s.readReg64 Reg.x1
  let nrSegs := (s.readReg32 Reg.x2).toNat
  let probe := step ((s.writeReg64 Reg.x1 0#64).writeReg64 Reg.x2 0#64)
  match probe.status with
  | .Running =>
    let pr := probe.readReg64 Reg.x0
    if pr.slt 0#64 && !(isRead && pr == -EISDIR) then (s.writeReg64 Reg.x0 pr).advancePC
    else if nrSegs > UIO_MAXIOV then (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
    else if nrSegs = 0 then (s.writeReg64 Reg.x0 0#64).advancePC
    else if vec.toNat + 16 * nrSegs > USER_VA_LIMIT then (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
    else
      match readIovecs s vec nrSegs with
      | .error s' => s'
      | .ok segs =>
        let total := (segs.map fun p => p.2.toNat).sum
        if total > MAX_RW_COUNT then s.setStatus (.Exception "iovec total exceeds MAX_RW_COUNT")
        else if segs.any (fun p => p.1.toNat + p.2.toNat > USER_VA_LIMIT) then
          (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
        else if total = 0 then (s.writeReg64 Reg.x0 0#64).advancePC
        else
          let posOverflow : Bool := match s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) with
            | some desc => desc.kind == .localFile && decide (desc.offset + total > MAX_LFS_FILESIZE)
            | none => false
          if posOverflow then (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
          else execIovLoop step s s 0 segs
  | _ => s.setStatus probe.status

/-- `readv(fd, vec, vlen)` (`__NR_readv = 65`, `fs/read_write.c:1163` `SYSCALL_DEFINE3(readv)`):
    `execRwvCommon` over `execRead`. -/
def execReadv (s : State) : State :=
  execRwvCommon execRead true s

/-- `writev(fd, vec, vlen)` (`__NR_writev = 66`, `fs/read_write.c:1169` `SYSCALL_DEFINE3(writev)`):
    `execRwvCommon` over `execWrite`. -/
def execWritev (s : State) : State :=
  execRwvCommon execWrite false s

end Arm64


