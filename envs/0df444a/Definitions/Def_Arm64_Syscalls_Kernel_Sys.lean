-- Prove2me | Definitions.Def_Arm64_Syscalls_Kernel_Sys
-- name    : Arm64_Syscalls_Kernel_Sys
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:10:38.148596+00:00
-- url     : https://prove2.me/theorems/7d7ad05f-c255-40ef-82c4-7e7324ba80f4
-- title:
--   Arm64.Trusted.Syscalls.Kernel.Sys — Thread Identity, Futex Wake, and Affinity Syscalls
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Kernel/Sys.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Kernel/Sys.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Kernel/Sys.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Kernel/Sys.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Kernel/Sys.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Syscalls_Common

/-!
# Thread Identity, Futex Wake, and Affinity Syscalls

Linux AArch64 syscall numbers and transition functions for `set_tid_address` (`96`),
`futex` (`98`, `FUTEX_WAKE` / `FUTEX_WAKE_PRIVATE`), `sched_getaffinity` (`123`), `getpid`
(`172`), and `gettid` (`178`), modeled after Linux `kernel/fork.c`, `kernel/futex/`,
`kernel/sched/syscalls.c`, and `kernel/sys.c` in a single-process, single-thread, single-CPU
environment.
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `set_tid_address` syscall number (`__NR_set_tid_address = 96`, `include/uapi/asm-generic/unistd.h:278`, `kernel/fork.c:1866`). -/
def SYS_SET_TID_ADDRESS : BitVec 64 := 96#64

/-- Linux AArch64 `futex` syscall number (`__NR_futex = 98`, `include/uapi/asm-generic/unistd.h:270`, `kernel/futex/syscalls.c:191`). -/
def SYS_FUTEX : BitVec 64 := 98#64

/-- `futex` command `FUTEX_WAKE` (`1`, `include/uapi/linux/futex.h:12`). -/
def FUTEX_WAKE : BitVec 32 := 1#32

/-- `futex` private-process flag `FUTEX_PRIVATE_FLAG` (`128`, `include/uapi/linux/futex.h:26`). -/
def FUTEX_PRIVATE_FLAG : BitVec 32 := 128#32

/-- `futex` private wake operation `FUTEX_WAKE_PRIVATE` (`FUTEX_WAKE | FUTEX_PRIVATE_FLAG = 129`, `include/uapi/linux/futex.h:59`). -/
def FUTEX_WAKE_PRIVATE : BitVec 32 := 129#32

/-- Linux AArch64 `sched_getaffinity` syscall number (`__NR_sched_getaffinity = 123`, `include/uapi/asm-generic/unistd.h:344`, `kernel/sched/syscalls.c:1395`). -/
def SYS_SCHED_GETAFFINITY : BitVec 64 := 123#64

/-- Linux AArch64 `getpid` syscall number (`__NR_getpid = 172`, `include/uapi/asm-generic/unistd.h:472`, `kernel/sys.c:966`). -/
def SYS_GETPID : BitVec 64 := 172#64

/-- Linux AArch64 `gettid` syscall number (`__NR_gettid = 178`, `include/uapi/asm-generic/unistd.h:487`, `kernel/sys.c:979`). -/
def SYS_GETTID : BitVec 64 := 178#64

/-- 8-byte kernel `cpumask_t` (`CPU 0` online) written by `sched_getaffinity` under `.singleCpu0`. -/
def SCHED_AFFINITY_MASK : List (BitVec 8) :=
  [1#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]

/-- Serialize `numWords` 64-bit little-endian `cpumask_t` words masked to `[0, nrCpuIds)` bits,
    ensuring at least CPU 0 is active when `words` masks to all-zero (`cpumask_and(&p->cpus_mask,
    cpu_active_mask)` on a running thread always contains at least one active CPU). -/
def encodeSchedAffinityMask (nrCpuIds : Nat) (words : List (BitVec 64)) (numWords : Nat) :
    List (BitVec 8) :=
  let masked := (List.range numWords).map fun i =>
    let rem := nrCpuIds - i * 64
    let mask64 : BitVec 64 :=
      if rem == 0 then 0#64
      else if rem ≥ 64 then BitVec.allOnes 64
      else (1#64 <<< rem) - 1#64
    (words.getD i 0#64) &&& mask64
  let nonEmpty :=
    if masked.all (· == 0#64) then
      match masked with
      | [] => []
      | w0 :: ws => (w0 ||| 1#64) :: ws
    else
      masked
  nonEmpty.flatMap leBytes64

/-- `set_tid_address(tidptr)` (`__NR_set_tid_address = 96`, `kernel/fork.c:1866`): per Linux
    `kernel/fork.c`, records `clear_child_tid` (`[INTENTIONAL_SCOPE]`: no-op in single-threaded
    execution without `CLONE_CHILD_CLEARTID`) without dereferencing `tidptr`, and always succeeds
    returning the caller's thread ID (`SIM_TID = 1`). -/
def execSetTidAddress (s : State) : State :=
  (s.writeReg64 Reg.x0 SIM_TID).advancePC

/-- `getpid()` (`__NR_getpid = 172`, `kernel/sys.c:966`) and `gettid()` (`__NR_gettid = 178`,
    `kernel/sys.c:979`): return the calling process/thread ID (`SIM_TID = 1`) in the
    single-process, single-thread model (`[INTENTIONAL_SCOPE]`). -/
def execGetpid (s : State) : State :=
  (s.writeReg64 Reg.x0 SIM_TID).advancePC

/-- `sched_getaffinity(pid, cpusetsize, mask)` (`__NR_sched_getaffinity = 123`,
    `kernel/sched/syscalls.c:1278,1307` `SYSCALL_DEFINE3(sched_getaffinity, pid_t, pid,
    unsigned int, len, unsigned long __user *, user_mask_ptr)` -> `sched_getaffinity`
    -> `find_process_by_pid` at `kernel/sched/syscalls.c:215`):
    - validates `len` (`W1`, 32-bit `unsigned int`) using exact 32-bit unsigned C arithmetic
      `(len * BITS_PER_BYTE) < nr_cpu_ids` (`(len * 8#32)` wraps modulo `2 ^ 32` when `len` has
      bits in `[31:29]`, e.g. `0x20000000` or `0x80000000`) and `(len & 7) != 0` -> `-EINVAL`
      (`kernel/sched/syscalls.c:1313-1316`);
    - `[INTENTIONAL_OVERAPPROX]`: queries `s.oracle.schedGetaffinity s.oracleIdx` (`SchedAffinityResult`,
      defaulting to `.singleCpu0`) to over-approximate host `nr_cpu_ids` (`1..8192`), active
      `cpumask_t` bits, `zalloc_cpumask_var` `-ENOMEM`, and LSM `security_task_getscheduler` `-EPERM`;
    - if `(pid : Int32) < 0` (`pid.slt 0#32`), returns `-ESRCH` (`find_process_by_pid(pid)`
      returns `NULL` in `kernel/sched/syscalls.c:1284-1286`);
    - `[INTENTIONAL_SCOPE]`: if `pid != 0` (calling thread) and `pid != 1` (`SIM_TID`), fails closed
      with `.Exception "unmodeled sched_getaffinity pid"`;
    - writes `retlen = min(len, cpumask_size())` bytes to `mask` (returning `-EFAULT` when
      `mask + retlen > USER_VA_LIMIT` or `mask` is unwritable at byte `0`, and failing closed with
      `.Exception` on partial-fault `copy_to_user`) and returns `retlen`. -/
def execSchedGetaffinity (s : State) : State :=
  let pid   := s.readReg32 Reg.x0
  let len32 := s.readReg32 Reg.x1
  let mask  := s.readReg64 Reg.x2
  if (len32 * 8#32) == 0#32 || (len32 &&& 7#32) != 0#32 then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else
    let q := s.oracle.schedGetaffinity s.oracleIdx
    let nrCpuIds : Nat :=
      match q with
      | .hostMask n _ => max 1 (min 8192 n)
      | _ => 1
    let cpumaskSize := ((nrCpuIds + 63) / 64) * 8
    let retlen := min len32.toNat cpumaskSize
    let outBytes : List (BitVec 8) :=
      match q with
      | .hostMask _ ws => encodeSchedAffinityMask nrCpuIds ws (retlen / 8)
      | _ => SCHED_AFFINITY_MASK
    if (len32 * 8#32).toNat < nrCpuIds then
      ((s.nextOracle).writeReg64 Reg.x0 (-EINVAL)).advancePC
    else if q == .refuseEnomem then
      ((s.nextOracle).writeReg64 Reg.x0 (-ENOMEM)).advancePC
    else if pid.slt 0#32 then
      ((s.nextOracle).writeReg64 Reg.x0 (-ESRCH)).advancePC
    else if pid != 0#32 && pid != 1#32 then
      s.setStatus (.Exception "unmodeled sched_getaffinity pid")
    else if q == .refuseEperm then
      ((s.nextOracle).writeReg64 Reg.x0 (-EPERM)).advancePC
    else if !decide (mask.toNat + retlen ≤ USER_VA_LIMIT) || !s.mem.canWrite mask retlen then
      if !decide (mask.toNat + retlen ≤ USER_VA_LIMIT) || !s.mem.canWrite mask 1 then
        ((s.nextOracle).writeReg64 Reg.x0 EFAULT_RET).advancePC
      else
        s.setStatus (.Exception "unmodeled sched_getaffinity partial-fault copy_to_user")
    else
      (((s.setMem (s.mem.writeBytes mask outBytes)).nextOracle).writeReg64
        Reg.x0 (BitVec.ofNat 64 retlen)).advancePC

/-- `futex(uaddr, futex_op, val, ...)` (`__NR_futex = 98`, `SYSCALL_DEFINE6(futex)` -> `do_futex`
    in `kernel/futex/syscalls.c:108,191` -> `futex_wake` in `kernel/futex/waitwake.c:178` ->
    `get_futex_key` in `kernel/futex/core.c:514`), modeled for `FUTEX_WAKE` (`1`) and
    `FUTEX_WAKE_PRIVATE` (`129`) in a single-process, single-thread environment:
    - `[INTENTIONAL_SCOPE]`: `op` (`W1`, 32-bit `int futex_op`) outside `FUTEX_WAKE` (`1`) and
      `FUTEX_WAKE_PRIVATE` (`129`)—i.e. `(op &&& 0xffffff7f#32) != FUTEX_WAKE`, including
      `FUTEX_WAIT`, `FUTEX_CLOCK_REALTIME` (`-ENOSYS`), and `FUTEX_ROBUST_UNLOCK`—fails closed
      with `.Exception "unmodeled futex op"`;
    - for `FUTEX_WAKE` and `FUTEX_WAKE_PRIVATE`, `futex_cmd_has_timeout` is `false` (`X3` ignored),
      `futex_robust_unlock` is a no-op (`X4` ignored), `X5` is ignored, and `FLAGS_STRICT` is unset
      so `nr_wake` (`W2`) is not constrained when zero waiters exist (`waitwake.c:186,202`);
    - if `uaddr` (`X0`) is not 4-byte-aligned (`uaddr.toNat % 4 != 0`), returns `-EINVAL`
      (`kernel/futex/core.c:535`, checked before `access_ok`);
    - if `uaddr.toNat + 4 > USER_VA_LIMIT`, returns `EFAULT_RET` (`-EFAULT`, `access_ok` in
      `kernel/futex/core.c:539`, `include/asm-generic/access_ok.h:39`);
    - for `FUTEX_WAKE_PRIVATE` (`(op &&& FUTEX_PRIVATE_FLAG) != 0`), `get_futex_key` keys on
      `(current->mm, address)` without faulting pages (`kernel/futex/core.c:583-597`) and
      `futex_wake` returns `0` (`0` threads woken in single-threaded execution);
    - for shared `FUTEX_WAKE` (`op == 1`), `get_futex_key` probes `get_user_pages_fast`
      (`kernel/futex/core.c:604-696`): returns `0` when `s.mem.canWrite uaddr 4`, returns
      `EFAULT_RET` (`-EFAULT`) when `[uaddr, uaddr + 4)` is unmapped or `PROT_NONE`
      (`!s.mem.allPerm (·.r) uaddr 4`), and `[INTENTIONAL_SCOPE]` fails closed with
      `.Exception "unmodeled shared futex on non-writable memory"` on read-only mappings (where
      Linux distinguishes anonymous `ZERO_PAGE` `-EFAULT` from file-backed `0`). -/
def execFutex (s : State) : State :=
  let uaddr := s.readReg64 Reg.x0
  let op    := s.readReg32 Reg.x1
  if (op &&& 0xffffff7f#32) != FUTEX_WAKE then
    s.setStatus (.Exception "unmodeled futex op")
  else if uaddr.toNat % 4 != 0 then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if !decide (uaddr.toNat + 4 ≤ USER_VA_LIMIT) then
    (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
  else if (op &&& FUTEX_PRIVATE_FLAG) != 0#32 || s.mem.canWrite uaddr 4 then
    (s.writeReg64 Reg.x0 0#64).advancePC
  else if !s.mem.allPerm (·.r) uaddr 4 then
    (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
  else
    s.setStatus (.Exception "unmodeled shared futex on non-writable memory")

end Arm64


