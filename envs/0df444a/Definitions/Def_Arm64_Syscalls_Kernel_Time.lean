-- Prove2me | Definitions.Def_Arm64_Syscalls_Kernel_Time
-- name    : Arm64_Syscalls_Kernel_Time
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:09:59.381538+00:00
-- url     : https://prove2.me/theorems/ce1d60ef-2f5c-4b30-a54a-93f559498245
-- title:
--   Arm64.Trusted.Syscalls.Kernel.Time — Clock and Time Syscalls
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Kernel/Time.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Kernel/Time.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Kernel/Time.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Kernel/Time.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Kernel/Time.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Syscalls_Common

/-!
# Clock and Time Syscalls

Trusted model of the Linux AArch64 `clock_gettime` syscall (`kernel/time/posix-timers.c`,
`include/uapi/linux/time.h`), defining `SYS_CLOCK_GETTIME`, the 16-byte `struct timespec`
encoder `encodeTimespec`, and `execClockGettime`.
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `clock_gettime` syscall number (`__NR_clock_gettime = 113`, `include/uapi/asm-generic/unistd.h:318`, `kernel/time/posix-timers.c:1150`). -/
def SYS_CLOCK_GETTIME : BitVec 64 := 113#64

/-- 16-byte little-endian Linux AArch64 `struct timespec` (`tv_sec` at `+0`, `tv_nsec` at `+8`,
    matching `put_timespec64` in `kernel/time/time.c:89`). -/
def encodeTimespec (ts : Timespec) : List (BitVec 8) :=
  leBytes64 ts.sec ++ leBytes64 (BitVec.ofNat 64 ts.nsec.val)

/-- `clock_gettime(clk_id, tp)` (`__NR_clock_gettime = 113`, `kernel/time/posix-timers.c:1150`):
    models `SYSCALL_DEFINE2(clock_gettime, ...)` and the AArch64 vDSO `__kernel_clock_gettime`
    (`lib/vdso/gettimeofday.c`) for static POSIX clocks `0..7`
    (`CLOCK_REALTIME = 0`, `CLOCK_MONOTONIC = 1`, `CLOCK_PROCESS_CPUTIME_ID = 2`,
    `CLOCK_THREAD_CPUTIME_ID = 3`, `CLOCK_MONOTONIC_RAW = 4`, `CLOCK_REALTIME_COARSE = 5`,
    `CLOCK_MONOTONIC_COARSE = 6`, `CLOCK_BOOTTIME = 7`):
    - `[INTENTIONAL_SCOPE]`: if `clk.toNat > 7`, fails closed with
      `.Exception "unmodeled clock_gettime clockid"` without consuming an oracle entry;
    - if `!s.mem.canWrite tp 16`, returns `EFAULT_RET` (`-EFAULT`, matching `put_timespec64`
      `copy_to_user` in `kernel/time/time.c`; on loaded process states `[USER_VA_LIMIT, 2 ^ 64)` is
      unmapped, so `!s.mem.canWrite tp 16` also rejects `access_ok` overflows) without consuming an
      oracle entry;
    - `[INTENTIONAL_OVERAPPROX]`: queries `ts := s.oracle.clockGettime s.oracleIdx`, writes the
      16-byte little-endian `struct timespec` (`encodeTimespec ts`), consumes one oracle entry via
      `s.nextOracle`, and returns `0`. No monotonicity is assumed across successive calls. -/
def execClockGettime (s : State) : State :=
  let clk := s.readReg32 Reg.x0
  let tp  := s.readReg64 Reg.x1
  if clk.toNat > 7 then
    s.setStatus (.Exception "unmodeled clock_gettime clockid")
  else if !s.mem.canWrite tp 16 then
    (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
  else
    let ts := s.oracle.clockGettime s.oracleIdx
    (((s.setMem (s.mem.writeBytes tp (encodeTimespec ts))).nextOracle).writeReg64 Reg.x0 0#64).advancePC

end Arm64


