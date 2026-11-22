-- Prove2me | Definitions.Def_Arm64_Syscalls_Kernel_Exit
-- name    : Arm64_Syscalls_Kernel_Exit
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:06:00.662682+00:00
-- url     : https://prove2.me/theorems/f964f587-a97b-4a0d-acf3-b3d949eaa309
-- title:
--   Arm64.Trusted.Syscalls.Kernel.Exit — Linux Process Termination exit & exit_group Syscalls
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Kernel/Exit.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Kernel/Exit.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Kernel/Exit.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Kernel/Exit.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Kernel/Exit.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Syscalls_Common

/-!
# Linux Process Termination `exit` & `exit_group` Syscalls (`Arm64.Trusted.Syscalls.Kernel.Exit`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Linux `7.3` Upstream Sources**:
  - `kernel/exit.c:1094` (`SYSCALL_DEFINE1(exit, int, error_code)` -> `do_exit`)
  - `kernel/exit.c:1138` (`SYSCALL_DEFINE1(exit_group, int, error_code)` -> `do_group_exit`)
- **Purpose & Key Exports**: `SYS_EXIT` (`93`), `SYS_EXIT_GROUP` (`94`), and `execExit`.
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `exit` syscall number (`__NR_exit = 93`, `include/uapi/asm-generic/unistd.h:258`, `kernel/exit.c:1094`). -/
def SYS_EXIT : BitVec 64 := 93#64

/-- Linux AArch64 `exit_group` syscall number (`__NR_exit_group = 94`, `include/uapi/asm-generic/unistd.h:260`, `kernel/exit.c:1138`). -/
def SYS_EXIT_GROUP : BitVec 64 := 94#64

/-- `exit(status)` (`__NR_exit = 93`, `kernel/exit.c:1094`) and `exit_group(status)`
    (`__NR_exit_group = 94`, `kernel/exit.c:1138`).
    - `[INTENTIONAL_SCOPE]`: In the single-threaded process model, `exit` and `exit_group` have
      identical process-termination semantics (`execExit` stores the full 64-bit `X0` in `.Exited`,
      and `ProcessOutcome.ofState` preserves `code` unmasked rather than masking with `0xff`, so
      `X0 = 256` gives `exitCode = 256` where Linux reports status `0`; specifications constrain
      the full 64-bit `exitCode`). -/
def execExit (s : State) : State :=
  s.setStatus (.Exited (s.readReg64 Reg.x0))

end Arm64


