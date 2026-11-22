-- Prove2me | Definitions.Def_Arm64_Syscalls_Misc
-- name    : Arm64_Syscalls_Misc
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:10:49.278708+00:00
-- url     : https://prove2.me/theorems/57a65fbd-bdd7-436d-b413-39b749e093d7
-- title:
--   Arm64.Trusted.Syscalls.Misc — Thread Identity, Futex Wake, and Affinity Syscalls
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Misc.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Misc.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Misc.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Misc.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Misc.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Syscalls_Common
public import Definitions.Def_Arm64_Syscalls_Kernel_Sys

/-!
# Thread Identity, Futex Wake, and Affinity Syscalls

Trusted syscall dispatch bundle (`Syscall.miscTable`, `Syscall.misc`) re-exporting `Kernel.Sys` for
single-thread `set_tid_address`, `futex` (`FUTEX_WAKE` / `FUTEX_WAKE_PRIVATE`),
`sched_getaffinity`, `getpid`, and `gettid`.
-/

@[expose] public section

namespace Arm64

namespace Syscall

/-- Dispatch table for single-thread identity, futex-wake, and CPU-affinity syscalls
    (`set_tid_address`, `futex`, `sched_getaffinity`, `getpid`, `gettid`). -/
def miscTable : List (BitVec 64 × (State → State)) :=
  [(SYS_SET_TID_ADDRESS, execSetTidAddress),
   (SYS_FUTEX, execFutex),
   (SYS_SCHED_GETAFFINITY, execSchedGetaffinity),
   (SYS_GETPID, execGetpid),
   (SYS_GETTID, execGetpid)]

/-- Syscall dispatcher for `miscTable`. -/
def misc : State → State := dispatch miscTable

end Syscall

end Arm64


