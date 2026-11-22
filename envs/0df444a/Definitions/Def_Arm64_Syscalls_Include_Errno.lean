-- Prove2me | Definitions.Def_Arm64_Syscalls_Include_Errno
-- name    : Arm64_Syscalls_Include_Errno
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:04:23.011589+00:00
-- url     : https://prove2.me/theorems/2ef1f2c3-0438-439b-b9c2-7e12a4ea5e7b
-- title:
--   Arm64.Trusted.Syscalls.Include.Errno — Linux UAPI Error Numbers
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Include/Errno.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Include/Errno.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Include/Errno.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Include/Errno.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Include/Errno.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_ISA_State

/-!
# Linux UAPI Error Numbers

Linux AArch64 errno constants from `include/uapi/asm-generic/errno-base.h` (`EPERM = 1` ..
`ENOTTY = 25`, `EFAULT_RET = -14`) and `include/uapi/asm-generic/errno.h` (`ENAMETOOLONG = 36`).
-/

@[expose] public section

namespace Arm64

/-- Linux `EPERM` (`1`, `include/uapi/asm-generic/errno-base.h`). -/
def EPERM        : BitVec 64 := 1#64
def ENOENT       : BitVec 64 := 2#64
def ESRCH        : BitVec 64 := 3#64
def ENXIO        : BitVec 64 := 6#64
def EBADF        : BitVec 64 := 9#64
def ENOMEM       : BitVec 64 := 12#64
def EEXIST       : BitVec 64 := 17#64
def ENOTDIR      : BitVec 64 := 20#64
def EISDIR       : BitVec 64 := 21#64
def EINVAL       : BitVec 64 := 22#64
def EMFILE       : BitVec 64 := 24#64
def ENOTTY       : BitVec 64 := 25#64
def ENAMETOOLONG : BitVec 64 := 36#64

/-- Linux `-EFAULT` error return (`-14`, `include/uapi/asm-generic/errno-base.h:18`). -/
def EFAULT_RET : BitVec 64 := -14#64

end Arm64


