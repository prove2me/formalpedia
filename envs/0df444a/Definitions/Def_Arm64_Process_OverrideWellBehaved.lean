-- Prove2me | Definitions.Def_Arm64_Process_OverrideWellBehaved
-- name    : Arm64_Process_OverrideWellBehaved
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:19:13.752493+00:00
-- url     : https://prove2.me/theorems/04c1c255-e320-4c78-811f-5e735610d10e
-- title:
--   Arm64.Trusted.Process.OverrideWellBehaved — Well-Behaved Function Overrides
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Process/OverrideWellBehaved.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process/OverrideWellBehaved.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Process/OverrideWellBehaved.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process/OverrideWellBehaved.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Process/OverrideWellBehaved.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Spec_Hoare

/-!
# Well-Behaved Function Overrides

`Override.WellBehaved pre fp f` specifies that a `State → State` function override `f` (see
`ElfRunsToWithOverrides`) behaves like a returning AAPCS64 leaf function that makes no system
calls. The process semantics do not assume it; callers supply `WellBehaved` proofs as review
evidence for override tables on whole-binary theorems.
-/

@[expose] public section

namespace Arm64.Override

/-- From every running state `s` with `pre s`, the override `f` behaves like a returning AAPCS64
    function without system calls:
    - `f s` updates only general-purpose and SIMD registers, condition flags (`pstate`), `fpsr`,
      memory, and sets `pc` to the entry link register `x30` (the caller's return address). Every
      other field (`sp`, `tpidrEl0`, `status = .Running`, `brk`, `fs`, `oracle`, `oracleIdx`,
      `exclFails`, `trace`, `symtab`, `sigActions`, etc.) is unchanged, including fields added to
      `State` later;
    - callee-saved registers are preserved (`CallingConventionPreserved`: `sp`, `x19..x28`, `x29`,
      `d8..d15`), while `x0..x18`, `x30`, flags, and other SIMD bits may be modified;
    - memory permissions are unchanged at every address (no mapping or `mprotect`), VMA anonymity
      is unchanged (`(f s).mem.isAnon = s.mem.isAnon`), and no new `lazyFree` markers are
      introduced (`s.mem.isLazyFree a = false → (f s).mem.isLazyFree a = false`);
    - every byte whose contents or `lazyFree` state changes lies in `fp s` and satisfies `canWrite`
      in `s`.
    Nothing is claimed outside `pre` (`WellBehaved (fun _ => False) fp f` holds for every `f`), so
    review `pre` and `fp`; the hook contract derived by `WellBehaved.hookOk` requires its
    precondition to imply `pre` and to own `fp`. -/
def WellBehaved (pre : State → Prop) (fp : State → BitVec 64 → Prop) (f : State → State) :
    Prop :=
  ∀ s, s.status = .Running → pre s →
    (∃ regs vregs pstate fpsr mem,
      f s = { s with regs, vregs, pstate, fpsr, mem, pc := s.readReg64 .lr }) ∧
    CallingConventionPreserved s (f s) ∧
    (f s).mem.perm = s.mem.perm ∧
    (f s).mem.isAnon = s.mem.isAnon ∧
    (∀ a, s.mem.isLazyFree a = false → (f s).mem.isLazyFree a = false) ∧
    ∀ a, ((f s).mem.read8 a ≠ s.mem.read8 a ∨ (f s).mem.isLazyFree a ≠ s.mem.isLazyFree a) →
      fp s a ∧ s.mem.canWrite a 1 = true

end Arm64.Override


