-- Prove2me | Definitions.Def_Arm64_Spec_Placed
-- name    : Arm64_Spec_Placed
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:15:45.29364+00:00
-- url     : https://prove2.me/theorems/d4a2a60e-04d6-416d-b3c0-4f6cb26f8079
-- title:
--   Arm64.Trusted.Spec.Placed — Layout-Generic Library Contracts
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Spec/Placed.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Spec/Placed.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Spec/Placed.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Spec/Placed.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Spec/Placed.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Object_Placed
public import Definitions.Def_Arm64_Spec_SepLogic
public import Definitions.Def_Arm64_Spec_Hoare

/-!
# Layout-Generic Library Contracts

Initial data assertions (`PlacedLib.dataInit`, `MultiPlacedLib.dataInit`) and layout-generic
subroutine contracts (`PlacedLib.subroutineOk`, `MultiPlacedLib.subroutineOk`) quantifying over
every valid linker placement (`Placeable`). See `Arm64/Trusted/Object/Placed.lean` for the
placement model and `Arm64/Trusted/Process/Placed.lean` for ELF containment checks.
-/

@[expose] public section

namespace Arm64.Obj

/-- Separating conjunction of a list of assertions (`emp` for `[]`). -/
def sepAll : List SepProp → SepProp
  | [] => emp
  | [p] => p
  | p :: ps => p ∗ sepAll ps

/-- The library's data objects in their initial (relocated) state under `pl`: each read-only
    object `d` as read-only bytes `pl.ρ d.sym ↦ᵣ lib.patchedData pl d`, each writable one as
    owned bytes `pl.ρ d.sym ↦ₛ lib.patchedData pl d`, all disjoint. -/
def PlacedLib.dataInit (lib : PlacedLib) (pl : Placement) : SepProp :=
  sepAll (lib.data.map fun d =>
    if d.readOnly then pointsToBytesRO (pl.ρ d.sym) (lib.patchedData pl d)
    else pointsToBytes (pl.ρ d.sym) (lib.patchedData pl d))

/-- Layout-generic correctness of the library's exported function `fnName`: `fnName` is one of
    `lib.exports` (whose `.symtab` entries `PlacedLib.InElf` checks), and for every placement `pl`
    under which the library is `Placeable`, `subroutine_ok` holds for the placed program
    (`lib.program pl externs overrides`) at the function's address, with the spec instantiated at
    `pl` and its base-dependent part at `pl.base`.

    Non-default `externs` / `overrides` replace real code by hooks: `PlacedLib.InElf` does not
    check them, so a whole-binary composition must show that the binary's code at each hooked
    address refines its hook (or use hook-free statements). -/
abbrev PlacedLib.subroutineOk {S α : Type} [ToBaseSpec S α] (lib : PlacedLib) (fnName : String)
    (spec : Placement → S)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none) : Prop :=
  fnName ∈ lib.exports ∧ ∀ pl : Placement, lib.Placeable pl →
    subroutine_ok (lib.program pl externs overrides) (lib.fnAddr pl fnName)
      (ToBaseSpec.toSpec (spec pl) pl.base)

/-- The multi-block library's data objects in their initial (relocated) state under `mpl`: each
    read-only object `d` as read-only bytes `mpl.ρ d.sym ↦ᵣ lib.patchedData mpl d`, each writable
    one as owned bytes `mpl.ρ d.sym ↦ₛ lib.patchedData mpl d`, all disjoint. -/
def MultiPlacedLib.dataInit (lib : MultiPlacedLib) (mpl : MultiPlacement) : SepProp :=
  sepAll (lib.data.map fun d =>
    if d.readOnly then pointsToBytesRO (mpl.ρ d.sym) (lib.patchedData mpl d)
    else pointsToBytes (mpl.ρ d.sym) (lib.patchedData mpl d))

/-- Adjoin `⌜lib.CodeLoaded mpl s0.mem⌝` to `spec.pre`, giving the proof of a block access to
    `Program.CodeLoaded` for every block of `lib` (for cross-block `SepWP.call_subroutine_frame_other`
    calls). Discharged automatically from `MultiPlacedLib.InElf` by
    `MultiPlacedLib.subroutineOk_toPureMem`. -/
def MultiPlacedLib.withCodeLoaded {α : Type} (lib : MultiPlacedLib) (mpl : MultiPlacement)
    (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜lib.CodeLoaded mpl s0.mem⌝ }

/-- Layout-generic correctness of the multi-block library's exported function `fnName`: `fnName`
    is one of `lib.exports`, defined in some block `i` (`lookupBlockSym fnName lib.blocks = some (i, off)`),
    and for every multi-block placement `mpl` under which `lib` is `Placeable`, `subroutine_ok`
    holds for block `i`'s placed program (`lib.blockProgram mpl i externs overrides`) at the
    function's address `lib.fnAddr mpl fnName`, with `lib.withCodeLoaded mpl` adjoined to the spec
    instantiated at `mpl` and block `i`'s base `mpl.base i`. -/
abbrev MultiPlacedLib.subroutineOk {S α : Type} [ToBaseSpec S α] (lib : MultiPlacedLib)
    (fnName : String) (spec : MultiPlacement → S)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none) : Prop :=
  fnName ∈ lib.exports ∧ ∃ i off, lookupBlockSym fnName lib.blocks = some (i, off) ∧
    ∀ mpl : MultiPlacement, lib.Placeable mpl →
      subroutine_ok (lib.blockProgram mpl i externs overrides) (lib.fnAddr mpl fnName)
        (lib.withCodeLoaded mpl (ToBaseSpec.toSpec (spec mpl) (mpl.base i)))

end Arm64.Obj


