-- Prove2me | Definitions.Def_OAIQ030L030
-- name    : OAIQ030L030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T02:36:31.140326+00:00
-- url     : https://prove2.me/theorems/03212c26-17f6-468f-8f8e-2c8c8275779a
-- title:
--   Definitions bundle OAIQ030L030 of the split of OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinGap.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 7 definitions and 1 theorem. The definitions and types are `OAI.LaughlinGap.RealOccupation.Certificate20.fibers`, `OAI.LaughlinGap.RealOccupation.Certificate20.representatives`, `OAI.LaughlinGap.RealOccupation.Certificate9.fibers`, `OAI.LaughlinGap.RealOccupation.Certificate9.representatives`, `OAI.LaughlinGap.RealOccupation.RowEntry.output`, `OAI.LaughlinGap.RealOccupation.annihilation`, `OAI.LaughlinGap.Spin.LadderSystem.normalized`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinGap_AuxiliaryComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/AuxiliaryComparison.lean), [`LaughlinGap_Certificate20`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate20.lean), [`LaughlinGap_Certificate9`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate9.lean), [`LaughlinGap_RealOccupation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/RealOccupation.lean), [`LaughlinGap_TensorSpin`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/TensorSpin.lean).
--
--   **Imports.** It imports the bundles `OAIQ030L000`, `OAIQ030L002`, `OAIQ030L010`, `OAIQ030L013` and `OAIQ030L014` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ030L035`.
-- source:
--   OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ030L000
import Definitions.Def_OAIQ030L002
import Definitions.Def_OAIQ030L010
import Definitions.Def_OAIQ030L013
import Definitions.Def_OAIQ030L014

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RealOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Occupation. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def annihilation {n : ℕ} (j : Fin n) : FockMatrix n := fun A B =>
  if j ∉ A ∧ B = Occupation.flip j A then
    (-1 : ℝ) ^ (A.filter (fun k => k < j)).card else 0

@[simp] theorem complexify_annihilation {n : ℕ} (j : Fin n) :
    complexify (annihilation j) = Occupation.annihilation j := by
  apply LinearMap.ext
  intro x
  ext A
  change (∑ B, (annihilation j A B : ℂ) * x B) = _
  by_cases hj : j ∈ A
  · simp [annihilation, Occupation.annihilation, Occupation.transition, hj]
  · simp [annihilation, Occupation.annihilation, Occupation.transition, hj,
      Occupation.sign, apply_ite]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_TensorSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

namespace LadderSystem
variable {ι : Type*} [Fintype ι]

noncomputable def normalized (S : LadderSystem ι) (x : ι → ℝ) (d l : ℕ) : ι → ℝ :=
  (1 / Real.sqrt (normalizationFactor d l)) • S.raw x l

end LadderSystem

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_AuxiliaryComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Auxiliary Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

def RowEntry.output {t : Fin 8} (a : RowEntry t) : Fin 9 :=
  ⟨a.val.1.val+a.val.2.val-t.val,by have := a.property; omega⟩

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate20. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate20

def fibers : Fin 54 → Finset (FourTerm 20) := ![{⟨⟨20,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨19,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨20,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨9,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨9,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨6,by decide⟩)⟩}]
def representatives : Fin 54 → FourTerm 20 := ![⟨⟨20,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩]
end Certificate20
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate9. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate9

def fibers : Fin 5 → Finset (FourTerm 9) := ![{⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}]
def representatives : Fin 5 → FourTerm 9 := ![⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩]
end Certificate9
end LaughlinGap.RealOccupation

end

end OAI
end


