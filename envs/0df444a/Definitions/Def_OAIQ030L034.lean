-- Prove2me | Definitions.Def_OAIQ030L034
-- name    : OAIQ030L034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T02:37:44.850171+00:00
-- url     : https://prove2.me/theorems/625b2cfb-6e5e-4242-830c-78f772467db5
-- title:
--   Definitions bundle OAIQ030L034 of the split of OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinGap.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 5 definitions and 1 theorem. The definitions and types are `OAI.LaughlinGap.RealOccupation.Certificate23.representatives`, `OAI.LaughlinGap.pairContractions`, `OAI.LaughlinGap.pairEnergyAt`, `OAI.LaughlinGap.sectorContractions`, `OAI.LaughlinGap.sectorHamiltonian`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinGap_Basic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Basic.lean), [`LaughlinGap_Certificate23`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate23.lean), [`LaughlinGap_Creation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Creation.lean), [`LaughlinGap_SpectralBound`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/SpectralBound.lean).
--
--   **Imports.** It imports the published bundle `Def_LaughlinGap`; the bundles `OAIQ030L000` and `OAIQ030L012` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.LaughlinGap.RealOccupation.Certificate23.keys_checked` and `OAI.LaughlinGap.thm_main`.
-- source:
--   OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_LaughlinGap
import Definitions.Def_OAIQ030L000
import Definitions.Def_OAIQ030L012

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Basic
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.coordinatesFromTensor_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Basic. -/

noncomputable section


namespace LaughlinGap
export _root_.OAI.Laughlin (Configuration State Antisymmetric pairCoefficient pairAmplitude energy SpinorVariables bracket laughlinPolynomial monomialExponent laughlinVector distanceToLaughlinSq )
open scoped BigOperators

noncomputable def pairContractions (N Q : ℕ) :
    TensorHilbert N Q →ₗ[ℂ] EuclideanSpace ℂ (ContractionIndex N Q) where
  toFun ψ := WithLp.toLp 2 (fun t =>
    if t.1 < t.2.1 ∧ t.2.2.2 t.1 = 0 ∧ t.2.2.2 t.2.1 = 0 then
      pairAmplitude (WithLp.ofLp ψ) t.1 t.2.1 t.2.2.1.val t.2.2.2 else 0)
  map_add' := by
    intro ψ φ
    ext t
    change (if _ then pairAmplitude _ _ _ _ _ else _) =
      (if _ then pairAmplitude _ _ _ _ _ else _) + (if _ then pairAmplitude _ _ _ _ _ else _)
    split_ifs
    · simp [pairAmplitude, mul_add, Finset.sum_add_distrib]
    · simp
  map_smul' := by
    intro c ψ
    ext t
    change (if _ then pairAmplitude _ _ _ _ _ else _) =
      c * (if _ then pairAmplitude _ _ _ _ _ else _)
    split_ifs
    · simp [pairAmplitude, Finset.mul_sum, mul_left_comm]
    · simp

noncomputable def sectorContractions (N Q : ℕ) :
    SectorHilbert N Q →ₗ[ℂ] EuclideanSpace ℂ (ContractionIndex N Q) :=
  (pairContractions N Q).comp (antisymmetricSubmodule N Q).subtype

noncomputable def sectorHamiltonian (N Q : ℕ) :
    SectorHilbert N Q →ₗ[ℂ] SectorHilbert N Q :=
  (LinearMap.adjoint (𝕜 := ℂ) (E := SectorHilbert N Q)
    (F := EuclideanSpace ℂ (ContractionIndex N Q)) (sectorContractions N Q)).comp (sectorContractions N Q)

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SpectralBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral Bound. -/

noncomputable section


namespace LaughlinGap
open scoped BigOperators

section LocalKernelConverse
open MvPolynomial

@[simp] theorem pairMoment_zero {Q : ℕ} (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    pairMoment φ 0 = 0 := by
  unfold pairMoment
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  split_ifs with hxy
  · have hx0 : x.val = 0 := by omega
    have hy0 : y.val = 0 := by omega
    simp [hx0, hy0]
  · rfl

end LocalKernelConverse

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Creation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Creation. -/

noncomputable section


namespace LaughlinGap
open scoped BigOperators InnerProduct

noncomputable def pairEnergyAt {N Q : ℕ} (ψ : State N Q) (i j : Fin N) (p : ℕ) : ℝ :=
  ∑ a, if a i = 0 ∧ a j = 0 then ‖pairAmplitude ψ i j p a‖ ^ 2 else 0

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate23. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate23

def representatives : Fin 84 → FourTerm 23 := ![⟨⟨23,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨10,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨23,by decide⟩,(⟨11,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨10,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨10,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨9,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨10,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨9,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨4,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨4,by decide⟩)⟩]
end Certificate23
end LaughlinGap.RealOccupation

end

end OAI
end


