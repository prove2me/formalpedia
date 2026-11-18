-- Prove2me | Definitions.Def_OAIQ368Chrom052
-- name    : OAIQ368Chrom052
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T19:32:22.344051+00:00
-- url     : https://prove2.me/theorems/cde21962-00bd-401c-8b01-fcf45028c859
-- title:
--   Definitions bundle OAIQ368Chrom052 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_UnitalOriginalDegree`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/UnitalOriginalDegree.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom049` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom053`; the proof of `OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom049

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalOriginalDegree
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)

lemma unitalAssociatedComponent_mk (d : I → ℕ) (W ℓ : ℤ)
    (f : unitalSourceFiltration a c η hc θ d W) :
    unitalAssociatedComponent a c η hc θ d W ℓ (Submodule.Quotient.mk f)=
      (Submodule.Quotient.mk ⟨componentB a (slope c η) d ℓ f.val,
        unitalSourceFiltration_component_mem a c η hc θ d W ℓ f.val f.property⟩ :
      UnitalSourceGrade a c η hc θ d W) := rfl

lemma unitalAssociatedComponent_nonzero (d : I → ℕ) (hd : d≠0) (W ℓ : ℤ)
    (x : UnitalSourceGrade a c η hc θ d W) :
    unitalGradeNonzeroEquiv a c η hc θ d hd W (unitalAssociatedComponent a c η hc θ d W ℓ x)=
      associatedComponent a c η hc θ d W ℓ (unitalGradeNonzeroEquiv a c η hc θ d hd W x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [unitalAssociatedComponent_mk,unitalGradeNonzeroEquiv_mk,unitalGradeNonzeroEquiv_mk,associatedComponent_mk]

lemma mem_unitalOriginalHomogeneous (d : I → ℕ) (W ℓ : ℤ) (x : UnitalSourceGrade a c η hc θ d W) :
    x∈unitalOriginalHomogeneous a c η hc θ d W ℓ ↔ unitalAssociatedComponent a c η hc θ d W ℓ x=x := by
  simp only [unitalOriginalHomogeneous,LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero]

end ElementaryPositivity.RawShuffle

end

end OAI
end


