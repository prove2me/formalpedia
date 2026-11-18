-- Prove2me | Definitions.Def_OAIQ368Chrom045
-- name    : OAIQ368Chrom045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:55:37.496483+00:00
-- url     : https://prove2.me/theorems/d17caa8b-cad2-4797-8401-b2547269c4a7
-- title:
--   Definitions bundle OAIQ368Chrom045 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_GlobalCoproductCoassociative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalCoproductCoassociative.lean), [`Chromatic_Shuffle_GlobalTripleGradeInclusion`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalTripleGradeInclusion.lean), [`Chromatic_Shuffle_TensorSymbolSwap`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/TensorSymbolSwap.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom041` and `OAIQ368Chrom044` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom046`; the proofs of `OAI_ElementaryPositivity_TriangularDynamics_triangularExpression_anchorSupported`, `OAI_ElementaryPositivity_TriangularDynamics_triangularLinear_theta` and `OAI_ElementaryPositivity_TriangularDynamics_triangularTheta_support`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom041
import Definitions.Def_OAIQ368Chrom044

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorSymbolSwap
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
open LinearFiltration
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cocommTensorBCommRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cocommTensorBAlgebra
lemma sourceTensorGradeComm_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) (x : sourceTensorFiltration a c η hc θ d e W) :
    sourceTensorGradeComm a c η hc θ d e W (Submodule.Quotient.mk x)=
      Submodule.Quotient.mk (SplitTree.sourceTensorComm a c η hc θ d e W x) := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalTripleGradeInclusion
attribute [-instance] _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma sum_slopeTriple {A : Type*} [AddCommMonoid A]
    (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ)
    (F : SlopeTriple c η hc θ d → A) :
    ∑ s : SlopeSplit c η hc θ d,∑ t : SlopeSplit c η hc θ (left s.val),
      F (leftTripleView c η hc θ d ⟨s,t⟩)=
    ∑ s : SlopeSplit c η hc θ d,∑ t : SlopeSplit c η hc θ (right s.val),
      F (rightTripleView c η hc θ d ⟨s,t⟩) := by
  rw [←Fintype.sum_sigma',←Fintype.sum_sigma']
  let e := (leftTripleEquiv c η hc θ d).trans (rightTripleEquiv c η hc θ d).symm
  exact Fintype.sum_equiv e _ _ (fun p=>by
    apply congrArg F
    exact ((rightTripleEquiv c η hc θ d).apply_symm_apply
      (leftTripleEquiv c η hc θ d p)).symm)
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalCoproductCoassociative
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma globalIteratedRightSplit_build (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ)
    (k : SlopeWeight c η hc θ) (p : SlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    globalIteratedRightSplit a c η hc θ k (rightTripleBuild c η hc θ k.1.val p).1
      (rightTripleBuild c η hc θ k.1.val p).2 x=
      globalTripleCoproduct a c η hc θ k p x := by
  simpa only [globalTripleCoproduct, LinearMap.comp_apply, LinearEquiv.coe_coe] using
    (globalIteratedRightSplit_natural a c η hc θ k
    (rightTripleBuild c η hc θ k.1.val p).1 (rightTripleBuild c η hc θ k.1.val p).2
    ⟨p.val.1,p.property.2.1⟩ ⟨p.val.2.1,p.property.2.2.1⟩ ⟨p.val.2.2,p.property.2.2.2⟩
    (right_ofPair p.val.1 (p.val.2.1+p.val.2.2) ((add_assoc _ _ _).symm.trans p.property.1)) rfl
    rfl (right_ofPair p.val.2.1 p.val.2.2 (by simp only [rightTripleBuild, right_ofPair]))
    ((add_assoc _ _ _).symm.trans p.property.1) x)

lemma globalIteratedRightSplit_view (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ)
    (k : SlopeWeight c η hc θ) (p : RightSlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    globalIteratedRightSplit a c η hc θ k p.1 p.2 x=
      globalTripleCoproduct a c η hc θ k (rightTripleView c η hc θ k.1.val p) x := by
  have hh := globalIteratedRightSplit_build a c η hc θ k
    (rightTripleView c η hc θ k.1.val p) x
  rw [rightTripleBuild_view] at hh
  exact hh

lemma globalIteratedRight_sum (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ)
    (k : SlopeWeight c η hc θ) (x : unitalComponent a c η hc θ k) :
    (∑ s : SlopeSplit c η hc θ k.1.val,∑ t : SlopeSplit c η hc θ (right s.val),
        globalIteratedRightSplit a c η hc θ k s t x)=
      ∑ s : SlopeSplit c η hc θ k.1.val,∑ t : SlopeSplit c η hc θ (right s.val),
        globalTripleCoproduct a c η hc θ k (rightTripleView c η hc θ k.1.val ⟨s,t⟩) x := by
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  exact globalIteratedRightSplit_view a c η hc θ k ⟨s,t⟩ x

end ElementaryPositivity.RawShuffle

end

end OAI
end


