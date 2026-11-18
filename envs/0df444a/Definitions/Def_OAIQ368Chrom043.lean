-- Prove2me | Definitions.Def_OAIQ368Chrom043
-- name    : OAIQ368Chrom043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:52:13.936802+00:00
-- url     : https://prove2.me/theorems/272b66a1-cc9c-4fa3-b763-7666ee83d72c
-- title:
--   Definitions bundle OAIQ368Chrom043 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 1 definition and 7 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.sourceTripleAssoc`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_PointEvaluation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/PointEvaluation.lean), [`Chromatic_Shuffle_PolynomialExtendInjective`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/PolynomialExtendInjective.lean), [`Chromatic_Shuffle_TripleFiltration`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/TripleFiltration.lean), [`Chromatic_Walls_UnitalCoproductNaturality`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/UnitalCoproductNaturality.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom040` and `OAIQ368Chrom041` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom046`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom040
import Definitions.Def_OAIQ368Chrom041

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PointEvaluation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma centerNumerator_ne_zero (a : I → I → ℕ) (T : SplitTree I) :
    centerNumerator a T T.centerPairs≠0 := by
  exact Finset.prod_ne_zero_iff.mpr fun ij hij=>
    pow_ne_zero _ (diagonal_ne_zero (T.centerPairs_ne ij hij))

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TripleFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LinearDetection
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma sourceTensorFiltration_lower (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) :
    sourceTensorFiltration a c η hc θ d e (-interaction a d d+-interaction a e e)=⊤ :=
  additiveTensorFiltration_top _ _ _ _ (sourceFiltration_lower a c η hc θ d)
    (sourceFiltration_lower a c η hc θ e)

theorem sourceTripleFiltration_iff (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e f : I → ℕ) (W : ℤ)
    (x : (B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e)⊗[ℚ]
      B a (SlopeArithmetic.slope c η) f) :
    x∈sourceTripleFiltration a c η hc θ d e f W ↔
      ∀ i : RestrictionIndex c η θ d, ∀ j : RestrictionIndex c η θ e, ∀ k : RestrictionIndex c η θ f,
        i.weight a+j.weight a+k.weight a<W → TensorProduct.map
          (TensorProduct.map (indexedRestriction a c η hc θ d i) (indexedRestriction a c η hc θ e j))
          (indexedRestriction a c η hc θ f k) x=0 := by
  have hd := funext (sourceTensorFiltration_eq_testFiltration a c η hc θ d e)
  have hf := funext (sourceFiltration_eq_testFiltration a c η hc θ f)
  unfold sourceTripleFiltration
  rw [hd,hf]
  have ht := additiveTensorFiltration_iff_tests
    (indexedTensorRestriction a c η hc θ d e) (indexedRestriction a c η hc θ f)
    (fun j=>j.1.weight a+j.2.weight a) (RestrictionIndex.weight a)
    (-interaction a d d+-interaction a e e) (-interaction a f f)
    (by rw [←hd,sourceTensorFiltration_lower]) (by rw [←hf,sourceFiltration_lower]) W x
  apply ht.trans
  constructor
  · exact fun h i j k=>h (i,j) k
  · exact fun h ij k=>h ij.1 ij.2 k

lemma triple_leading_restrictions_detect (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e f : I → ℕ) (W : ℤ)
    (x : (B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e)⊗[ℚ]
      B a (SlopeArithmetic.slope c η) f)
    (hx : x∈sourceTripleFiltration a c η hc θ d e f W)
    (h : ∀ i : RestrictionIndex c η θ d, ∀ j : RestrictionIndex c η θ e, ∀ k : RestrictionIndex c η θ f,
      i.weight a+j.weight a+k.weight a=W → TensorProduct.map
        (TensorProduct.map (indexedRestriction a c η hc θ d i) (indexedRestriction a c η hc θ e j))
        (indexedRestriction a c η hc θ f k) x=0) :
    x∈sourceTripleFiltration a c η hc θ d e f (W+1) := by
  rw [sourceTripleFiltration_iff] at hx ⊢
  intro i j k hijk
  by_cases hw : i.weight a+j.weight a+k.weight a=W
  · exact h i j k hw
  · exact hx i j k (by omega)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PolynomialExtendInjective
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.pairAdd
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.tripleAdd
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.tripleFilterAdd
noncomputable def sourceTripleAssoc (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : I → ℕ) (W : ℤ) :
    sourceTripleFiltration a c η hc θ d e f W ≃ₗ[ℚ]
      additiveTensorFiltration (sourceFiltration a c η hc θ d)
        (sourceTensorFiltration a c η hc θ e f) W :=
  tensorFiltrationAssoc (sourceFiltration a c η hc θ d) (sourceFiltration a c η hc θ e)
    (sourceFiltration a c η hc θ f) W

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_UnitalCoproductNaturality
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] unitalSepTensor unitalSepTensorA

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.naturalTensorAdd
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.naturalTensorModule
lemma unitalSeparationConstant_zero_right_any (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (d : I → ℕ) (x : B a (slope c η) (d+0)) :
    unitalSeparationConstant a c η hc d 0 (Or.inr (Or.inl rfl)) x=
      castB a (slope c η) (add_zero d) x⊗ₜ[ℚ](1:B a (slope c η) 0) := by
  have h := unitalSeparationConstant_zero_right a c η hc d
    (castB a (slope c η) (add_zero d) x)
  simpa only [castB_trans,castB_rfl] using h

lemma unitalSeparationConstant_map_zero_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (d e : I → ℕ)
    (x : B a (slope c η) d⊗[ℚ]B a (slope c η) (e+0)) :
    TensorProduct.map LinearMap.id (unitalSeparationConstant a c η hc e 0 (Or.inr (Or.inl rfl))) x=
      TensorProduct.assoc ℚ _ _ _
        ((TensorProduct.map LinearMap.id (castBLinear a (slope c η) (add_zero e)) x)⊗ₜ[ℚ]
          (1:B a (slope c η) 0)) := by
  apply TensorTransport.map_right_insert
  intro y
  rw [castBLinear_apply]
  exact unitalSeparationConstant_zero_right_any a c η hc e y

lemma unitalCoproduct_coassoc_zero_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e)
    (x : B a (slope c η) ((d+e)+0)) :
    TensorProduct.assoc ℚ _ _ _
      (TensorProduct.map (unitalSeparationConstant a c η hc d e (hd.compatible he)) LinearMap.id
        (unitalSeparationConstant a c η hc (d+e) 0 (Or.inr (Or.inl rfl)) x))=
      TensorProduct.map LinearMap.id
        (unitalSeparationConstant a c η hc e 0 (Or.inr (Or.inl rfl)))
        (unitalSeparationConstant a c η hc d (e+0)
          (hd.compatible (he.add hc (Or.inl rfl)))
          (castB a (slope c η) (add_assoc d e 0) x)) := by
  rw [unitalSeparationConstant_map_zero_right]
  have h := unitalSeparationConstant_cast a c η hc (rfl : d=d) (add_zero e)
    (hd.compatible (he.add hc (Or.inl rfl))) (hd.compatible he)
    (castB a (slope c η) (add_assoc d e 0) x)
  simp only [castBLinear_rfl] at h ⊢
  rw [←h]
  rw [unitalSeparationConstant_zero_right_any,TensorProduct.map_tmul,LinearMap.id_apply,
    castB_trans]

end ElementaryPositivity.RawShuffle

end

end OAI
end


