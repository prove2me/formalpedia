-- Prove2me | Definitions.Def_OAIQ368Chrom040
-- name    : OAIQ368Chrom040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:48:06.468863+00:00
-- url     : https://prove2.me/theorems/5f4c893d-48ae-460d-917a-0562dc9d51f8
-- title:
--   Definitions bundle OAIQ368Chrom040 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 94 declarations of OpenAI's Lean: 36 definitions, 1 inductive type or structure, 4 instances and 53 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.PBWAdmissible`, `OAI.ElementaryPositivity.RawShuffle.PBWWord`, `OAI.ElementaryPositivity.RawShuffle.RightSlopeTriple`, `OAI.ElementaryPositivity.RawShuffle.SignedGlobalTensor`, `OAI.ElementaryPositivity.RawShuffle.SignedWordCut`, `OAI.ElementaryPositivity.RawShuffle.SignedWordCut.prependLeft`, `OAI.ElementaryPositivity.RawShuffle.SignedWordCut.prependRight`, `OAI.ElementaryPositivity.RawShuffle.SourceAssociatedGrade`, `OAI.ElementaryPositivity.RawShuffle.SourceTensorAssociatedGrade`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.crossPower`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.crossSign`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.refinedTripleCenterPolynomial`, `OAI.ElementaryPositivity.RawShuffle.emptyCutSum`, `OAI.ElementaryPositivity.RawShuffle.globalColorSign`, `OAI.ElementaryPositivity.RawShuffle.globalCounit`, `OAI.ElementaryPositivity.RawShuffle.globalHomogeneous`, `OAI.ElementaryPositivity.RawShuffle.globalPrimitives`, `OAI.ElementaryPositivity.RawShuffle.globalSignedComm`, `OAI.ElementaryPositivity.RawShuffle.globalUnit`, `OAI.ElementaryPositivity.RawShuffle.gradeSeparationCoefficient`, `OAI.ElementaryPositivity.RawShuffle.indexedTensorRestriction`, `OAI.ElementaryPositivity.RawShuffle.nextFiltration`, `OAI.ElementaryPositivity.RawShuffle.primitiveWord`, `OAI.ElementaryPositivity.RawShuffle.separationCoproduct`, `OAI.ElementaryPositivity.RawShuffle.signedLeft`, `OAI.ElementaryPositivity.RawShuffle.signedLeftAlgHom`, `OAI.ElementaryPositivity.RawShuffle.signedMapProduct`, `OAI.ElementaryPositivity.RawShuffle.signedRight`, `OAI.ElementaryPositivity.RawShuffle.signedRightAlgHom`, `OAI.ElementaryPositivity.RawShuffle.signedWordCuts`, `OAI.ElementaryPositivity.RawShuffle.singletonCutSum`, `OAI.ElementaryPositivity.RawShuffle.sourceGradeDimensionEquiv`, `OAI.ElementaryPositivity.RawShuffle.wordCutTensor`, `OAI.ElementaryPositivity.RawShuffle.wordWeight`, `OAI.ElementaryPositivity.RawShuffle.zeroGradeCounit`, `OAI.ElementaryPositivity.RawShuffle.zeroPolynomialEquiv`, `OAI.ElementaryPositivity.RawShuffle.zeroQuotientEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_Shuffle_GlobalConvolutionSeries`, `Chromatic_Shuffle_GlobalCoproductCocommutative`, `Chromatic_Shuffle_GlobalCoproductUnits`, `Chromatic_Shuffle_GlobalPBWIndependent`, `Chromatic_Shuffle_GlobalPrimitiveBracket`, `Chromatic_Shuffle_GlobalPrimitiveGeneration`, `Chromatic_Shuffle_GlobalSeriesEvaluation`, `Chromatic_Shuffle_GlobalTensorInduction`, `Chromatic_Shuffle_GlobalTripleGradeInclusion`, `Chromatic_Shuffle_GlobalWordDetection`, `Chromatic_Shuffle_GlobalWordPairing`, `Chromatic_Shuffle_GradedCoproduct`, `Chromatic_Shuffle_LeadingIndex`, `Chromatic_Shuffle_PolynomialExtendInjective`, `Chromatic_Shuffle_SymbolSwap`, `Chromatic_Shuffle_TensorPolynomialAssoc`, `Chromatic_Shuffle_TensorSymbolSwap`, `Chromatic_Shuffle_TripleFiltration`, `Chromatic_Shuffle_UnitalCoproductCoassociative`, `Chromatic_Shuffle_UnitalCoproductComparison`, `Chromatic_Shuffle_UnitalCoproductUnits`, `Chromatic_Shuffle_UnitalGradeCoproductUnits`, `Chromatic_Walls_FilteredTensorComm`, `Chromatic_Walls_Grade`, `Chromatic_Walls_TripleSymbols`, `Chromatic_Walls_UnitalCoproductNaturality`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom035` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom042`, `OAIQ368Chrom043`, `OAIQ368Chrom044` and `OAIQ368Chrom050`; the statements `OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_independent` and `OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_span`; the proofs of `OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds` and `OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom035

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_LeadingIndex
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def nextFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) :
    Submodule ℚ (sourceFiltration a c η hc θ d W) :=
  (sourceFiltration a c η hc θ d (W+1)).comap (sourceFiltration a c η hc θ d W).subtype

abbrev SourceAssociatedGrade (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) :=
  (sourceFiltration a c η hc θ d W) ⧸ nextFiltration a c η hc θ d W

end ElementaryPositivity.RawShuffle

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

noncomputable def indexedTensorRestriction (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (j : RestrictionIndex c η θ d × RestrictionIndex c η θ e) :=
  TensorProduct.map (indexedRestriction a c η hc θ d j.1) (indexedRestriction a c η hc θ e j.2)

lemma sourceTensorFiltration_eq_testFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :
    sourceTensorFiltration a c η hc θ d e W=testFiltration (indexedTensorRestriction a c η hc θ d e)
      (fun j=>j.1.weight a+j.2.weight a) W := by
  ext x
  rw [sourceTensorFiltration_iff,mem_testFiltration]
  constructor
  · exact fun h j=>h j.1 j.2
  · exact fun h i j=>h (i,j)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TripleSymbols
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def refinedTripleCenterPolynomial (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ) :
    ((B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) M.dim)⊗[ℚ]
      B a (SlopeArithmetic.slope c η) N.dim) →ₗ[ℚ]
    MvPolynomial ((L.node M).node N).Centers
      (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)) :=
  ((centerTranslation (quotientFamily a (SlopeArithmetic.slope c η)) (taylorB a (SlopeArithmetic.slope c η))
    ((L.node M).node N)).comp
    (Algebra.TensorProduct.map (Algebra.TensorProduct.map (restrictionB a c η hc θ L hL)
      (restrictionB a c η hc θ M hM)) (restrictionB a c η hc θ N hN))).toLinearMap

lemma refinedTripleCenterPolynomial_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (x : B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) M.dim)
    (y : B a (SlopeArithmetic.slope c η) N.dim) :
    refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN (x⊗ₜ[ℚ]y)=
      box (refinedCenterPolynomial a c η hc θ L M hL hM x)
        (centeredRestrictionB a c η hc θ N hN y) := by
  unfold refinedTripleCenterPolynomial
  rw [AlgHom.toLinearMap_apply,AlgHom.comp_apply,Algebra.TensorProduct.map_tmul]
  erw [centerTranslation_tmul]
  rfl

lemma refinedTripleCenterPolynomial_coeff_test (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (k : L.Degrees) (l : M.Degrees) (m : N.Degrees)
    (z : L.Centers →₀ ℕ) (w : M.Centers →₀ ℕ) (t : N.Centers →₀ ℕ)
    (x : (B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) M.dim)⊗[ℚ]
      B a (SlopeArithmetic.slope c η) N.dim) :
    componentTensor a (SlopeArithmetic.slope c η) ((L.node M).node N) ((k,l),m)
      ((refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN x).coeff ((z.sumElim w).sumElim t))=
      TensorProduct.map (TensorProduct.map (restrictionTest a c η hc θ L hL rfl k z)
        (restrictionTest a c η hc θ M hM rfl l w)) (restrictionTest a c η hc θ N hN rfl m t) x := by
  induction x using OAI.tensorInductionOn with
  | tmul x y =>
    rw [refinedTripleCenterPolynomial_tmul,coeff_box,TensorProduct.map_tmul]
    change componentTensor a (SlopeArithmetic.slope c η) (.node L M) (k,l) _⊗ₜ[ℚ]
      componentTensor a (SlopeArithmetic.slope c η) N m _=_
    rw [refinedCenterPolynomial_coeff_test]
    rfl
  | add x y hx hy =>
    rw [(refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN).map_add,
      MvPolynomial.coeff_add]
    simp only [LinearMap.map_add,hx,hy]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_Grade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
noncomputable def zeroPolynomialEquiv : S (0 : I → ℕ) ≃ₗ[ℚ] ℚ where
  toFun f := constantCoeff f.val
  invFun r := r • (1 : S (0 : I → ℕ))
  left_inv := fun f=>(S_zero_eq_scalar f).symm
  right_inv := by intro r; simp
  map_add' f g := by simp
  map_smul' r f := by simp

noncomputable def zeroQuotientEquiv (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) :
    B a μ 0 ≃ₗ[ℚ] ℚ :=
  ((destabilizingSpace a μ 0).quotEquivOfEqBot (destabilizingSpace_zero a μ)).trans zeroPolynomialEquiv

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GradedCoproduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open SeparationInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

abbrev SourceTensorAssociatedGrade (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :=
  LinearFiltration.Grade (sourceTensorFiltration a c η hc θ d e W)
    (sourceTensorFiltration a c η hc θ d e (W+1))

noncomputable def gradeSeparationCoefficient (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W j : ℤ) :
    SourceAssociatedGrade a c η hc θ (d+e) W →ₗ[ℚ]
      SourceTensorAssociatedGrade a c η hc θ d e W :=
  LinearFiltration.map (sourceFiltration a c η hc θ (d+e) W)
    (sourceFiltration a c η hc θ (d+e) (W+1))
    (sourceTensorFiltration a c η hc θ d e W)
    (sourceTensorFiltration a c η hc θ d e (W+1))
    (separationCoefficient a c η hc hs j)
    (separationCoefficient_filtration a c η hc θ d e hs W j)
    (separationCoefficient_filtration a c η hc θ d e hs (W+1) j)

noncomputable def separationCoproduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W : ℤ) :
    SourceAssociatedGrade a c η hc θ (d+e) W →ₗ[ℚ]
      SourceTensorAssociatedGrade a c η hc θ d e W :=
  gradeSeparationCoefficient a c η hc θ d e hs W 0

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
open scoped TensorProduct
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace SplitTree

lemma tensorTest_next_zero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (W : ℤ) (x : B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) R.dim)
    (hx : x∈sourceTensorFiltration a c η hc θ L.dim R.dim (W+1))
    (k : L.Degrees) (l : R.Degrees) (z : L.Centers →₀ ℕ) (w : R.Centers →₀ ℕ)
    (hw : (2*L.totalDegree k+L.doubleShift a)+(2*R.totalDegree l+R.doubleShift a)=W) :
    TensorProduct.map (restrictionTest a c η hc θ L hL rfl k z)
      (restrictionTest a c η hc θ R hR rfl l w) x=0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨U,V,x,y,hUV,hx,hy,rfl⟩
    rw [TensorProduct.map_tmul]
    by_cases h : 2*L.totalDegree k+L.doubleShift a<U
    · rw [sourceFiltration_allTrees a c η hc θ U x hx L hL rfl k z h,TensorProduct.zero_tmul]
    · rw [sourceFiltration_allTrees a c η hc θ V y hy R hR rfl l w (by omega),TensorProduct.tmul_zero]
  | zero => exact map_zero _
  | add x y hx hy hix hiy => rw [map_add,hix,hiy,add_zero]
  | smul r x hx hix => rw [map_smul,hix,smul_zero]

end SplitTree

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalCoproductUnits
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LaurentAtInfinity
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] unitalSepTensor unitalSepTensorA unitalSepTensorN unitalSepTensorM

lemma unitalSeparationConstant_zero_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) (d : I → ℕ) (f : B a (slope c η) d) :
    unitalSeparationConstant a c η hc 0 d (Or.inl rfl)
      (castB a (slope c η) (zero_add d).symm f) =
      (1 : B a (slope c η) 0) ⊗ₜ[ℚ] f := by
  change ((quotientInverseKernelUnit a (slope c η) 0 d).val *
    polynomial (unitalRestrictionRelativeB a c η hc (Or.inl rfl)
      (castB a (slope c η) (zero_add d).symm f))).coeff 0 = _
  rw [quotientInverseKernelUnit_zero_left, Units.val_one, one_mul]
  rw [show (0 : ℤ) = -(0 : ℕ) by simp, polynomial_coeff]
  change (relativeTaylorB a (slope c η) 0 d
    (restrictionBUnit a c η hc (Or.inl rfl) (firstCut 0 d)
      (castB a (slope c η) (zero_add d).symm f))).coeff 0 = _
  rw [relativeTaylorB_coeff_zero, restrictionBUnit_zero_left]

lemma unitalSeparationConstant_zero_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) (d : I → ℕ) (f : B a (slope c η) d) :
    unitalSeparationConstant a c η hc d 0 (Or.inr (Or.inl rfl))
      (castB a (slope c η) (add_zero d).symm f) =
      f ⊗ₜ[ℚ] (1 : B a (slope c η) 0) := by
  change ((quotientInverseKernelUnit a (slope c η) d 0).val *
    polynomial (unitalRestrictionRelativeB a c η hc (Or.inr (Or.inl rfl))
      (castB a (slope c η) (add_zero d).symm f))).coeff 0 = _
  rw [quotientInverseKernelUnit_zero_right, Units.val_one, one_mul]
  rw [show (0 : ℤ) = -(0 : ℕ) by simp, polynomial_coeff]
  change (relativeTaylorB a (slope c η) d 0
    (restrictionBUnit a c η hc (Or.inr (Or.inl rfl)) (firstCut d 0)
      (castB a (slope c η) (add_zero d).symm f))).coeff 0 = _
  rw [relativeTaylorB_coeff_zero, restrictionBUnit_zero_right]

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.ShufflePolynomiality
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma extendPolynomial_map_algebra {A B α β : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (f : A →ₐ[ℚ] B) (j : α → β) (p : MvPolynomial α ℚ) :
    extendPolynomial f j (map (algebraMap ℚ A) p)=
      map (algebraMap ℚ B) (rename j p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp only [map_C,extendPolynomial_C,AlgHom.commutes,rename_C]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp => simp only [map_mul,map_X,extendPolynomial_X,rename_X,hp]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SymbolSwap
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def crossPower (a : I → I → ℕ) (L R : SplitTree I) (φ : ℤ → ℕ) :
    MvPolynomial (L.node R).Centers ℚ :=
  ∏ z : L.Centers,∏ t : R.Centers,
    diagonal (Sum.inl z) (Sum.inr t)^φ (eulerForm a (L.leafDimension z) (R.leafDimension t))

noncomputable def crossSign (a : I → I → ℕ) (L R : SplitTree I) (φ : ℤ → ℕ) : ℚ :=
  ∏ z : L.Centers,∏ t : R.Centers,(-1)^φ (eulerForm a (L.leafDimension z) (R.leafDimension t))

omit [DecidableEq I] in
lemma crossPower_swap (a : I → I → ℕ) (L R : SplitTree I) (φ : ℤ → ℕ)
    (hs : ∀ z t,eulerForm a (L.leafDimension z) (R.leafDimension t)=
      eulerForm a (R.leafDimension t) (L.leafDimension z)) :
    rename (Equiv.sumComm L.Centers R.Centers) (crossPower a L R φ)=
      C (crossSign a L R φ)*crossPower a R L φ := by
  classical
  unfold crossPower crossSign
  simp only [map_prod,map_pow,diagonal,map_sub,rename_X,Equiv.sumComm_apply,
    Sum.swap_inl,Sum.swap_inr]
  rw [Finset.prod_comm (f:=fun (t : R.Centers) (z : L.Centers)=>
    (X (Sum.inr z)-X (Sum.inl t))^φ (eulerForm a (R.leafDimension t) (L.leafDimension z))),
    ←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro z hz
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t ht
  rw [hs z t,←mul_pow]
  congr 1
  simp only [map_neg,map_one]
  ring

omit [DecidableEq I] in
lemma crossSign_sq (a : I → I → ℕ) (L R : SplitTree I) (φ : ℤ → ℕ) :
    crossSign a L R φ*crossSign a L R φ=1 := by
  unfold crossSign
  rw [←Finset.prod_mul_distrib]
  simp only [←Finset.prod_mul_distrib,←mul_pow,neg_mul_neg,one_mul,one_pow,Finset.prod_const_one]

omit [DecidableEq I] in
lemma sum_leaf_euler_left (a : I → I → ℕ) (L : SplitTree I) (d : I → ℕ) :
    (∑ z : L.Centers,eulerForm a (L.leafDimension z) d)=eulerForm a L.dim d := by
  classical
  induction L with
  | leaf d => simp [Centers,leafDimension,dim]
  | node T U hT hU =>
    change (∑ z : T.Centers ⊕ U.Centers,eulerForm a ((T.node U).leafDimension z) d)=_
    rw [Fintype.sum_sum_type]
    change (∑ z : T.Centers,eulerForm a (T.leafDimension z) d)+
      (∑ z : U.Centers,eulerForm a (U.leafDimension z) d)=eulerForm a (T.dim+U.dim) d
    rw [hT,hU,eulerForm_add_left]

omit [DecidableEq I] in
lemma sum_leaf_euler_right (a : I → I → ℕ) (d : I → ℕ) (R : SplitTree I) :
    (∑ z : R.Centers,eulerForm a d (R.leafDimension z))=eulerForm a d R.dim := by
  classical
  induction R with
  | leaf d => simp [Centers,leafDimension,dim]
  | node T U hT hU =>
    change (∑ z : T.Centers ⊕ U.Centers,eulerForm a d ((T.node U).leafDimension z))=_
    rw [Fintype.sum_sum_type]
    change (∑ z : T.Centers,eulerForm a d (T.leafDimension z))+
      (∑ z : U.Centers,eulerForm a d (U.leafDimension z))=eulerForm a d (T.dim+U.dim)
    rw [hT,hU,eulerForm_add_right]

lemma negOne_pos_neg (e : ℤ) : (-1:ℚ)^e.toNat*(-1)^(-e).toNat=(-1)^e := by
  cases e with
  | ofNat n => simp
  | negSucc n =>
    have h : Int.negSucc n = -((n+1:ℕ):ℤ) := by omega
    have h0 : (-((n+1:ℕ):ℤ)).toNat=0 := Int.toNat_eq_zero.mpr (by omega)
    rw [h,h0,pow_zero,one_mul,neg_neg,Int.toNat_natCast,zpow_neg,zpow_natCast]
    simp only [←inv_pow,inv_neg,inv_one]

lemma prod_negOne {α : Type*} (s : Finset α) (f : α → ℤ) :
    (∏ i∈s,(-1:ℚ)^f i)=(-1)^(∑ i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx,Finset.sum_insert hx,ih,zpow_add₀ (by norm_num : (-1:ℚ)≠0)]

omit [DecidableEq I] in
lemma crossSign_pos_neg (a : I → I → ℕ) (L R : SplitTree I) :
    crossSign a L R Int.toNat*crossSign a L R (fun e=>(-e).toNat)=
      (-1:ℚ)^eulerForm a L.dim R.dim := by
  unfold crossSign
  rw [←Finset.prod_mul_distrib]
  simp only [←Finset.prod_mul_distrib,negOne_pos_neg,prod_negOne,
    sum_leaf_euler_right,sum_leaf_euler_left]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FilteredTensorComm
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity

lemma linearMap_span_ext {K M N : Type*} [Semiring K] [AddCommMonoid M] [Module K M]
    [AddCommMonoid N] [Module K N] (s : Set M)
    (f g : Submodule.span K s →ₗ[K] N)
    (h : ∀ x (hx : x∈s),f ⟨x,Submodule.subset_span hx⟩=g ⟨x,Submodule.subset_span hx⟩) : f=g := by
  ext ⟨x,hx⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => change f 0=g 0; rw [map_zero,map_zero]
  | add x y hx hy hix hiy =>
    change f (⟨x,hx⟩+⟨y,hy⟩)=g (⟨x,hx⟩+⟨y,hy⟩)
    rw [map_add,map_add,hix,hiy]
  | smul r x hx hix =>
    change f (r • ⟨x,hx⟩)=g (r • ⟨x,hx⟩)
    rw [map_smul,map_smul,hix]

end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorSymbolSwap
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.LinearFiltration
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma box_swap {A B α β : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (p : MvPolynomial α A) (q : MvPolynomial β B) :
    extendPolynomial (Algebra.TensorProduct.comm ℚ A B).toAlgHom (Equiv.sumComm α β)
      (box p q)=box q p := by
  change extendPolynomial _ _
    (extendPolynomial (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A ⊗[ℚ] B) Sum.inl p*
      extendPolynomial (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] A ⊗[ℚ] B) Sum.inr q)=
    extendPolynomial (Algebra.TensorProduct.includeLeft : B →ₐ[ℚ] B ⊗[ℚ] A) Sum.inl q*
      extendPolynomial (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] B ⊗[ℚ] A) Sum.inr p
  rw [map_mul,extendPolynomial_comp,extendPolynomial_comp,mul_comm]
  congr 1

end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
open LinearFiltration
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cocommTensorBCommRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cocommTensorBAlgebra
noncomputable def sourceGradeDimensionEquiv (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e : I → ℕ} (h : d=e) (W : ℤ) :
    SourceAssociatedGrade a c η hc θ d W ≃ₗ[ℚ] SourceAssociatedGrade a c η hc θ e W := by
  subst e
  exact LinearEquiv.refl _ _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalCoproductComparison
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cocommTensorBCommRing cocommTensorBAlgebra

lemma unitalSeparationConstant_eq (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (d e : I → ℕ)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (hde : slope c η d=slope c η e) (x : B a (slope c η) (d+e)) :
    unitalSeparationConstant a c η hc d e hs x=
      separationCoefficient a c η hc (d:=d) (e:=e) hde 0 x := by
  have heq : unitalRestrictionRelativeB a c η hc hs=
      restrictionRelativeB a c η hc hde (firstCut d e) := by
    unfold unitalRestrictionRelativeB restrictionRelativeB
    congr 1
  simp only [unitalSeparationConstant,unitalSeparationSeries,LinearMap.comp_apply,heq,
    separationCoefficient_eq_coeff,separationSeries,neg_zero]
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalCoproductCocommutative
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
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

noncomputable def globalSignedComm (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) :
    UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  (TensorProduct.comm ℚ _ _).toLinearMap.comp (globalSignOperator a c η hc θ)

lemma globalSignOperator_inclusion (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    globalSignOperator a c η hc θ (globalTensorGradeInclusion a c η hc θ d e W x)=
      (-1:ℚ)^eulerForm a d.val e.val • globalTensorGradeInclusion a c η hc θ d e W x := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simp only [map_zero,smul_zero]
  | ha x y hx hy => simp only [map_add,smul_add,hx,hy]
  | ht u x y => rw [globalTensorGradeInclusion_part,globalSignOperator_tmul_lof]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorPolynomialAssoc
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open scoped TensorProduct

lemma box_assoc {A B C α β γ : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra ℚ A] [Algebra ℚ B] [Algebra ℚ C]
    (p : MvPolynomial α A) (q : MvPolynomial β B) (r : MvPolynomial γ C) :
    extendPolynomial (Algebra.TensorProduct.assoc ℚ ℚ ℚ A B C).toAlgHom (Equiv.sumAssoc α β γ)
      (box (box p q) r)=box p (box q r) := by
  change extendPolynomial _ _
    (extendPolynomial (Algebra.TensorProduct.includeLeft : A⊗[ℚ]B →ₐ[ℚ] (A⊗[ℚ]B)⊗[ℚ]C) Sum.inl
      (extendPolynomial (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A⊗[ℚ]B) Sum.inl p *
       extendPolynomial (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] A⊗[ℚ]B) Sum.inr q) *
     extendPolynomial (Algebra.TensorProduct.includeRight : C →ₐ[ℚ] (A⊗[ℚ]B)⊗[ℚ]C) Sum.inr r)=
    extendPolynomial (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A⊗[ℚ](B⊗[ℚ]C)) Sum.inl p *
    extendPolynomial (Algebra.TensorProduct.includeRight : B⊗[ℚ]C →ₐ[ℚ] A⊗[ℚ](B⊗[ℚ]C)) Sum.inr
      (extendPolynomial (Algebra.TensorProduct.includeLeft : B →ₐ[ℚ] B⊗[ℚ]C) Sum.inl q *
       extendPolynomial (Algebra.TensorProduct.includeRight : C →ₐ[ℚ] B⊗[ℚ]C) Sum.inr r)
  simp only [map_mul,extendPolynomial_comp]
  rw [mul_assoc]
  congr 2

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PolynomialExtendInjective
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
lemma extendPolynomial_injective {A B α β : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (f : A →ₐ[ℚ] B) (j : α → β)
    (hf : Function.Injective f) (hj : Function.Injective j) :
    Function.Injective (extendPolynomial f j) := by
  intro p q h
  apply MvPolynomial.map_injective f.toRingHom hf
  apply MvPolynomial.rename_injective j hj
  exact h
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_UnitalCoproductNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TensorTransport
open scoped TensorProduct
variable {M N P X : Type*} [AddCommGroup M] [Module ℚ M]
  [AddCommGroup N] [Module ℚ N] [AddCommGroup P] [Module ℚ P]
  [AddCommGroup X] [Module ℚ X]
lemma map_left_insert (f : X →ₗ[ℚ] M⊗[ℚ]N) (g : X →ₗ[ℚ] N)
    (u : M) (hf : ∀ x,f x=u⊗ₜ[ℚ]g x) (x : X⊗[ℚ]P) :
    TensorProduct.assoc ℚ M N P (TensorProduct.map f LinearMap.id x)=
      u⊗ₜ[ℚ]TensorProduct.map g LinearMap.id x := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,TensorProduct.tmul_add,hx,hy]
  | tmul x y => simp only [TensorProduct.map_tmul,LinearMap.id_apply,hf,TensorProduct.assoc_tmul]
lemma map_right_insert (f : X →ₗ[ℚ] N⊗[ℚ]P) (g : X →ₗ[ℚ] N)
    (u : P) (hf : ∀ x,f x=g x⊗ₜ[ℚ]u) (x : M⊗[ℚ]X) :
    TensorProduct.map LinearMap.id f x=
      TensorProduct.assoc ℚ M N P (TensorProduct.map LinearMap.id g x⊗ₜ[ℚ]u) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,TensorProduct.add_tmul,hx,hy]
  | tmul x y => simp only [TensorProduct.map_tmul,LinearMap.id_apply,hf,TensorProduct.assoc_tmul]
lemma map_middle_left (f : X →ₗ[ℚ] M⊗[ℚ]N) (g : X →ₗ[ℚ] M)
    (u : N) (hf : ∀ x,f x=g x⊗ₜ[ℚ]u) (x : X⊗[ℚ]P) :
    TensorProduct.assoc ℚ M N P (TensorProduct.map f LinearMap.id x)=
      TensorProduct.map LinearMap.id (TensorProduct.mk ℚ N P u)
        (TensorProduct.map g LinearMap.id x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y => simp only [TensorProduct.map_tmul,LinearMap.id_apply,hf,
      TensorProduct.assoc_tmul,TensorProduct.mk_apply]
lemma map_middle_right (f : X →ₗ[ℚ] N⊗[ℚ]P) (g : X →ₗ[ℚ] P)
    (u : N) (hf : ∀ x,f x=u⊗ₜ[ℚ]g x) (x : M⊗[ℚ]X) :
    TensorProduct.map LinearMap.id f x=
      TensorProduct.map LinearMap.id (TensorProduct.mk ℚ N P u)
        (TensorProduct.map LinearMap.id g x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y => simp only [TensorProduct.map_tmul,LinearMap.id_apply,hf,TensorProduct.mk_apply]
end ElementaryPositivity.TensorTransport

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalCoproductCoassociative
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TensorTransport
open scoped TensorProduct
lemma assoc_sub_symm {M N P : Type*} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N] [AddCommGroup P] [Module ℚ P]
    (x : (M⊗[ℚ]N)⊗[ℚ]P) (y : M⊗[ℚ](N⊗[ℚ]P)) :
    TensorProduct.assoc ℚ M N P (x-(TensorProduct.assoc ℚ M N P).symm y)=
      TensorProduct.assoc ℚ M N P x-y := by
  simp only [map_sub,LinearEquiv.apply_symm_apply]
end ElementaryPositivity.TensorTransport

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalTripleGradeInclusion
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

abbrev RightSlopeTriple (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ) :=
  Σ s : SlopeSplit c η hc θ d,SlopeSplit c η hc θ (right s.val)
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalGradeCoproductUnits
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma unitalGradeCoproduct_zero_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ) (W : ℤ)
    (f : UnitalSourceGrade a c η hc θ d W) :
    unitalGradeCoproduct a c η hc θ 0 d (Or.inl rfl) W
      (unitalGradeCast a c η hc θ (zero_add d).symm rfl f)=
      unitalTensorGradeInclusionW a c η hc θ 0 d W 0
        (unitalGradeOne a c η hc θ⊗ₜ[ℚ]
          unitalGradeCast a c η hc θ rfl (sub_zero W).symm f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    simp only [unitalGradeCast_mk,unitalGradeOne,unitalTensorGradeInclusionW,
      unitalGradeCoproduct_mk]
    apply congrArg (mk _ _)
    apply Subtype.ext
    change unitalSeparationConstant a c η hc 0 d (Or.inl rfl)
      (unitalFiltrationCast a c η hc θ (zero_add d).symm rfl f).val=
      (1:B a (slope c η) 0)⊗ₜ[ℚ]
        (unitalFiltrationCast a c η hc θ rfl (sub_zero W).symm f).val
    rw [unitalFiltrationCast_val,unitalFiltrationCast_val]
    exact unitalSeparationConstant_zero_left a c η hc d f.val

lemma unitalGradeCoproduct_zero_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ) (W : ℤ)
    (f : UnitalSourceGrade a c η hc θ d W) :
    unitalGradeCoproduct a c η hc θ d 0 (Or.inr (Or.inl rfl)) W
      (unitalGradeCast a c η hc θ (add_zero d).symm rfl f)=
      unitalTensorGradeInclusionW a c η hc θ d 0 W W
        (f⊗ₜ[ℚ]unitalGradeCast a c η hc θ rfl (sub_self W).symm
          (unitalGradeOne a c η hc θ)) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    simp only [unitalGradeCast_mk,unitalGradeOne,unitalTensorGradeInclusionW,
      unitalGradeCoproduct_mk]
    apply congrArg (mk _ _)
    apply Subtype.ext
    change unitalSeparationConstant a c η hc d 0 (Or.inr (Or.inl rfl))
      (unitalFiltrationCast a c η hc θ (add_zero d).symm rfl f).val=
      f.val⊗ₜ[ℚ](unitalFiltrationCast a c η hc θ rfl (sub_self W).symm _).val
    rw [unitalFiltrationCast_val,unitalFiltrationCast_val]
    exact unitalSeparationConstant_zero_right a c η hc d f.val

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def zeroGradeCounit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) : UnitalSourceGrade a c η hc θ 0 0 →ₗ[ℚ] ℚ :=
  (next (unitalSourceFiltration a c η hc θ 0 0)
    (unitalSourceFiltration a c η hc θ 0 (0+1))).liftQ
    ((zeroQuotientEquiv a (slope c η)).toLinearMap.comp
      (unitalSourceFiltration a c η hc θ 0 0).subtype) (by
        intro x hx
        have hx0 : x.val=0 := by
          change x.val∈unitalSourceFiltration a c η hc θ 0 (0+1) at hx
          simpa only [unitalSourceFiltration_zero,Int.reduceAdd,Int.reduceLE,ite_false, if_false,
            Submodule.mem_bot] using hx
        change zeroQuotientEquiv a (slope c η) x.val=0
        rw [hx0,map_zero])

lemma zeroGradeCounit_mk (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (x : unitalSourceFiltration a c η hc θ 0 0) :
    zeroGradeCounit a c η hc θ (Submodule.Quotient.mk x)=
      zeroQuotientEquiv a (slope c η) x.val := rfl

lemma zeroGradeCounit_one (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) :
    zeroGradeCounit a c η hc θ (unitalGradeOne a c η hc θ)=1 := by
  rw [unitalGradeOne,zeroGradeCounit_mk]
  change MvPolynomial.constantCoeff (1 : S (0:I → ℕ)).val=1
  simp

lemma zeroGrade_eq_scalar (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (x : UnitalSourceGrade a c η hc θ 0 0) :
    x=zeroGradeCounit a c η hc θ x • unitalGradeOne a c η hc θ := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [zeroGradeCounit_mk,unitalGradeOne]
    change mk _ _ x = mk _ _ (_ • _)
    apply congrArg (mk _ _)
    apply Subtype.ext
    change x.val=zeroQuotientEquiv a (slope c η) x.val • (1 : B a (slope c η) 0)
    apply (zeroQuotientEquiv a (slope c η)).injective
    rw [map_smul]
    change zeroQuotientEquiv a (slope c η) x.val =
      zeroQuotientEquiv a (slope c η) x.val • MvPolynomial.constantCoeff (1 : S (0:I → ℕ)).val
    simp

noncomputable def globalUnit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) : UnitalShuffle a c η hc θ :=
  DirectSum.lof ℚ _ (unitalComponent a c η hc θ) 0 (unitalGradeOne a c η hc θ)

noncomputable def globalCounit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) : UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ :=
  (zeroGradeCounit a c η hc θ).comp
    (DirectSum.component ℚ _ (unitalComponent a c η hc θ) 0)

lemma globalCounit_lof_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (x : unitalComponent a c η hc θ 0) :
    globalCounit a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) 0 x)=
      zeroGradeCounit a c η hc θ x := by
  rw [globalCounit,LinearMap.comp_apply,DirectSum.component.lof_self]

lemma globalCounit_lof_ne (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ) (hk : k≠0)
    (x : unitalComponent a c η hc θ k) :
    globalCounit a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)=0 := by
  simp only [globalCounit,LinearMap.comp_apply,DirectSum.component.of,dite_eq_right hk,map_zero]

lemma globalCounit_unit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) : globalCounit a c η hc θ (globalUnit a c η hc θ)=1 := by
  rw [globalUnit,globalCounit_lof_zero,zeroGradeCounit_one]

lemma globalCounit_tensor_nonzero_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (hd : d.val≠0)
    (W : ℤ) (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    TensorProduct.map (globalCounit a c η hc θ) LinearMap.id
      (globalTensorGradeInclusion a c η hc θ d e W x)=0 := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
  | ht u x y =>
    rw [globalTensorGradeInclusion_part,TensorProduct.map_tmul,
      globalCounit_lof_ne a c η hc θ (d,u) (by intro h; exact hd (congrArg (fun k=>k.1.val) h)),
      TensorProduct.zero_tmul]

lemma globalCounit_tensor_nonzero_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (he : e.val≠0)
    (W : ℤ) (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    TensorProduct.map LinearMap.id (globalCounit a c η hc θ)
      (globalTensorGradeInclusion a c η hc θ d e W x)=0 := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
  | ht u x y =>
    rw [globalTensorGradeInclusion_part,TensorProduct.map_tmul,
      globalCounit_lof_ne a c η hc θ (e,W-u) (by intro h; exact he (congrArg (fun k=>k.1.val) h)),
      TensorProduct.tmul_zero]
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalCoproductUnits
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
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

lemma globalLof_gradeOne_cast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (V : ℤ) (h : 0=V) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (0,V)
      (unitalGradeCast a c η hc θ rfl h (unitalGradeOne a c η hc θ))=
      globalUnit a c η hc θ := by
  subst V
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalTensorInduction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma globalTensor_induction (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ)
    (P : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ → Prop)
    (hz : P 0) (ha : ∀ x y,P x → P y → P (x+y))
    (ht : ∀ (k l : SlopeWeight c η hc θ) (x : unitalComponent a c η hc θ k)
      (y : unitalComponent a c η hc θ l),
      P (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y))
    (x : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) : P x := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => exact ha x y hx hy
  | tmul x y =>
    induction x using DirectSum.induction_on with
    | zero => simpa only [TensorProduct.zero_tmul] using hz
    | add x x' hx hx' => rw [TensorProduct.add_tmul]; exact ha _ _ hx hx'
    | of k x =>
      induction y using DirectSum.induction_on with
      | zero => simpa only [TensorProduct.tmul_zero] using hz
      | add y y' hy hy' => rw [TensorProduct.tmul_add]; exact ha _ _ hy hy'
      | of l y => exact ht k l x y

lemma globalLof_mul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
    (k l : SlopeWeight c η hc θ) (x : unitalComponent a c η hc θ k)
    (y : unitalComponent a c η hc θ l) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x *
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y=
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (k+l) (GradedMonoid.GMul.mul x y) :=
  DirectSum.of_mul_of x y
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

omit [DecidableEq I] in
lemma euler_interchange_cocycle (a : I → I → ℕ) (d e f g : I → ℕ) :
    ((-1:ℚ)^eulerForm a d e) * ((-1:ℚ)^eulerForm a (d+f) g)=
      ((-1:ℚ)^eulerForm a f g) * ((-1:ℚ)^eulerForm a d (e+g)) := by
  rw [eulerForm_add_left,eulerForm_add_right,zpow_add₀ (by norm_num : (-1:ℚ)≠0),
    zpow_add₀ (by norm_num : (-1:ℚ)≠0)]
  ring

lemma globalSignedTensorMultiply_assoc_homogeneous (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
    (k l m n p q : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) (y : unitalComponent a c η hc θ l)
    (z : unitalComponent a c η hc θ m) (w : unitalComponent a c η hc θ n)
    (v : unitalComponent a c η hc θ p) (u : unitalComponent a c η hc θ q) :
    globalSignedTensorMultiply a c η hc θ
      (globalSignedTensorMultiply a c η hc θ
        (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]
          DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y)
        (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) m z⊗ₜ[ℚ]
          DirectSum.lof ℚ _ (unitalComponent a c η hc θ) n w))
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) p v⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) q u)=
    globalSignedTensorMultiply a c η hc θ
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y)
      (globalSignedTensorMultiply a c η hc θ
        (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) m z⊗ₜ[ℚ]
          DirectSum.lof ℚ _ (unitalComponent a c η hc θ) n w)
        (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) p v⊗ₜ[ℚ]
          DirectSum.lof ℚ _ (unitalComponent a c η hc θ) q u)) := by
  rw [globalSignedTensorMultiply_tmul_lof,globalSignedTensorMultiply_tmul_lof]
  simp only [map_smul,LinearMap.smul_apply]
  simp only [globalLof_mul]
  rw [globalSignedTensorMultiply_tmul_lof,globalSignedTensorMultiply_tmul_lof]
  simp only [←globalLof_mul,smul_smul,mul_assoc]
  congr 1
  exact euler_interchange_cocycle a l.1.val m.1.val n.1.val p.1.val

lemma globalSignedTensorMultiply_assoc (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
    (x₀ y₀ z₀ : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :
    globalSignedTensorMultiply a c η hc θ (globalSignedTensorMultiply a c η hc θ x₀ y₀) z₀=
      globalSignedTensorMultiply a c η hc θ x₀ (globalSignedTensorMultiply a c η hc θ y₀ z₀) := by
  induction x₀ using globalTensor_induction a c η hc θ with
  | hz => simp only [map_zero,LinearMap.zero_apply]
  | ha x x' hx hx' => simp only [map_add,LinearMap.add_apply,hx,hx']
  | ht k l x y =>
    induction y₀ using globalTensor_induction a c η hc θ with
    | hz => simp only [map_zero,LinearMap.zero_apply]
    | ha z z' hz hz' => simp only [map_add,LinearMap.add_apply,hz,hz']
    | ht m n z w =>
      induction z₀ using globalTensor_induction a c η hc θ with
      | hz => simp only [map_zero]
      | ha v v' hv hv' => simp only [map_add,hv,hv']
      | ht p q v u => exact globalSignedTensorMultiply_assoc_homogeneous a c η hc θ k l m n p q x y z w v u
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma globalSignedTensorMultiply_one_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
    (x : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :
    globalSignedTensorMultiply a c η hc θ
      (globalUnit a c η hc θ⊗ₜ[ℚ]globalUnit a c η hc θ) x=x := by
  induction x using globalTensor_induction a c η hc θ with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht k l x y =>
    rw [globalUnit,globalSignedTensorMultiply_tmul_lof]
    change ((-1:ℚ)^eulerForm a 0 k.1.val) • ((1 * _)⊗ₜ[ℚ](1 * _))=_
    simp only [eulerForm,Pi.zero_apply,Int.natCast_zero,zero_mul,mul_zero,Finset.sum_const_zero,sub_zero,zpow_zero,one_smul]
    exact congrArg₂ (fun x y : UnitalShuffle a c η hc θ=>x⊗ₜ[ℚ]y) (one_mul _) (one_mul _)

lemma globalSignedTensorMultiply_one_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
    (x : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :
    globalSignedTensorMultiply a c η hc θ x
      (globalUnit a c η hc θ⊗ₜ[ℚ]globalUnit a c η hc θ)=x := by
  induction x using globalTensor_induction a c η hc θ with
  | hz => simp only [map_zero,LinearMap.zero_apply]
  | ha x y hx hy => simp only [map_add,LinearMap.add_apply,hx,hy]
  | ht k l x y =>
    rw [globalUnit,globalSignedTensorMultiply_tmul_lof]
    change ((-1:ℚ)^eulerForm a l.1.val 0) • ((_ * 1)⊗ₜ[ℚ](_ * 1))=_
    simp only [eulerForm,Pi.zero_apply,Int.natCast_zero,mul_zero,Finset.sum_const_zero,sub_zero,zpow_zero,one_smul]
    exact congrArg₂ (fun x y : UnitalShuffle a c η hc θ=>x⊗ₜ[ℚ]y) (mul_one _) (mul_one _)

def SignedGlobalTensor (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) :=
  UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ

noncomputable instance instAddCommGroupSignedGlobalTensor (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) : AddCommGroup (SignedGlobalTensor a c η hc θ) :=
  inferInstanceAs (AddCommGroup (UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ))
noncomputable instance instModuleRatSignedGlobalTensor (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) : Module ℚ (SignedGlobalTensor a c η hc θ) :=
  inferInstanceAs (Module ℚ (UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ))
noncomputable instance instRingSignedGlobalTensorOfFactSlopeEulerSymmetric (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)] :
    Ring (SignedGlobalTensor a c η hc θ) where
  mul x y := globalSignedTensorMultiply a c η hc θ x y
  one := globalUnit a c η hc θ⊗ₜ[ℚ]globalUnit a c η hc θ
  one_mul := globalSignedTensorMultiply_one_left a c η hc θ
  mul_one := globalSignedTensorMultiply_one_right a c η hc θ
  mul_assoc := globalSignedTensorMultiply_assoc a c η hc θ
  left_distrib := fun x y z=>map_add (globalSignedTensorMultiply a c η hc θ x) y z
  right_distrib := fun x y z=>by
    exact LinearMap.congr_fun (map_add (globalSignedTensorMultiply a c η hc θ) x y) z
  zero_mul := fun x=>by
    exact LinearMap.congr_fun (map_zero (globalSignedTensorMultiply a c η hc θ)) x
  mul_zero := fun x=>map_zero (globalSignedTensorMultiply a c η hc θ x)
  natCast n := n • (globalUnit a c η hc θ⊗ₜ[ℚ]globalUnit a c η hc θ)
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    change (n+1) • (globalUnit a c η hc θ⊗ₜ[ℚ]globalUnit a c η hc θ)=_
    exact succ_nsmul _ _
  intCast n := n • (globalUnit a c η hc θ⊗ₜ[ℚ]globalUnit a c η hc θ)
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc n := negSucc_zsmul _ _

noncomputable instance instAlgebraRatSignedGlobalTensor (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)] :
    Algebra ℚ (SignedGlobalTensor a c η hc θ) :=
  Algebra.ofModule
    (fun r x y=>LinearMap.congr_fun (map_smul (globalSignedTensorMultiply a c η hc θ) r x) y)
    (fun r x y=>map_smul (globalSignedTensorMultiply a c η hc θ x) r y)
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalConvolutionSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable def signedLeft : UnitalShuffle a c η hc θ →ₗ[ℚ] SignedGlobalTensor a c η hc θ :=
  (TensorProduct.mk ℚ _ _).flip (globalUnit a c η hc θ)
noncomputable def signedRight : UnitalShuffle a c η hc θ →ₗ[ℚ] SignedGlobalTensor a c η hc θ :=
  TensorProduct.mk ℚ _ _ (globalUnit a c η hc θ)

lemma signedLeft_apply (x : UnitalShuffle a c η hc θ) :
    signedLeft a c η hc θ x=x⊗ₜ[ℚ]globalUnit a c η hc θ := rfl
lemma signedRight_apply (x : UnitalShuffle a c η hc θ) :
    signedRight a c η hc θ x=globalUnit a c η hc θ⊗ₜ[ℚ]x := rfl

noncomputable def signedMapProduct (f g : UnitalShuffle a c η hc θ →ₗ[ℚ] SignedGlobalTensor a c η hc θ) :
    UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ →ₗ[ℚ] SignedGlobalTensor a c η hc θ :=
  (LinearMap.mul' ℚ (SignedGlobalTensor a c η hc θ)).comp (TensorProduct.map f g)

lemma signedMapProduct_tmul (f g : UnitalShuffle a c η hc θ →ₗ[ℚ] SignedGlobalTensor a c η hc θ)
    (x y : UnitalShuffle a c η hc θ) :
    signedMapProduct a c η hc θ f g (x⊗ₜ[ℚ]y)=f x*g y := rfl

lemma signedTensor_mul_eq (x y : SignedGlobalTensor a c η hc θ) :
    x*y=globalSignedTensorMultiply a c η hc θ x y := rfl

lemma signedLeft_product (t : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :
    signedMapProduct a c η hc θ (signedLeft a c η hc θ) (signedLeft a c η hc θ) t=
      signedLeft a c η hc θ (LinearMap.mul' ℚ (UnitalShuffle a c η hc θ) t) := by
  induction t using globalTensor_induction a c η hc θ with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht k l x y =>
    rw [signedMapProduct_tmul,signedTensor_mul_eq,LinearMap.mul'_apply,signedLeft_apply,signedLeft_apply,signedLeft_apply]
    rw [globalUnit,globalSignedTensorMultiply_tmul_lof]
    change ((-1:ℚ)^eulerForm a 0 l.1.val) • ((_ * _)⊗ₜ[ℚ]((1:UnitalShuffle a c η hc θ)*1))=(_ * _)⊗ₜ[ℚ]1
    simp only [eulerForm,Pi.zero_apply,Int.natCast_zero,zero_mul,mul_zero,Finset.sum_const_zero,sub_zero,zpow_zero,one_smul]
    exact congrArg₂ (fun x y : UnitalShuffle a c η hc θ=>x⊗ₜ[ℚ]y) rfl (one_mul _)

lemma signedRight_product (t : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :
    signedMapProduct a c η hc θ (signedRight a c η hc θ) (signedRight a c η hc θ) t=
      signedRight a c η hc θ (LinearMap.mul' ℚ (UnitalShuffle a c η hc θ) t) := by
  induction t using globalTensor_induction a c η hc θ with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht k l x y =>
    rw [signedMapProduct_tmul,signedTensor_mul_eq,LinearMap.mul'_apply,signedRight_apply,signedRight_apply,signedRight_apply]
    rw [globalUnit,globalSignedTensorMultiply_tmul_lof]
    change ((-1:ℚ)^eulerForm a k.1.val 0) • (((1:UnitalShuffle a c η hc θ)*1)⊗ₜ[ℚ](_ * _))=1⊗ₜ[ℚ](_ * _)
    simp only [eulerForm,Pi.zero_apply,Int.natCast_zero,mul_zero,Finset.sum_const_zero,sub_zero,zpow_zero,one_smul]
    exact congrArg₂ (fun x y : UnitalShuffle a c η hc θ=>x⊗ₜ[ℚ]y) (one_mul _) rfl

lemma signedLeftRight_product (t : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :
    signedMapProduct a c η hc θ (signedLeft a c η hc θ) (signedRight a c η hc θ) t=t := by
  induction t using globalTensor_induction a c η hc θ with
  | hz => simp only [map_zero]; rfl
  | ha x y hx hy => simp only [map_add,hx,hy]; rfl
  | ht k l x y =>
    rw [signedMapProduct_tmul,signedTensor_mul_eq,signedLeft_apply,signedRight_apply]
    rw [globalUnit,globalSignedTensorMultiply_tmul_lof]
    change ((-1:ℚ)^eulerForm a 0 0) • ((_ * 1)⊗ₜ[ℚ](1 * _))=_
    simp only [eulerForm,Pi.zero_apply,Int.natCast_zero,mul_zero,Finset.sum_const_zero,sub_zero,zpow_zero,one_smul]
    exact congrArg₂ (fun x y : UnitalShuffle a c η hc θ=>x⊗ₜ[ℚ]y) (mul_one _) (one_mul _)

lemma signedRightLeft_product (t : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :
    signedMapProduct a c η hc θ (signedRight a c η hc θ) (signedLeft a c η hc θ) t=
      globalSignedComm a c η hc θ t := by
  induction t using globalTensor_induction a c η hc θ with
  | hz => simp only [map_zero]; rfl
  | ha x y hx hy => simp only [map_add,hx,hy]; rfl
  | ht k l x y =>
    rw [signedMapProduct_tmul,signedTensor_mul_eq,signedRight_apply,signedLeft_apply]
    rw [globalUnit,globalSignedTensorMultiply_tmul_lof]
    change ((-1:ℚ)^eulerForm a k.1.val l.1.val) • ((1 * _)⊗ₜ[ℚ](_ * 1))=_
    rw [globalSignedComm,LinearMap.comp_apply,globalSignOperator_tmul_lof,map_smul]
    simp only [LinearEquiv.coe_coe,TensorProduct.comm_tmul]
    exact congrArg (fun t=>((-1:ℚ)^eulerForm a k.1.val l.1.val) • t)
      (congrArg₂ (fun x y : UnitalShuffle a c η hc θ=>x⊗ₜ[ℚ]y) (one_mul _) (mul_one _))

noncomputable def signedLeftAlgHom : UnitalShuffle a c η hc θ →ₐ[ℚ] SignedGlobalTensor a c η hc θ :=
  AlgHom.ofLinearMap (signedLeft a c η hc θ) rfl
    (fun x y=>(signedLeft_product a c η hc θ (x⊗ₜ[ℚ]y)).symm)
noncomputable def signedRightAlgHom : UnitalShuffle a c η hc θ →ₐ[ℚ] SignedGlobalTensor a c η hc θ :=
  AlgHom.ofLinearMap (signedRight a c η hc θ) rfl
    (fun x y=>(signedRight_product a c η hc θ (x⊗ₜ[ℚ]y)).symm)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPrimitiveGeneration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable def globalHomogeneous (k : SlopeWeight c η hc θ) : Submodule ℚ (UnitalShuffle a c η hc θ) :=
  LinearMap.range (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k)

lemma globalHomogeneous_mul {k l : SlopeWeight c η hc θ} {x y : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalHomogeneous a c η hc θ k) (hy : y ∈ globalHomogeneous a c η hc θ l) :
    x*y ∈ globalHomogeneous a c η hc θ (k+l) := by
  obtain ⟨x,rfl⟩ := hx
  obtain ⟨y,rfl⟩ := hy
  exact ⟨GradedMonoid.GMul.mul x y,(globalLof_mul a c η hc θ k l x y).symm⟩

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalSeriesEvaluation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable def globalPrimitives : Submodule ℚ (UnitalShuffle a c η hc θ) :=
  LinearMap.ker (globalCoproduct a c η hc θ -
    ((TensorProduct.mk ℚ (UnitalShuffle a c η hc θ) (UnitalShuffle a c η hc θ)).flip
      (globalUnit a c η hc θ) +
      TensorProduct.mk ℚ (UnitalShuffle a c η hc θ) (UnitalShuffle a c η hc θ)
        (globalUnit a c η hc θ)))

lemma mem_globalPrimitives (x : UnitalShuffle a c η hc θ) :
    x ∈ globalPrimitives a c η hc θ ↔ globalCoproduct a c η hc θ x=
      x⊗ₜ[ℚ]globalUnit a c η hc θ+globalUnit a c η hc θ⊗ₜ[ℚ]x := by
  change globalCoproduct a c η hc θ x -
    (x⊗ₜ[ℚ]globalUnit a c η hc θ+globalUnit a c η hc θ⊗ₜ[ℚ]x)=0 ↔ _
  exact sub_eq_zero

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPrimitiveBracket
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [hχ : Fact (SlopeEulerSymmetric a c η θ)]

def globalColorSign (k l : SlopeWeight c η hc θ) : ℚ := (-1:ℚ)^eulerForm a k.1.val l.1.val

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*}

structure SignedWordCut (J : Type*) where
  left : List J
  right : List J
  coeff : ℚ

def wordWeight (w : J → SlopeWeight c η hc θ) (l : List J) := (l.map w).sum
noncomputable def primitiveWord (b : J → UnitalShuffle a c η hc θ) (l : List J) := (l.map b).prod

def SignedWordCut.prependLeft (i : J) (s : SignedWordCut J) : SignedWordCut J :=
  ⟨i::s.left,s.right,s.coeff⟩
def SignedWordCut.prependRight (w : J → SlopeWeight c η hc θ) (i : J)
    (s : SignedWordCut J) : SignedWordCut J :=
  ⟨s.left,i::s.right,s.coeff*globalColorSign a c η hc θ (w i) (wordWeight c η hc θ w s.left)⟩

def signedWordCuts (w : J → SlopeWeight c η hc θ) : List J → List (SignedWordCut J)
  | [] => [⟨[],[],1⟩]
  | i::l => (signedWordCuts w l).map (SignedWordCut.prependLeft i) ++
      (signedWordCuts w l).map (SignedWordCut.prependRight a c η hc θ w i)

noncomputable def wordCutTensor (b : J → UnitalShuffle a c η hc θ)
    (s : SignedWordCut J) : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  s.coeff • (primitiveWord a c η hc θ b s.left⊗ₜ[ℚ]primitiveWord a c η hc θ b s.right)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalWordPairing
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*}

noncomputable def emptyCutSum (w : J → SlopeWeight c η hc θ) (l : List J) (g : List J → ℚ) : ℚ :=
  ((signedWordCuts a c η hc θ w l).map fun s => if s.left=[] then s.coeff*g s.right else 0).sum

noncomputable def singletonCutSum (w : J → SlopeWeight c η hc θ) (i : J) (l : List J)
    (g : List J → ℚ) : ℚ :=
  ((signedWordCuts a c η hc θ w l).map fun s => if s.left=[i] then s.coeff*g s.right else 0).sum

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalWordDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*} [LinearOrder J]

def PBWAdmissible (w : J → SlopeWeight c η hc θ) (l : List J) : Prop :=
  l.Pairwise (fun i j=>i≤j ∧ (i=j → globalColorSign a c η hc θ (w i) (w i)=1))

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPBWIndependent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*} [LinearOrder J]

abbrev PBWWord (w : J → SlopeWeight c η hc θ) :=
  {l : List J // PBWAdmissible a c η hc θ w l}

end ElementaryPositivity.RawShuffle

end

end OAI
end


