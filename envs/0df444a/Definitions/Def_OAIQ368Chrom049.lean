-- Prove2me | Definitions.Def_OAIQ368Chrom049
-- name    : OAIQ368Chrom049
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T19:30:24.785847+00:00
-- url     : https://prove2.me/theorems/c27f2eec-d9f4-464a-b7d8-f10ef44729c6
-- title:
--   Definitions bundle OAIQ368Chrom049 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 150 declarations of OpenAI's Lean: 52 definitions, 2 inductive types or structures, 1 instance and 95 theorems. The definitions and types are `OAI.ElementaryPositivity.LinearFiltration.congr`, `OAI.ElementaryPositivity.PrimitiveStrings.Strings`, `OAI.ElementaryPositivity.PrimitiveStrings.decomposition`, `OAI.ElementaryPositivity.PrimitiveStrings.differentiate`, `OAI.ElementaryPositivity.PrimitiveStrings.evaluate`, `OAI.ElementaryPositivity.PrimitiveStrings.integrate`, `OAI.ElementaryPositivity.RawShuffle.GlobalStringIndex`, `OAI.ElementaryPositivity.RawShuffle.LeadingIndex`, `OAI.ElementaryPositivity.RawShuffle.NonzeroSlopeWeight`, `OAI.ElementaryPositivity.RawShuffle.SlopeStringCoefficient`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.IsProper`, `OAI.ElementaryPositivity.RawShuffle.StringBaseIndex`, `OAI.ElementaryPositivity.RawShuffle.StringPBWGradedIndex`, `OAI.ElementaryPositivity.RawShuffle.StringPBWIndex`, `OAI.ElementaryPositivity.RawShuffle.SymbolIndex`, `OAI.ElementaryPositivity.RawShuffle.associatedComponent`, `OAI.ElementaryPositivity.RawShuffle.convPreservesWeight`, `OAI.ElementaryPositivity.RawShuffle.derivativeB`, `OAI.ElementaryPositivity.RawShuffle.derivativeS`, `OAI.ElementaryPositivity.RawShuffle.globalOriginalHomogeneous`, `OAI.ElementaryPositivity.RawShuffle.globalStringPolynomialDegree`, `OAI.ElementaryPositivity.RawShuffle.globalTensorComponent`, `OAI.ElementaryPositivity.RawShuffle.gradeDerivative`, `OAI.ElementaryPositivity.RawShuffle.gradeMeanMultiply`, `OAI.ElementaryPositivity.RawShuffle.gradeSymbolFamily`, `OAI.ElementaryPositivity.RawShuffle.homogeneousStringBaseBasis`, `OAI.ElementaryPositivity.RawShuffle.homogeneousStringBases`, `OAI.ElementaryPositivity.RawShuffle.indexedSymbol`, `OAI.ElementaryPositivity.RawShuffle.instAddCommGroupSubtypeSourceAssociatedGradeMemSubmoduleRatPrimitiveSpace`, `OAI.ElementaryPositivity.RawShuffle.instAddCommGroupSubtypeSourceAssociatedGradeMemSubmoduleRatPrimitiveSpaceKerPrimitiveDerivative`, `OAI.ElementaryPositivity.RawShuffle.instModuleRatSubtypeSourceAssociatedGradeMemSubmodulePrimitiveSpace`, `OAI.ElementaryPositivity.RawShuffle.instModuleRatSubtypeSourceAssociatedGradeMemSubmodulePrimitiveSpaceKerPrimitiveDerivative`, `OAI.ElementaryPositivity.RawShuffle.instModuleRatSubtypeSourceAssociatedGradeMemSubmodulePrimitiveSpace_1`, `OAI.ElementaryPositivity.RawShuffle.leadingRawMap`, `OAI.ElementaryPositivity.RawShuffle.meanB`, `OAI.ElementaryPositivity.RawShuffle.meanMultiplyB`, `OAI.ElementaryPositivity.RawShuffle.meanS`, `OAI.ElementaryPositivity.RawShuffle.primitiveComponent`, `OAI.ElementaryPositivity.RawShuffle.primitiveDerivative`, `OAI.ElementaryPositivity.RawShuffle.primitiveMeanMultiply` and 14 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_Shuffle_GlobalHilbertGrading`, `Chromatic_Shuffle_GlobalLocalPrimitives`, `Chromatic_Shuffle_GlobalPrimitiveGeneration`, `Chromatic_Shuffle_GlobalPrimitiveStrings`, `Chromatic_Shuffle_GlobalTensorDetection`, `Chromatic_Shuffle_GradedCoproduct`, `Chromatic_Shuffle_Interaction`, `Chromatic_Shuffle_LeadingIndex`, `Chromatic_Shuffle_OriginalDegree`, `Chromatic_Shuffle_PointEvaluation`, `Chromatic_Shuffle_PrimitiveOperators`, `Chromatic_Shuffle_PrimitiveSpace`, `Chromatic_Shuffle_PrimitiveStringBounds`, `Chromatic_Shuffle_RestrictionTestHomogeneity`, `Chromatic_Shuffle_SymbolDetection`, `Chromatic_Shuffle_UnitalOriginalDegree`, `Chromatic_Shuffle_VariableMean`, `Chromatic_Walls_DirectSumSubtype`, `Chromatic_Walls_LinearFiltrationOperators`, `Chromatic_Walls_PrimitiveStrings`, `Chromatic_Walls_Taylor`, `Chromatic_Walls_UnitalGradeComparison`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom047` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom051` and `OAIQ368Chrom052`; the statement `OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom047

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_Taylor
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.map_taylorS _root_.OAI.ElementaryPositivity.RawShuffle.map_taylorSValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.CommonTranslation

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

variable {A : Type*} [CommRing A] [Algebra ℚ A]

section Polynomials
open MvPolynomial
variable {α β : Type*}

lemma taylor_iterate_D (n : ℕ) (p : MvPolynomial α ℚ) :
    taylor ((D.toLinearMap ^ n) p) = (Polynomial.derivative^[n]) (taylor p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    change taylor (D ((D.toLinearMap^n) p)) = _
    rw [← taylor_derivative, ih, Function.iterate_succ_apply']

theorem locally_nilpotent_D (p : MvPolynomial α ℚ) :
    (D.toLinearMap ^ ((taylor p).natDegree+1)) p = 0 := by
  have h := taylor_iterate_D ((taylor p).natDegree+1) p
  rw [Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _)] at h
  have h0 := congrArg (fun q : Polynomial (MvPolynomial α ℚ) => q.coeff 0) h
  simpa using h0

end Polynomials

end ElementaryPositivity.CommonTranslation

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Interaction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
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

theorem leading_restrictions_detect (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d W)
    (h : ∀ (T : SplitTree I), T.IsOrderedList → ∀ (hs : T.OnSlope c η θ)
      (hd : T.dim=d) (k : T.Degrees) (z : T.Centers →₀ ℕ),
      2*T.totalDegree k+T.doubleShift a=W → restrictionTest a c η hc θ T hs hd k z f=0) :
    f∈sourceFiltration a c η hc θ d (W+1) := by
  intro T hT hs hd k z hw
  by_cases he : 2*T.totalDegree k+T.doubleShift a=W
  · exact h T hT hs hd k z he
  · exact hf T hT hs hd k z (by omega)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PointEvaluation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

lemma normalizedSymbol_eq_zero_iff (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (hχ : T.PairSymmetric a) (W : ℤ) (f : sourceFiltration a c η hc θ T.dim W) :
    normalizedSymbol a c η hc θ T hT hχ W f=0 ↔
      totalLeadingPolynomial a c η hc θ T hT W f.val=0 := by
  change map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T))
      (centerNumerator a T T.centerPairs) * clearedLeading a c η hc θ T hT hχ W f=0 ↔ _
  rw [SymbolCoordinates.scalar_mul_eq_zero_iff _ (centerNumerator_ne_zero a T)]
  rw [← denominator_clearedLeading a c η hc θ T hT hχ W f,
    SymbolCoordinates.scalar_mul_eq_zero_iff _ (centerDenominator_ne_zero a T)]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_LeadingIndex
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
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

structure LeadingIndex (c η : I → ℝ) (θ : ℝ) (a : I → I → ℕ)
    (d : I → ℕ) (W : ℤ) where
  tree : SplitTree I
  ordered : tree.IsOrderedList
  onSlope : tree.OnSlope c η θ
  dimension : tree.dim=d
  degree : tree.Degrees
  center : tree.Centers →₀ ℕ
  weight : 2*tree.totalDegree degree+tree.doubleShift a=W

noncomputable def leadingRawMap (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) :
    sourceFiltration a c η hc θ d W →ₗ[ℚ]
      (∀ j : LeadingIndex c η θ a d W,
        SplitTree.tensor (SplitTree.quotientFamily a (SlopeArithmetic.slope c η)) j.tree) :=
  LinearMap.pi fun j => (restrictionTest a c η hc θ j.tree j.onSlope j.dimension j.degree j.center).comp
    (sourceFiltration a c η hc θ d W).subtype

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SymbolDetection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.globalCoalgebra _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationCoefficient_apply _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.leafVarsEquiv_center _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.leafVarsEquiv_pack _root_.OAI.ElementaryPositivity.RawShuffle.castB_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castB_trans _root_.OAI.ElementaryPositivity.RawShuffle.castS_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castS_trans _root_.OAI.ElementaryPositivity.RawShuffle.fourValueAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.restrictionBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

namespace SplitTree

lemma totalLeadingPolynomial_next_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (W : ℤ) (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : f∈sourceFiltration a c η hc θ T.dim (W+1)) :
    totalLeadingPolynomial a c η hc θ T hT W f=0 := by
  ext z
  simp only [totalLeadingPolynomial,coeff_mapLinear,MvPolynomial.coeff_zero,
    Finsupp.zero_apply]
  apply componentTensor_detect a (SlopeArithmetic.slope c η) T
  intro k
  rw [componentTensor_weightComponent]
  split_ifs with hw
  · exact sourceFiltration_allTrees a c η hc θ (W+1) f hf T hT rfl k z (by omega)
  · rfl

lemma totalLeadingPolynomial_zero_test (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (W : ℤ) (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : totalLeadingPolynomial a c η hc θ T hT W f=0)
    (k : T.Degrees) (z : T.Centers →₀ ℕ) (hw : 2*T.totalDegree k+T.doubleShift a=W) :
    restrictionTest a c η hc θ T hT rfl k z f=0 := by
  have h:=congrArg (fun polynomial=>componentTensor a (SlopeArithmetic.slope c η) T k
    (MvPolynomial.coeff z polynomial)) hf
  simpa [totalLeadingPolynomial,coeff_mapLinear,componentTensor_weightComponent,hw,
    restrictionTest,dimensionEquivB] using h
end SplitTree

structure SymbolIndex (c η : I → ℝ) (θ : ℝ) (d : I → ℕ) where
  tree : SplitTree I
  ordered : tree.IsOrderedList
  onSlope : tree.OnSlope c η θ
  dimension : tree.dim=d

noncomputable def indexedSymbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d : I → ℕ) (W : ℤ) (j : SymbolIndex c η θ d) :
    sourceFiltration a c η hc θ d W →ₗ[ℚ]
      MvPolynomial j.tree.Centers (SplitTree.tensor (SplitTree.quotientFamily a (SlopeArithmetic.slope c η)) j.tree) :=
  (SplitTree.normalizedSymbol a c η hc θ j.tree j.onSlope
    (j.tree.pairSymmetric_of_slope a c η θ hχ j.onSlope) W).comp
      (filtrationDimensionEquiv a c η hc θ j.dimension.symm W).toLinearMap

noncomputable def symbolFamily (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ) :
    sourceFiltration a c η hc θ d W →ₗ[ℚ]
      (∀ j : SymbolIndex c η θ d,
        MvPolynomial j.tree.Centers (SplitTree.tensor (SplitTree.quotientFamily a (SlopeArithmetic.slope c η)) j.tree)) :=
  LinearMap.pi (indexedSymbol a c η hc θ hχ d W)

lemma symbolFamily_ker (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ) :
    LinearMap.ker (symbolFamily a c η hc θ hχ d W)=nextFiltration a c η hc θ d W := by
  ext f
  change symbolFamily a c η hc θ hχ d W f=0 ↔ f.val∈sourceFiltration a c η hc θ d (W+1)
  constructor
  · intro hf
    apply leading_restrictions_detect a c η hc θ d W f.val f.property
    intro T hT hs hd k z hw
    have h:=congrFun hf (⟨T,hT,hs,hd⟩ : SymbolIndex c η θ d)
    subst d
    change SplitTree.normalizedSymbol a c η hc θ T hs _ W f=0 at h
    rw [SplitTree.normalizedSymbol_eq_zero_iff] at h
    exact SplitTree.totalLeadingPolynomial_zero_test a c η hc θ T hs W f.val h k z hw
  · intro hf
    funext j
    change indexedSymbol a c η hc θ hχ d W j f=0
    obtain ⟨T,hT,hs,hd⟩:=j
    subst d
    change SplitTree.normalizedSymbol a c η hc θ T hs _ W f=0
    rw [SplitTree.normalizedSymbol_eq_zero_iff]
    exact SplitTree.totalLeadingPolynomial_next_zero a c η hc θ T hs W f.val hf

noncomputable def gradeSymbolFamily (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ) :
    SourceAssociatedGrade a c η hc θ d W →ₗ[ℚ]
      (∀ j : SymbolIndex c η θ d,
        MvPolynomial j.tree.Centers (SplitTree.tensor (SplitTree.quotientFamily a (SlopeArithmetic.slope c η)) j.tree)) :=
  (nextFiltration a c η hc θ d W).liftQ (symbolFamily a c η hc θ hχ d W)
    (le_of_eq (symbolFamily_ker a c η hc θ hχ d W).symm)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_RestrictionTestHomogeneity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationCoefficient_apply _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.leafVarsEquiv_center _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.leafVarsEquiv_pack _root_.OAI.ElementaryPositivity.RawShuffle.castB_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castB_trans _root_.OAI.ElementaryPositivity.RawShuffle.castS_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castS_trans _root_.OAI.ElementaryPositivity.RawShuffle.fourValueAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.restrictionBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace SplitTree
lemma restrictionTest_homogeneous (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (T : SplitTree I) (hs : T.OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) (ℓ : ℤ)
    (hf : f∈gradeB a (SlopeArithmetic.slope c η) T.dim ℓ)
    (k : T.Degrees) (z : T.Centers →₀ ℕ)
    (hz : T.totalDegree k+Finsupp.weight (fun _=>(1:ℤ)) z≠ℓ) :
    restrictionTest a c η hc θ T hs rfl k z f=0 := by
  classical
  induction T generalizing ℓ with
  | leaf d =>
    have hzs : z=Finsupp.single () (z ()) := by apply Finsupp.ext; intro x; cases x; simp
    rw [hzs]
    rw [restrictionTest_leaf_coeff]
    have hh:=taylorB_coeff_graded a (SlopeArithmetic.slope c η) d f ℓ hf (z ())
    have hne : k≠ℓ-(z () : ℤ) := by
      rw [hzs,Finsupp.weight_single] at hz
      change (k : ℤ)+(z () : ℤ) • (1 : ℤ)≠ℓ at hz
      simp only [zsmul_eq_mul, mul_one] at hz
      change (k : ℤ)+(z () : ℤ)≠ℓ at hz
      intro h
      apply hz
      rw [h,sub_add_cancel]
    rw [←(mem_gradeB_iff a _ d (ℓ-(z ():ℤ)) _).mp hh,componentB_componentB,ite_eq_right hne]
    rfl
  | node l r ihl ihr =>
    let z₁:=z.comapDomain Sum.inl Sum.inl_injective.injOn
    let z₂:=z.comapDomain Sum.inr Sum.inr_injective.injOn
    have hzs : z₁.sumElim z₂=z := Finsupp.comapDomain_sumElim_comapDomain z
    rw [←hzs] at hz ⊢
    rw [totalWeight_sumElim] at hz
    rw [restrictionTest_node]
    let μ:=SlopeArithmetic.slope c η
    let Rl:=restrictionTest a c η hc θ l hs.1 rfl k.1 z₁
    let Rr:=restrictionTest a c η hc θ r hs.2 rfl k.2 z₂
    let x:=RawShuffle.restrictionB a c η hc
      ((slope_dim c η hc hs.1).trans (slope_dim c η hc hs.2).symm) (firstCut l.dim r.dim) f
    let F:=TensorProduct.map Rl Rr
    change F x=0
    obtain ⟨s,_,he⟩:=componentTensor_finite_decomposition a μ (.node (.leaf l.dim) (.leaf r.dim)) x
    change (∑ mn∈s,TensorProduct.map (componentB a μ l.dim mn.1) (componentB a μ r.dim mn.2) x)=x at he
    have hterm : ∀ mn∈s,F (TensorProduct.map (componentB a μ l.dim mn.1) (componentB a μ r.dim mn.2) x)=0 := by
      intro mn _
      by_cases hm : mn.1+mn.2=ℓ
      · have hsep : l.totalDegree k.1+Finsupp.weight (fun _=>(1:ℤ)) z₁≠mn.1 ∨
            r.totalDegree k.2+Finsupp.weight (fun _=>(1:ℤ)) z₂≠mn.2 := by
          change l.totalDegree k.1+r.totalDegree k.2+_≠ℓ at hz
          by_contra hh
          push Not at hh
          apply hz
          rw [←hm,←hh.1,←hh.2]
          ring
        generalize x=y
        induction y using OAI.tensorInductionOn with
        | tmul g h =>
          change Rl (componentB a μ l.dim mn.1 g) ⊗ₜ[ℚ] Rr (componentB a μ r.dim mn.2 h)=0
          rcases hsep with hl|hr
          · have hzero:=ihl hs.1 (componentB a μ l.dim mn.1 g) mn.1 ⟨g,rfl⟩ k.1 z₁ hl
            rw [show Rl (componentB a μ l.dim mn.1 g)=0 from hzero,TensorProduct.zero_tmul]
          · have hzero:=ihr hs.2 (componentB a μ r.dim mn.2 h) mn.2 ⟨h,rfl⟩ k.2 z₂ hr
            rw [show Rr (componentB a μ r.dim mn.2 h)=0 from hzero,TensorProduct.tmul_zero]
        | add g h hg hh => simp only [map_add,hg,hh,add_zero]
      · have hzero:=RawShuffle.restrictionB_graded a c η hc
          ((slope_dim c η hc hs.1).trans (slope_dim c η hc hs.2).symm)
          (firstCut l.dim r.dim) f ℓ hf mn.1 mn.2 hm
        change TensorProduct.map (componentB a μ l.dim mn.1) (componentB a μ r.dim mn.2) x=0 at hzero
        rw [hzero,map_zero]
    rw [←he,map_sum]
    exact Finset.sum_eq_zero hterm

lemma restrictionTest_component (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (T : SplitTree I) (hs : T.OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) (ℓ : ℤ) (k : T.Degrees) (z : T.Centers →₀ ℕ) :
    restrictionTest a c η hc θ T hs rfl k z (componentB a (SlopeArithmetic.slope c η) T.dim ℓ f)=
      if ℓ=T.totalDegree k+Finsupp.weight (fun _=>(1:ℤ)) z
      then restrictionTest a c η hc θ T hs rfl k z f else 0 := by
  classical
  split_ifs with h
  · obtain ⟨s,hs',he⟩:=componentB_finite_decomposition a (SlopeArithmetic.slope c η) T.dim f
    let R:=restrictionTest a c η hc θ T hs rfl k z
    change R (componentB a (SlopeArithmetic.slope c η) T.dim ℓ f)=R f
    have hsum : (∑ i∈s,R (componentB a (SlopeArithmetic.slope c η) T.dim i f))=
        R (componentB a (SlopeArithmetic.slope c η) T.dim ℓ f) := by
      apply Finset.sum_eq_single ℓ
      · intro i _ hi
        exact restrictionTest_homogeneous a c η hc θ T hs _ i ⟨f,rfl⟩ k z (by omega)
      · intro hl
        rw [hs' ℓ hl,map_zero]
    rw [←hsum,←map_sum,he]
  · exact restrictionTest_homogeneous a c η hc θ T hs _ ℓ ⟨f,rfl⟩ k z (Ne.symm h)
end SplitTree

lemma sourceFiltration_component_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W ℓ : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d W) :
    componentB a (SlopeArithmetic.slope c η) d ℓ f∈sourceFiltration a c η hc θ d W := by
  intro T ho hs hd k z hw
  subst d
  rw [SplitTree.restrictionTest_component]
  split_ifs
  · exact hf T ho hs rfl k z hw
  · rfl
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial CommonTranslation
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def derivativeS (d : I → ℕ) : Module.End ℚ (S d) :=
  ((Polynomial.lcoeff (S d) 1).restrictScalars ℚ).comp (taylorS d).toLinearMap

omit [Fintype I] [DecidableEq I] in
lemma derivativeS_val (d : I → ℕ) (f : S d) :
    (derivativeS d f).val=D f.val := by
  have h:=congrArg (fun p : Polynomial (MvPolynomial (Σi,Fin (d i)) ℚ)=>p.coeff 1)
    (map_taylorS d f)
  simpa [derivativeS] using h

noncomputable def derivativeB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    Module.End ℚ (B a μ d) :=
  ((Polynomial.lcoeff (B a μ d) 1).restrictScalars ℚ).comp (taylorB a μ d).toLinearMap

lemma derivativeB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (f : S d) :
    derivativeB a μ d (quotientAlg a μ d f)=quotientAlg a μ d (derivativeS d f) := by
  change (taylorB a μ d (quotientAlg a μ d f)).coeff 1=_
  rw [taylorB_mk,Polynomial.coeff_map]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma derivativeS_pow_val (d : I → ℕ) (n : ℕ) (f : S d) :
    ((derivativeS d^n) f).val=(D.toLinearMap^n) f.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ',Module.End.mul_apply,derivativeS_val,ih]
    rfl

lemma derivativeB_pow_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (n : ℕ) (f : S d) :
    (derivativeB a μ d^n) (quotientAlg a μ d f)=quotientAlg a μ d ((derivativeS d^n) f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Module.End.mul_apply,ih,derivativeB_mk]

theorem derivativeB_locally_nilpotent (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (f : B a μ d) : ∃ N : ℕ,(derivativeB a μ d^N) f=0 := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    refine ⟨(taylor f.val).natDegree+1,?_⟩
    change (derivativeB a μ d^_) (quotientAlg a μ d f)=0
    rw [derivativeB_pow_mk]
    have h : (derivativeS d^((taylor f.val).natDegree+1)) f=0 := by
      apply Subtype.ext
      rw [derivativeS_pow_val,locally_nilpotent_D]
      rfl
    rw [h,map_zero]

lemma derivativeB_mul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (f g : B a μ d) :
    derivativeB a μ d (f*g)=derivativeB a μ d f*g+f*derivativeB a μ d g := by
  change (taylorB a μ d (f*g)).coeff 1=_
  rw [map_mul,Polynomial.mul_coeff_one,taylorB_coeff_zero,taylorB_coeff_zero]
  exact add_comm _ _

lemma derivativeB_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d W) :
    derivativeB a (SlopeArithmetic.slope c η) d f∈sourceFiltration a c η hc θ d W := by
  apply polynomial_coeff_mem (sourceFiltration a c η hc θ d W) (taylorB a _ d f)
  intro t
  rw [taylorB_eval]
  exact sourceFiltration_translation_mem a c η hc θ d W f hf t

noncomputable def gradeDerivative (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) : Module.End ℚ (SourceAssociatedGrade a c η hc θ d W) :=
  LinearFiltration.map (sourceFiltration a c η hc θ d W)
    (sourceFiltration a c η hc θ d (W+1))
    (sourceFiltration a c η hc θ d W) (sourceFiltration a c η hc θ d (W+1))
    (derivativeB a (SlopeArithmetic.slope c η) d)
    (fun f hf=>derivativeB_filtered a c η hc θ d W f hf)
    (fun f hf=>derivativeB_filtered a c η hc θ d (W+1) f hf)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LinearFiltrationOperators
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
variable {M : Type*} [AddCommGroup M] [Module ℚ M]

lemma restrict_pow_val (F : Submodule ℚ M) (D : Module.End ℚ M)
    (h : ∀ x∈F,D x∈F) (n : ℕ) (x : F) :
    ((restrict F F D h ^n) x).val=(D^n) x.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ',Module.End.mul_apply]
    change D ((restrict F F D h^n) x).val=_
    rw [ih]

lemma map_pow_mk (F F' : Submodule ℚ M) (D : Module.End ℚ M)
    (h : ∀ x∈F,D x∈F) (h' : ∀ x∈F',D x∈F') (n : ℕ) (x : F) :
    (map F F' F F' D h h'^n) (mk F F' x)=mk F F' ((restrict F F D h^n) x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Module.End.mul_apply,ih]; rfl

lemma map_locally_nilpotent (F F' : Submodule ℚ M) (D : Module.End ℚ M)
    (h : ∀ x∈F,D x∈F) (h' : ∀ x∈F',D x∈F')
    (hnil : ∀ x,∃ N : ℕ,(D^N) x=0) (x : Grade F F') :
    ∃ N : ℕ,(map F F' F F' D h h'^N) x=0 := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    obtain ⟨N,hN⟩:=hnil x.val
    refine ⟨N,?_⟩
    change (map F F' F F' D h h'^N) (mk F F' x)=0
    rw [map_pow_mk]
    have hz : (restrict F F D h^N) x=0 := by
      apply Subtype.ext
      rw [restrict_pow_val,hN]
      rfl
    rw [hz,map_zero]

lemma map_weyl (F F' : Submodule ℚ M) (D T : Module.End ℚ M)
    (hD : ∀ x∈F,D x∈F) (hD' : ∀ x∈F',D x∈F')
    (hT : ∀ x∈F,T x∈F) (hT' : ∀ x∈F',T x∈F')
    (h : ∀ x,D (T x)=T (D x)+x) (x : Grade F F') :
    map F F' F F' D hD hD' (map F F' F F' T hT hT' x)=
      map F F' F F' T hT hT' (map F F' F F' D hD hD' x)+x := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change mk F F' (restrict F F D hD (restrict F F T hT x)) =
      mk F F' (restrict F F T hT (restrict F F D hD x)) + mk F F' x
    rw [←map_add]
    exact congrArg (mk F F') (Subtype.ext (h x.val))

end ElementaryPositivity.LinearFiltration

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_VariableMean
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial CommonTranslation ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def variableSum (d : I → ℕ) : S d := by
  classical
  refine ⟨∑ v : Σi,Fin (d i),X v,?_⟩
  intro σ
  simp only [map_sum,rename_X]
  exact Equiv.sum_comp (packAction (fun i=>Fin (d i)) σ) _

omit [DecidableEq I] in
lemma derivativeS_variableSum (d : I → ℕ) :
    derivativeS d (variableSum d)=(Fintype.card (Σi,Fin (d i)) : S d) := by
  classical
  apply Subtype.ext
  rw [derivativeS_val]
  change D (∑ v : Σi,Fin (d i),X v)=_
  simp only [map_sum,D_X,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma variables_nonempty_of_ne_zero (d : I → ℕ) (hd : d≠0) : Nonempty (Σi,Fin (d i)) := by
  classical
  by_contra h
  apply hd
  funext i
  by_contra hi
  exact h ⟨⟨i,⟨0,Nat.pos_of_ne_zero hi⟩⟩⟩

noncomputable def meanS (d : I → ℕ) : S d :=
  (Fintype.card (Σi,Fin (d i)) : ℚ)⁻¹ • variableSum d

omit [DecidableEq I] in
lemma derivativeS_meanS (d : I → ℕ) (hd : d≠0) : derivativeS d (meanS d)=1 := by
  have :=variables_nonempty_of_ne_zero d hd
  have hn : (Fintype.card (Σi,Fin (d i)) : ℚ)≠0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [meanS,map_smul,derivativeS_variableSum]
  change _ • (algebraMap ℚ (S d) (Fintype.card (Σi,Fin (d i))))=1
  rw [Algebra.smul_def,←map_mul,inv_mul_cancel₀ hn,map_one]

noncomputable def meanB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) : B a μ d :=
  quotientAlg a μ d (meanS d)

lemma derivativeB_meanB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (hd : d≠0) :
    derivativeB a μ d (meanB a μ d)=1 := by
  rw [meanB,derivativeB_mk,derivativeS_meanS d hd,map_one]

noncomputable def meanMultiplyB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    Module.End ℚ (B a μ d) := Algebra.lmul ℚ _ (meanB a μ d)

lemma derivativeB_meanMultiply_weyl (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (hd : d≠0) (f : B a μ d) :
    derivativeB a μ d (meanMultiplyB a μ d f)=
      meanMultiplyB a μ d (derivativeB a μ d f)+f := by
  change derivativeB a μ d (meanB a μ d*f)=meanB a μ d*derivativeB a μ d f+f
  rw [derivativeB_mul,derivativeB_meanB a μ d hd,one_mul,add_comm]

lemma meanMultiplyB_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d W) :
    meanMultiplyB a (SlopeArithmetic.slope c η) d f∈sourceFiltration a c η hc θ d W := by
  change meanB a (SlopeArithmetic.slope c η) d*f∈_
  rw [mul_comm]
  exact sourceFiltration_mul_mem a c η hc θ d W f _ hf

noncomputable def gradeMeanMultiply (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) : Module.End ℚ (SourceAssociatedGrade a c η hc θ d W) :=
  LinearFiltration.map (sourceFiltration a c η hc θ d W)
    (sourceFiltration a c η hc θ d (W+1))
    (sourceFiltration a c η hc θ d W) (sourceFiltration a c η hc θ d (W+1))
    (meanMultiplyB a (SlopeArithmetic.slope c η) d)
    (fun f hf=>meanMultiplyB_filtered a c η hc θ d W f hf)
    (fun f hf=>meanMultiplyB_filtered a c η hc θ d (W+1) f hf)

lemma gradeDerivative_meanMultiply_weyl (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (hd : d≠0) (W : ℤ) (f : SourceAssociatedGrade a c η hc θ d W) :
    gradeDerivative a c η hc θ d W (gradeMeanMultiply a c η hc θ d W f)=
      gradeMeanMultiply a c η hc θ d W (gradeDerivative a c η hc θ d W f)+f := by
  exact LinearFiltration.map_weyl _ _ _ _ _ _ _ _
    (derivativeB_meanMultiply_weyl a (SlopeArithmetic.slope c η) d hd) f

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus ElementaryPositivity.CoefficientIdeals
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace SplitTree

def IsProper : SplitTree I → Prop
  | .leaf _ => False
  | .node _ _ => True
end SplitTree

noncomputable def properSourceFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) : Submodule ℚ (B a (SlopeArithmetic.slope c η) d) where
  carrier := {f | ∀ (T : SplitTree I),T.IsOrderedList → T.IsProper →
    ∀ (hT : T.OnSlope c η θ) (h : T.dim=d) k z,
      2*T.totalDegree k+T.doubleShift a<W → restrictionTest a c η hc θ T hT h k z f=0}
  zero_mem' := by
    intro T ho hp hT h k z hw
    exact (restrictionTest a c η hc θ T hT h k z).map_zero
  add_mem' := by intro f g hf hg T ho hp hT h k z hw; rw [map_add,hf T ho hp hT h k z hw,hg T ho hp hT h k z hw,add_zero]
  smul_mem' := by intro r f hf T ho hp hT h k z hw; rw [map_smul,hf T ho hp hT h k z hw,smul_zero]

lemma properSourceFiltration_translation_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈properSourceFiltration a c η hc θ d W) (t : ℚ) :
    translationB a (SlopeArithmetic.slope c η) d t f∈properSourceFiltration a c η hc θ d W := by
  intro T hT hp hs hd k z hw
  subst d
  let P:=SplitTree.componentTensor a (SlopeArithmetic.slope c η) T k
  have h0 : mapLinear P (SplitTree.centeredRestrictionB a c η hc θ T hs f)=0 := by
    ext s
    rw [coeff_mapLinear,MvPolynomial.coeff_zero]
    exact hf T hT hp hs rfl k s hw
  have h1 : mapLinear P (SplitTree.centeredRestrictionB a c η hc θ T hs
      (translationB a (SlopeArithmetic.slope c η) T.dim t f))=0 := by
    apply eq_of_evalRat
    intro v
    rw [map_zero,evalRat_mapLinear,SplitTree.centeredRestrictionB_translate_eval,
      ←evalRat_mapLinear,h0,map_zero]
  have he:=congrArg (fun polynomial=>MvPolynomial.coeff z polynomial) h1
  change P ((SplitTree.centeredRestrictionB a c η hc θ T hs
    (translationB a (SlopeArithmetic.slope c η) T.dim t f)).coeff z)=0
  simpa only [coeff_mapLinear,MvPolynomial.coeff_zero,Finsupp.zero_apply] using he

lemma properSourceFiltration_mul_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (x y : B a (SlopeArithmetic.slope c η) d)
    (hx : x∈properSourceFiltration a c η hc θ d W) :
    x*y∈properSourceFiltration a c η hc θ d W := by
  intro T hT hp hs hd k z hw
  subst d
  let ρ:=SplitTree.centeredRestrictionB a c η hc θ T hs
  let J:=SplitTree.degreeCutIdeal a (SlopeArithmetic.slope c η) T W
  have hxc : ∀ m,(ρ x).coeff m∈J := by
    intro m j hj
    exact hx T hT hp hs rfl j m hj
  have hxy:=coeff_mul_mem J (ρ x) (ρ y) hxc z
  change SplitTree.componentTensor a (SlopeArithmetic.slope c η) T k ((ρ (x*y)).coeff z)=0
  rw [map_mul]
  exact hxy k hw

lemma proper_next_iff_leading_zero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : sourceFiltration a c η hc θ d W) :
    f.val∈properSourceFiltration a c η hc θ d (W+1) ↔
      ∀ j : LeadingIndex c η θ a d W,j.tree.IsProper → leadingRawMap a c η hc θ d W f j=0 := by
  constructor
  · intro h j hp
    exact h j.tree j.ordered hp j.onSlope j.dimension j.degree j.center (by rw [j.weight]; omega)
  · intro h T ho hp hT hd k z hw
    by_cases hl : 2*T.totalDegree k+T.doubleShift a<W
    · exact f.property T ho hT hd k z hl
    · have he : 2*T.totalDegree k+T.doubleShift a=W := by omega
      exact h ⟨T,ho,hT,hd,k,z,he⟩ hp

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PrimitiveSpace
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.globalCoalgebra _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma proper_next_iff_symbols_zero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)
    (f : sourceFiltration a c η hc θ d W) :
    f.val∈properSourceFiltration a c η hc θ d (W+1) ↔
      ∀ j : SymbolIndex c η θ d,j.tree.IsProper → symbolFamily a c η hc θ hχ d W f j=0 := by
  constructor
  · intro hf j hp
    obtain ⟨T,ho,hs,hd⟩:=j
    subst d
    change SplitTree.normalizedSymbol a c η hc θ T hs _ W f=0
    rw [SplitTree.normalizedSymbol_eq_zero_iff]
    ext z
    simp only [SplitTree.totalLeadingPolynomial,coeff_mapLinear,
      MvPolynomial.coeff_zero,Finsupp.zero_apply]
    apply SplitTree.componentTensor_detect a (SlopeArithmetic.slope c η) T
    intro k
    rw [SplitTree.componentTensor_weightComponent]
    split_ifs with hw
    · exact hf T ho hp hs rfl k z (by omega)
    · rfl
  · intro hf
    rw [proper_next_iff_leading_zero]
    intro j hp
    obtain ⟨T,ho,hs,hd,k,z,hw⟩:=j
    have hh:=hf ⟨T,ho,hs,hd⟩ hp
    subst d
    change SplitTree.normalizedSymbol a c η hc θ T hs _ W f=0 at hh
    rw [SplitTree.normalizedSymbol_eq_zero_iff] at hh
    exact SplitTree.totalLeadingPolynomial_zero_test a c η hc θ T hs W f.val hh k z hw

noncomputable def primitiveSpace (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ) :
    Submodule ℚ (SourceAssociatedGrade a c η hc θ d W) :=
  LinearMap.ker (LinearMap.pi fun j : {j : SymbolIndex c η θ d // j.tree.IsProper} =>
    (LinearMap.proj j.val).comp (gradeSymbolFamily a c η hc θ hχ d W))

lemma primitiveSpace_mk_iff (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)
    (f : sourceFiltration a c η hc θ d W) :
    (Submodule.Quotient.mk f : SourceAssociatedGrade a c η hc θ d W)∈
      primitiveSpace a c η hc θ hχ d W ↔
      f.val∈properSourceFiltration a c η hc θ d (W+1) := by
  rw [proper_next_iff_symbols_zero a c η hc θ hχ d W f]
  change (fun j : {j : SymbolIndex c η θ d // j.tree.IsProper} =>
    symbolFamily a c η hc θ hχ d W f j.val)=0 ↔ _
  constructor
  · intro h j hp
    exact congrFun h ⟨j,hp⟩
  · intro h
    funext j
    exact h j.val j.property

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GradedCoproduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.globalCoalgebra _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
open scoped TensorProduct
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace SplitTree.Regroup
omit [Fintype I] [DecidableEq I] in
lemma proper {T U : SplitTree I} (e : Regroup T U) (hT : T.IsProper) : U.IsProper := by
  induction e with
  | refl T => exact hT
  | assoc T U V => trivial
  | swap T U => trivial
  | node e f he hf => trivial
  | trans e f he hf => exact hf (he hT)
end SplitTree.Regroup

lemma properSourceFiltration_allTrees (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d : I → ℕ} (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈properSourceFiltration a c η hc θ d W) (T : SplitTree I)
    (hp : T.IsProper) (hs : T.OnSlope c η θ) (hd : T.dim=d)
    (k : T.Degrees) (z : T.Centers →₀ ℕ) (hw : 2*T.totalDegree k+T.doubleShift a<W) :
    restrictionTest a c η hc θ T hs hd k z f=0 := by
  obtain ⟨U,hU,⟨e⟩⟩ := SplitTree.Regroup.ordered_normalization T
  apply (e.equivalence (SplitTree.quotientFamily a (SlopeArithmetic.slope c η))).injective
  rw [map_zero,SplitTree.Regroup.restrictionTest_natural a c η hc θ e hs (e.onSlope c η θ hs)]
  apply hf U hU (e.proper hp)
  rw [e.totalDegree,e.doubleShift]
  exact hw

namespace SplitTree
lemma totalLeadingPolynomial_proper_next_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (T : SplitTree I) (hp : T.IsProper)
    (hT : T.OnSlope c η θ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : f∈properSourceFiltration a c η hc θ T.dim (W+1)) :
    totalLeadingPolynomial a c η hc θ T hT W f=0 := by
  ext z
  simp only [totalLeadingPolynomial,coeff_mapLinear,MvPolynomial.coeff_zero,Finsupp.zero_apply]
  apply componentTensor_detect a (SlopeArithmetic.slope c η) T
  intro k
  rw [componentTensor_weightComponent]
  split_ifs with hw
  · exact properSourceFiltration_allTrees a c η hc θ (W+1) f hf T hp hT rfl k z (by omega)
  · rfl

end SplitTree

lemma separationCoproduct_mk_eq_zero_iff (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W : ℤ)
    (f : sourceFiltration a c η hc θ (d+e) W) :
    separationCoproduct a c η hc θ d e hs W (Submodule.Quotient.mk f)=0 ↔
      separationCoefficient a c η hc hs 0 f.val∈sourceTensorFiltration a c η hc θ d e (W+1) :=
  Submodule.Quotient.mk_eq_zero _

lemma separationCoproduct_primitive_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W : ℤ)
    (f : SourceAssociatedGrade a c η hc θ (d+e) W)
    (hf : f∈primitiveSpace a c η hc θ hχ (d+e) W) :
    separationCoproduct a c η hc θ d e hs W f=0 := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [primitiveSpace_mk_iff] at hf
    rw [separationCoproduct_mk_eq_zero_iff]
    apply SplitTree.normalizedTensorSymbol_detect a c η hc θ hχ d e W
      (separationCoefficientRestricted a c η hc θ d e hs W 0 f)
    intro L R hL hR hd he
    subst d
    subst e
    apply (SplitTree.coproduct_normalized_symbol a c η hc θ hχ L R hL hR W f).trans
    rw [SplitTree.normalizedSymbol_eq_zero_iff]
    exact SplitTree.totalLeadingPolynomial_proper_next_zero a c η hc θ (.node L R) trivial ⟨hL,hR⟩ W f.val hf

theorem primitiveSpace_iff_coproducts_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)
    (f : SourceAssociatedGrade a c η hc θ d W) :
    f∈primitiveSpace a c η hc θ hχ d W ↔
      ∀ (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
        (hd : L.dim+R.dim=d),
      separationCoproduct a c η hc θ L.dim R.dim
        ((SplitTree.slope_dim c η hc hL).trans (SplitTree.slope_dim c η hc hR).symm) W
        (hd.symm ▸ f)=0 := by
  constructor
  · intro hf L R hL hR hd
    subst d
    exact separationCoproduct_primitive_zero a c η hc θ hχ L.dim R.dim _ W f hf
  · intro hf
    induction f using Submodule.Quotient.induction_on with
    | H f =>
      rw [primitiveSpace_mk_iff,proper_next_iff_symbols_zero a c η hc θ hχ d W f]
      rintro ⟨T,ho,hs,hd⟩ hp
      subst d
      cases T with
      | leaf d => exact False.elim hp
      | node L R =>
        have hf0:=hf L R hs.1 hs.2 rfl
        rw [separationCoproduct_mk_eq_zero_iff] at hf0
        change SplitTree.normalizedSymbol a c η hc θ (.node L R) hs _ W f=0
        rw [←SplitTree.coproduct_normalized_symbol a c η hc θ hχ L R hs.1 hs.2 W f]
        apply SplitTree.normalizedTensorSymbol_next_zero
        exact hf0

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalTensorDetection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.LinearFiltration DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)

noncomputable def globalTensorComponent (k l : SlopeWeight c η hc θ) :
    UnitalShuffle a c η hc θ ⊗[ℚ] UnitalShuffle a c η hc θ →ₗ[ℚ]
      unitalComponent a c η hc θ k ⊗[ℚ] unitalComponent a c η hc θ l :=
  TensorProduct.map (DirectSum.component ℚ _ (unitalComponent a c η hc θ) k)
    (DirectSum.component ℚ _ (unitalComponent a c η hc θ) l)

lemma globalComponent_lof_ne (k l : SlopeWeight c η hc θ) (h : l≠k)
    (x : unitalComponent a c η hc θ l) :
    DirectSum.component ℚ _ (unitalComponent a c η hc θ) k
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l x)=0 := by
  rw [DirectSum.component.of, dite_eq_right h]

lemma unitalSourceTensorGradeEquiv_symm_part (d e : I → ℕ) (W v : ℤ)
    (x : UnitalSourceGrade a c η hc θ d v) (y : UnitalSourceGrade a c η hc θ e (W-v)) :
    (unitalSourceTensorGradeEquiv a c η hc θ d e W).symm
      (unitalTensorGradeInclusionW a c η hc θ d e W v (x⊗ₜ[ℚ]y))=
      DirectSum.lof ℚ ℤ (fun v=>UnitalSourceGrade a c η hc θ d v⊗[ℚ]UnitalSourceGrade a c η hc θ e (W-v)) v (x⊗ₜ[ℚ]y) :=
  tensorGradeEquiv_symm_inclusion _ _ _ _ W v _

lemma globalTensorComponent_inclusion (d e : slopeDimensions c η hc θ) (W u : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    globalTensorComponent a c η hc θ (d,u) (e,W-u) (globalTensorGradeInclusion a c η hc θ d e W x)=
      DirectSum.component ℚ ℤ _ u ((unitalSourceTensorGradeEquiv a c η hc θ d.val e.val W).symm x) := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht v x y =>
    rw [globalTensorGradeInclusion_part]
    rw [unitalSourceTensorGradeEquiv_symm_part]
    change TensorProduct.map _ _ (_⊗ₜ[ℚ]_)=_
    rw [TensorProduct.map_tmul]
    by_cases hv : v=u
    · subst v
      simp only [DirectSum.component.lof_self]
    · rw [globalComponent_lof_ne a c η hc θ (d,u) (d,v) (by simpa using hv),TensorProduct.zero_tmul,
        DirectSum.component.of,dite_eq_right hv]

lemma globalTensorGradeInclusion_injective (d e : slopeDimensions c η hc θ) (W : ℤ) :
    Function.Injective (globalTensorGradeInclusion a c η hc θ d e W) := by
  intro x y h
  apply (unitalSourceTensorGradeEquiv a c η hc θ d.val e.val W).symm.injective
  apply DirectSum.ext_component ℚ
  intro u
  simpa only [globalTensorComponent_inclusion] using
    congrArg (globalTensorComponent a c η hc θ (d,u) (e,W-u)) h

lemma globalTensorComponent_inclusion_ne_left (k l : SlopeWeight c η hc θ)
    (d e : slopeDimensions c η hc θ) (h : d≠k.1) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    globalTensorComponent a c η hc θ k l (globalTensorGradeInclusion a c η hc θ d e W x)=0 := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
  | ht u x y =>
    rw [globalTensorGradeInclusion_part]
    change TensorProduct.map _ _ (_⊗ₜ[ℚ]_)=0
    rw [TensorProduct.map_tmul,globalComponent_lof_ne a c η hc θ k (d,u)
      (fun he=>h (congrArg Prod.fst he)),TensorProduct.zero_tmul]

lemma globalTensorComponent_split_ne (k : SlopeWeight c η hc θ)
    (s t : SlopeSplit c η hc θ k.1.val) (h : t≠s) (u : ℤ)
    (x : unitalComponent a c η hc θ k) :
    globalTensorComponent a c η hc θ (⟨left s.val,s.property.1⟩,u)
      (⟨right s.val,s.property.2⟩,k.2-u) (globalSplitCoproduct a c η hc θ k t x)=0 := by
  apply globalTensorComponent_inclusion_ne_left
  intro he
  apply h
  exact Subtype.ext (DimensionSplit.ext (congrArg Subtype.val he))

lemma globalTensorComponent_coproduct (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (u : ℤ) (x : unitalComponent a c η hc θ k) :
    globalTensorComponent a c η hc θ (⟨left s.val,s.property.1⟩,u)
      (⟨right s.val,s.property.2⟩,k.2-u)
      (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))=
    globalTensorComponent a c η hc θ (⟨left s.val,s.property.1⟩,u)
      (⟨right s.val,s.property.2⟩,k.2-u) (globalSplitCoproduct a c η hc θ k s x) := by
  rw [globalCoproduct_lof,map_sum,Finset.sum_eq_single s]
  · intro t ht hts
    exact globalTensorComponent_split_ne a c η hc θ k s t hts u x
  · simp

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma globalComponent_unit (k : SlopeWeight c η hc θ) (hk : k.1.val≠0) :
    DirectSum.component ℚ _ (unitalComponent a c η hc θ) k (globalUnit a c η hc θ)=0 :=
  globalComponent_lof_ne a c η hc θ k (0,0)
    (fun h=>hk (congrArg (fun z : SlopeWeight c η hc θ=>z.1.val) h).symm) _

lemma globalPrimitive_split_zero (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (hl : left s.val≠0) (hr : right s.val≠0)
    (x : unitalComponent a c η hc θ k)
    (hx : DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x∈globalPrimitives a c η hc θ) :
    globalSplitCoproduct a c η hc θ k s x=0 := by
  change globalTensorGradeInclusion a c η hc θ _ _ _ _=0
  rw [←map_zero (globalTensorGradeInclusion a c η hc θ ⟨left s.val,s.property.1⟩ ⟨right s.val,s.property.2⟩ k.2)]
  congr 1
  apply (unitalSourceTensorGradeEquiv a c η hc θ (left s.val) (right s.val) k.2).symm.injective
  apply DirectSum.ext_component ℚ
  intro u
  rw [map_zero,map_zero]
  rw [←globalTensorComponent_inclusion a c η hc θ ⟨left s.val,s.property.1⟩ ⟨right s.val,s.property.2⟩ k.2 u]
  change globalTensorComponent a c η hc θ _ _ (globalSplitCoproduct a c η hc θ k s x)=0
  rw [←globalTensorComponent_coproduct,(mem_globalPrimitives a c η hc θ _).mp hx,map_add]
  change TensorProduct.map _ _ (_⊗ₜ[ℚ]_) + TensorProduct.map _ _ (_⊗ₜ[ℚ]_)=0
  rw [TensorProduct.map_tmul,TensorProduct.map_tmul,globalComponent_unit a c η hc θ (⟨left s.val,s.property.1⟩,u) hl,
    globalComponent_unit a c η hc θ (⟨right s.val,s.property.2⟩,k.2-u) hr,TensorProduct.tmul_zero,TensorProduct.zero_tmul,add_zero]

lemma globalPrimitive_iff_split_zero (k : SlopeWeight c η hc θ) (hk : k.1.val≠0)
    (x : unitalComponent a c η hc θ k) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x∈globalPrimitives a c η hc θ ↔
      ∀ s : SlopeSplit c η hc θ k.1.val,left s.val≠0 → right s.val≠0 →
        globalSplitCoproduct a c η hc θ k s x=0 := by
  constructor
  · exact fun hx s hl hr=>globalPrimitive_split_zero a c η hc θ k s hl hr x hx
  · intro hx
    rw [mem_globalPrimitives,globalCoproduct_lof]
    let l := slopeSplitZeroLeft c η hc θ k.1
    let r := slopeSplitZeroRight c η hc θ k.1
    have hlr : l≠r := by
      intro h
      have hh := congrArg (fun s : SlopeSplit c η hc θ k.1.val=>left s.val) h
      exact hk hh.symm
    have hs : (∑ s : SlopeSplit c η hc θ k.1.val,globalSplitCoproduct a c η hc θ k s x)=
        ∑ s∈({l,r} : Finset _),globalSplitCoproduct a c η hc θ k s x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro s _ hs
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hs
      exact hx s (slopeSplit_ne_left_zero c η hc θ k.1 s hs.1)
        (slopeSplit_ne_right_zero c η hc θ k.1 s hs.2)
    rw [hs,Finset.sum_pair hlr,globalSplitCoproduct_zero_left,globalSplitCoproduct_zero_right,add_comm]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_OriginalDegree
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.globalCoalgebra _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma properSourceFiltration_component_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W ℓ : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈properSourceFiltration a c η hc θ d W) :
    componentB a (SlopeArithmetic.slope c η) d ℓ f∈properSourceFiltration a c η hc θ d W := by
  intro T ho hp hs hd k z hw
  subst d
  rw [SplitTree.restrictionTest_component]
  split_ifs
  · exact hf T ho hp hs rfl k z hw
  · rfl

noncomputable def associatedComponent (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W ℓ : ℤ) : Module.End ℚ (SourceAssociatedGrade a c η hc θ d W) :=
  LinearFiltration.map _ _ _ _ (componentB a (SlopeArithmetic.slope c η) d ℓ)
    (fun f hf=>sourceFiltration_component_mem a c η hc θ d W ℓ f hf)
    (fun f hf=>sourceFiltration_component_mem a c η hc θ d (W+1) ℓ f hf)

lemma associatedComponent_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W ℓ : ℤ) (f : sourceFiltration a c η hc θ d W) :
    associatedComponent a c η hc θ d W ℓ (Submodule.Quotient.mk f)=
      (Submodule.Quotient.mk ⟨componentB a (SlopeArithmetic.slope c η) d ℓ f.val,
        sourceFiltration_component_mem a c η hc θ d W ℓ f.val f.property⟩ :
      SourceAssociatedGrade a c η hc θ d W) := rfl

lemma associatedComponent_twice (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W ℓ m : ℤ) (f : SourceAssociatedGrade a c η hc θ d W) :
    associatedComponent a c η hc θ d W ℓ (associatedComponent a c η hc θ d W m f)=
      if ℓ=m then associatedComponent a c η hc θ d W m f else 0 := by
  classical
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    simp only [associatedComponent_mk]
    split_ifs with h
    · apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact (componentB_componentB a _ d ℓ m f.val).trans (ite_eq_left h)
    · rw [show (0 : SourceAssociatedGrade a c η hc θ d W)=Submodule.Quotient.mk 0 from rfl]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact (componentB_componentB a _ d ℓ m f.val).trans (ite_eq_right h)

lemma associatedComponent_finite_decomposition (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ) (W : ℤ)
    (f : SourceAssociatedGrade a c η hc θ d W) :
    ∃ s : Finset ℤ,(∀ ℓ∉s,associatedComponent a c η hc θ d W ℓ f=0) ∧
      (∑ ℓ∈s,associatedComponent a c η hc θ d W ℓ f)=f := by
  classical
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    obtain ⟨s,hs,he⟩:=componentB_finite_decomposition a (SlopeArithmetic.slope c η) d f.val
    refine ⟨s,?_,?_⟩
    · intro ℓ hℓ
      rw [associatedComponent_mk]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change componentB a _ d ℓ f.val∈sourceFiltration a c η hc θ d (W+1)
      rw [hs ℓ hℓ]
      exact Submodule.zero_mem _
    · let g : ℤ → sourceFiltration a c η hc θ d W := fun ℓ=>
        ⟨componentB a (SlopeArithmetic.slope c η) d ℓ f.val,
          sourceFiltration_component_mem a c η hc θ d W ℓ f.val f.property⟩
      change (∑ ℓ∈s,(nextFiltration a c η hc θ d W).mkQ (g ℓ))=_
      rw [←map_sum]
      apply congrArg (nextFiltration a c η hc θ d W).mkQ
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using he

lemma associatedComponent_primitive (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W ℓ : ℤ)
    (f : SourceAssociatedGrade a c η hc θ d W)
    (hf : f∈primitiveSpace a c η hc θ hχ d W) :
    associatedComponent a c η hc θ d W ℓ f∈primitiveSpace a c η hc θ hχ d W := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [associatedComponent_mk]
    apply (primitiveSpace_mk_iff a c η hc θ hχ d W _).mpr
    exact properSourceFiltration_component_mem a c η hc θ d (W+1) ℓ f.val
      ((primitiveSpace_mk_iff a c η hc θ hχ d W f).mp hf)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PrimitiveStrings
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
namespace PrimitiveStrings

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (D T : Module.End ℚ V)

abbrev Strings := ℕ →₀ LinearMap.ker D

noncomputable def evaluate : Strings D →ₗ[ℚ] V :=
  Finsupp.lsum ℚ fun n => (T ^ n).comp (LinearMap.ker D).subtype

@[simp] theorem evaluate_single (n : ℕ) (v : LinearMap.ker D) :
    evaluate D T (Finsupp.single n v) = (T ^ n) v.val := by
  simp [evaluate]

noncomputable def differentiate : Strings D →ₗ[ℚ] Strings D :=
  Finsupp.lsum ℚ fun n =>
    match n with
    | 0 => 0
    | k + 1 => (k + 1 : ℚ) • Finsupp.lsingle k

noncomputable def integrate : Strings D →ₗ[ℚ] Strings D :=
  Finsupp.lsum ℚ fun n => (n + 1 : ℚ)⁻¹ • Finsupp.lsingle (n + 1)

@[simp] theorem differentiate_single_zero (v : LinearMap.ker D) :
    differentiate D (Finsupp.single 0 v) = 0 := by simp [differentiate]

@[simp] theorem differentiate_single_succ (n : ℕ) (v : LinearMap.ker D) :
    differentiate D (Finsupp.single (n + 1) v) =
      Finsupp.single n ((n + 1 : ℚ) • v) := by simp [differentiate]

@[simp] theorem integrate_single (n : ℕ) (v : LinearMap.ker D) :
    integrate D (Finsupp.single n v) =
      Finsupp.single (n + 1) ((n + 1 : ℚ)⁻¹ • v) := by simp [integrate]

 theorem differentiate_apply (f : Strings D) (n : ℕ) :
    differentiate D f n = (n + 1 : ℚ) • f (n + 1) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, smul_add]
  | single k v =>
    cases k with
    | zero => simp
    | succ k =>
      by_cases h : k = n
      · subst k; simp
      · simp [Ne.symm h]

@[simp] theorem differentiate_integrate (f : Strings D) :
    differentiate D (integrate D f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single k v => simp [smul_smul, show (k + 1 : ℚ) ≠ 0 by positivity]

variable (weyl : ∀ v, D (T v) = T (D v) + v)
include weyl

 theorem derivative_string (v : LinearMap.ker D) (n : ℕ) :
    D ((T ^ (n + 1)) v.val) = (n + 1 : ℚ) • (T ^ n) v.val := by
  induction n with
  | zero => simpa using (weyl v.val).trans (by simp)
  | succ n ih =>
    rw [pow_succ' T (n + 1), Module.End.mul_apply, weyl, ih, map_smul]
    rw [← Module.End.mul_apply, ← pow_succ' T n]
    simp only [Nat.cast_add, Nat.cast_one]
    simp only [add_smul, one_smul]

 theorem evaluate_differentiate (f : Strings D) :
    evaluate D T (differentiate D f) = D (evaluate D T f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single n v =>
    cases n with
    | zero => simp
    | succ n => simp [derivative_string D T weyl, map_smul]

theorem evaluate_injective_bounded (N : ℕ) (f : Strings D)
    (bound : ∀ n, N ≤ n → f n = 0) (hf : evaluate D T f = 0) : f = 0 := by
  induction N generalizing f with
  | zero => apply Finsupp.ext; intro n; exact bound n (Nat.zero_le n)
  | succ N ih =>
    have hd : differentiate D f = 0 := by
      apply ih
      · intro n hn
        rw [differentiate_apply, bound (n + 1) (Nat.succ_le_succ hn), smul_zero]
      · rw [evaluate_differentiate D T weyl, hf, map_zero]
    have hpos : ∀ n, f (n + 1) = 0 := by
      intro n
      have h := congrArg (fun g : Strings D => g n) hd
      rw [differentiate_apply] at h
      exact (smul_eq_zero.mp h).resolve_left (by positivity)
    have heq : f = Finsupp.single 0 (f 0) := by
      ext n
      cases n with
      | zero => simp
      | succ n => simp [hpos]
    rw [heq, evaluate_single, pow_zero, Module.End.one_apply] at hf
    rw [heq]
    have hzero : f 0 = 0 := Subtype.ext hf
    rw [hzero, Finsupp.single_zero]

 theorem evaluate_injective : Function.Injective (evaluate D T) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro f hf
  apply evaluate_injective_bounded D T weyl (f.support.sup id + 1) f _ hf
  intro n hn
  by_contra hne
  have hn' : n ≤ f.support.sup id := Finset.le_sup (f := id) (f.mem_support_iff.mpr hne)
  omega

theorem exists_strings_of_pow_eq_zero (N : ℕ) (v : V) (hv : (D ^ N) v = 0) :
    ∃ f : Strings D, evaluate D T f = v := by
  induction N generalizing v with
  | zero =>
    simp only [pow_zero, Module.End.one_apply] at hv
    subst v
    exact ⟨0, map_zero _⟩
  | succ N ih =>
    have hd : (D ^ N) (D v) = 0 := by
      rw [← Module.End.mul_apply, ← pow_succ]
      exact hv
    obtain ⟨f, hf⟩ := ih (D v) hd
    let g := integrate D f
    have hg : D (v - evaluate D T g) = 0 := by
      rw [map_sub, ← evaluate_differentiate D T weyl]
      simp only [g, differentiate_integrate, hf, sub_self]
    let c : LinearMap.ker D := ⟨v - evaluate D T g, hg⟩
    refine ⟨Finsupp.single 0 c + g, ?_⟩
    simp [c]

noncomputable def decomposition (nilpotent : ∀ v : V, ∃ N : ℕ, (D ^ N) v = 0) :
    Strings D ≃ₗ[ℚ] V :=
  LinearEquiv.ofBijective (evaluate D T)
    ⟨evaluate_injective D T weyl, fun v => by
      obtain ⟨N, hv⟩ := nilpotent v
      exact exists_strings_of_pow_eq_zero D T weyl N v hv⟩

end PrimitiveStrings
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PrimitiveOperators
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.globalCoalgebra _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open CommonTranslation
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma derivativeB_properFiltered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈properSourceFiltration a c η hc θ d W) :
    derivativeB a (SlopeArithmetic.slope c η) d f∈properSourceFiltration a c η hc θ d W := by
  apply polynomial_coeff_mem (properSourceFiltration a c η hc θ d W) (taylorB a _ d f)
  intro t
  rw [taylorB_eval]
  exact properSourceFiltration_translation_mem a c η hc θ d W f hf t

lemma meanMultiplyB_properFiltered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈properSourceFiltration a c η hc θ d W) :
    meanMultiplyB a (SlopeArithmetic.slope c η) d f∈properSourceFiltration a c η hc θ d W := by
  change meanB a (SlopeArithmetic.slope c η) d*f∈_
  rw [mul_comm]
  exact properSourceFiltration_mul_mem a c η hc θ d W f _ hf

lemma gradeDerivative_primitive (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)
    (f : SourceAssociatedGrade a c η hc θ d W) (hf : f∈primitiveSpace a c η hc θ hχ d W) :
    gradeDerivative a c η hc θ d W f∈primitiveSpace a c η hc θ hχ d W := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [primitiveSpace_mk_iff] at hf
    let y : sourceFiltration a c η hc θ d W :=
      ⟨derivativeB a (SlopeArithmetic.slope c η) d f.val,
        derivativeB_filtered a c η hc θ d W f.val f.property⟩
    change (Submodule.Quotient.mk y : SourceAssociatedGrade a c η hc θ d W)∈_
    exact (primitiveSpace_mk_iff a c η hc θ hχ d W y).mpr
      (derivativeB_properFiltered a c η hc θ d (W+1) f.val hf)

lemma gradeMeanMultiply_primitive (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)
    (f : SourceAssociatedGrade a c η hc θ d W) (hf : f∈primitiveSpace a c η hc θ hχ d W) :
    gradeMeanMultiply a c η hc θ d W f∈primitiveSpace a c η hc θ hχ d W := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [primitiveSpace_mk_iff] at hf
    let y : sourceFiltration a c η hc θ d W :=
      ⟨meanMultiplyB a (SlopeArithmetic.slope c η) d f.val,
        meanMultiplyB_filtered a c η hc θ d W f.val f.property⟩
    change (Submodule.Quotient.mk y : SourceAssociatedGrade a c η hc θ d W)∈_
    exact (primitiveSpace_mk_iff a c η hc θ hχ d W y).mpr
      (meanMultiplyB_properFiltered a c η hc θ d (W+1) f.val hf)

lemma gradeDerivative_locally_nilpotent (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : SourceAssociatedGrade a c η hc θ d W) :
    ∃ N : ℕ,(gradeDerivative a c η hc θ d W^N) f=0 :=
  LinearFiltration.map_locally_nilpotent _ _ _ _ _
    (derivativeB_locally_nilpotent a (SlopeArithmetic.slope c η) d) f

noncomputable def primitiveDerivative (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ) :
    Module.End ℚ (primitiveSpace a c η hc θ hχ d W) :=
  LinearFiltration.restrict _ _ (gradeDerivative a c η hc θ d W)
    (gradeDerivative_primitive a c η hc θ hχ d W)

noncomputable def primitiveMeanMultiply (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ) :
    Module.End ℚ (primitiveSpace a c η hc θ hχ d W) :=
  LinearFiltration.restrict _ _ (gradeMeanMultiply a c η hc θ d W)
    (gradeMeanMultiply_primitive a c η hc θ hχ d W)

lemma primitive_weyl (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (hd : d≠0) (W : ℤ)
    (f : primitiveSpace a c η hc θ hχ d W) :
    primitiveDerivative a c η hc θ hχ d W (primitiveMeanMultiply a c η hc θ hχ d W f)=
      primitiveMeanMultiply a c η hc θ hχ d W (primitiveDerivative a c η hc θ hχ d W f)+f := by
  apply Subtype.ext
  exact gradeDerivative_meanMultiply_weyl a c η hc θ d hd W f.val

lemma primitiveDerivative_locally_nilpotent (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)
    (f : primitiveSpace a c η hc θ hχ d W) :
    ∃ N : ℕ,(primitiveDerivative a c η hc θ hχ d W^N) f=0 := by
  obtain ⟨N,hN⟩:=gradeDerivative_locally_nilpotent a c η hc θ d W f.val
  refine ⟨N,Subtype.ext ?_⟩
  change ((LinearFiltration.restrict _ _ _ _^N) f).val=0
  rw [LinearFiltration.restrict_pow_val,hN]

noncomputable def primitiveStringDecomposition (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d : I → ℕ) (hd : d≠0) (W : ℤ) :
    PrimitiveStrings.Strings (primitiveDerivative a c η hc θ hχ d W) ≃ₗ[ℚ]
      primitiveSpace a c η hc θ hχ d W :=
  PrimitiveStrings.decomposition (primitiveDerivative a c η hc θ hχ d W)
    (primitiveMeanMultiply a c η hc θ hχ d W)
    (primitive_weyl a c η hc θ hχ d hd W)
    (primitiveDerivative_locally_nilpotent a c η hc θ hχ d W)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_UnitalGradeComparison
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.globalCoalgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
variable {M : Type*} [AddCommGroup M] [Module ℚ M]
noncomputable def congr {F F' G G' : Submodule ℚ M} (h : F=G) (h' : F'=G') :
    Grade F F' ≃ₗ[ℚ] Grade G G' := by
  subst G; subst G'
  exact LinearEquiv.refl ℚ _
lemma congr_mk {F F' G G' : Submodule ℚ M} (h : F=G) (h' : F'=G') (x : F) :
    congr h h' (Submodule.Quotient.mk x)=Submodule.Quotient.mk ⟨x.val,h ▸ x.property⟩ := by
  subst G; subst G'; rfl
end ElementaryPositivity.LinearFiltration

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LinearFiltration ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
noncomputable def unitalGradeNonzeroEquiv (d : I → ℕ) (hd : d≠0) (W : ℤ) :
    UnitalSourceGrade a c η hc θ d W ≃ₗ[ℚ] SourceAssociatedGrade a c η hc θ d W :=
  LinearFiltration.congr (unitalSourceFiltration_nonzero a c η hc θ d hd W)
    (unitalSourceFiltration_nonzero a c η hc θ d hd (W+1))
lemma unitalGradeNonzeroEquiv_mk (d : I → ℕ) (hd : d≠0) (W : ℤ)
    (x : unitalSourceFiltration a c η hc θ d W) :
    unitalGradeNonzeroEquiv a c η hc θ d hd W (Submodule.Quotient.mk x)=
      Submodule.Quotient.mk ⟨x.val,(unitalSourceFiltration_nonzero a c η hc θ d hd W) ▸ x.property⟩ :=
  LinearFiltration.congr_mk _ _ _
noncomputable def unitalTensorGradeNonzeroEquiv (d e : I → ℕ) (hd : d≠0) (he : e≠0) (W : ℤ) :
    UnitalSourceTensorGrade a c η hc θ d e W ≃ₗ[ℚ] SourceTensorAssociatedGrade a c η hc θ d e W :=
  LinearFiltration.congr (unitalSourceTensorFiltration_nonzero a c η hc θ d e hd he W)
    (unitalSourceTensorFiltration_nonzero a c η hc θ d e hd he (W+1))
lemma unitalTensorGradeNonzeroEquiv_mk (d e : I → ℕ) (hd : d≠0) (he : e≠0) (W : ℤ)
    (x : unitalSourceTensorFiltration a c η hc θ d e W) :
    unitalTensorGradeNonzeroEquiv a c η hc θ d e hd he W (Submodule.Quotient.mk x)=
      LinearFiltration.mk (sourceTensorFiltration a c η hc θ d e W)
        (sourceTensorFiltration a c η hc θ d e (W+1))
        ⟨x.val,(unitalSourceTensorFiltration_nonzero a c η hc θ d e hd he W) ▸ x.property⟩ :=
  LinearFiltration.congr_mk _ _ _
lemma unitalGradeCoproduct_nonzero (d e : I → ℕ) (hd : d≠0) (he : e≠0)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (hde : slope c η d=slope c η e) (W : ℤ)
    (x : UnitalSourceGrade a c η hc θ (d+e) W) :
    unitalTensorGradeNonzeroEquiv a c η hc θ d e hd he W (unitalGradeCoproduct a c η hc θ d e hs W x)=
      separationCoproduct a c η hc θ d e hde W
        (unitalGradeNonzeroEquiv a c η hc θ (d+e) (add_ne_zero_left _ _ hd) W x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [unitalGradeCoproduct_mk,unitalTensorGradeNonzeroEquiv_mk,unitalGradeNonzeroEquiv_mk,separationCoproduct_mk]
    apply congrArg (LinearFiltration.mk (sourceTensorFiltration a c η hc θ d e W)
      (sourceTensorFiltration a c η hc θ d e (W+1)))
    apply Subtype.ext
    exact unitalSeparationConstant_eq a c η hc d e hs hde x.val
end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
lemma unitalGradeNonzeroEquiv_cast {d e : I → ℕ} (h : d=e) (hd : d≠0) (he : e≠0) (W : ℤ)
    (x : UnitalSourceGrade a c η hc θ d W) :
    unitalGradeNonzeroEquiv a c η hc θ e he W (unitalGradeCast a c η hc θ h rfl x)=
      h ▸ unitalGradeNonzeroEquiv a c η hc θ d hd W x := by
  subst e
  rfl
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalLocalPrimitives
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open DimensionSplit ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

lemma globalPrimitive_iff_local (d : slopeDimensions c η hc θ) (hd : d.val≠0) (W : ℤ)
    (x : UnitalSourceGrade a c η hc θ d.val W) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,W) x ∈ globalPrimitives a c η hc θ ↔
      unitalGradeNonzeroEquiv a c η hc θ d.val hd W x ∈
        primitiveSpace a c η hc θ Fact.out d.val W := by
  rw [globalPrimitive_iff_split_zero a c η hc θ (d,W) hd x,
    primitiveSpace_iff_coproducts_zero]
  constructor
  · intro hx L R hL hR hde
    have hls : OnSlopeOrZero c η θ L.dim := Or.inr (SplitTree.slope_dim c η hc hL)
    have hrs : OnSlopeOrZero c η θ R.dim := Or.inr (SplitTree.slope_dim c η hc hR)
    let s : SlopeSplit c η hc θ d.val := ⟨ofPair L.dim R.dim hde,by
      constructor
      · exact hls
      · simpa only [right_ofPair] using hrs⟩
    have hz := hx s (SplitTree.dim_ne_zero hL) (by simpa only [s,right_ofPair] using SplitTree.dim_ne_zero hR)
    rw [globalSplitCoproduct_dimensions a c η hc θ (d,W) s L.dim R.dim rfl
      (right_ofPair _ _ hde) hls hrs hde x] at hz
    have hz' := (globalTensorGradeInclusion_injective a c η hc θ ⟨L.dim,hls⟩ ⟨R.dim,hrs⟩ W)
      (hz.trans (map_zero _).symm)
    have hcomp := unitalGradeCoproduct_nonzero a c η hc θ L.dim R.dim
      (SplitTree.dim_ne_zero hL) (SplitTree.dim_ne_zero hR) (hls.compatible hrs)
      ((SplitTree.slope_dim c η hc hL).trans (SplitTree.slope_dim c η hc hR).symm) W
      (unitalGradeCast a c η hc θ hde.symm rfl x)
    rw [hz',map_zero,unitalGradeNonzeroEquiv_cast a c η hc θ hde.symm hd] at hcomp
    exact hcomp.symm
  · intro hx s hl hr
    have hL : (SplitTree.leaf (left s.val)).OnSlope c η θ := ⟨hl,s.property.1.resolve_left hl⟩
    have hR : (SplitTree.leaf (right s.val)).OnSlope c η θ := ⟨hr,s.property.2.resolve_left hr⟩
    have hz := hx (.leaf (left s.val)) (.leaf (right s.val)) hL hR (left_add_right s.val)
    have hcomp := unitalGradeCoproduct_nonzero a c η hc θ (left s.val) (right s.val)
      hl hr (s.property.1.compatible s.property.2) (hL.2.trans hR.2.symm) W
      (unitalGradeCast a c η hc θ (left_add_right s.val).symm rfl x)
    rw [unitalGradeNonzeroEquiv_cast a c η hc θ (left_add_right s.val).symm hd,hz] at hcomp
    have hz' := (unitalTensorGradeNonzeroEquiv a c η hc θ (left s.val) (right s.val) hl hr W).injective
      (hcomp.trans (map_zero _).symm)
    change globalTensorGradeInclusion a c η hc θ _ _ _
      (unitalGradeCoproduct a c η hc θ _ _ _ _ (unitalGradeCast a c η hc θ _ _ x))=0
    rw [hz',map_zero]

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial CommonTranslation
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma derivativeS_component (d : I → ℕ) (ℓ : ℤ) (f : S d) :
    derivativeS d (componentS d ℓ f)=componentS d (ℓ-1) (derivativeS d f) := by
  classical
  rw [←sum_componentS d f]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hh : (derivativeS d (componentS d m f)).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) (m-1) := by
    rw [derivativeS_val]
    exact D_homogeneous _ _ (componentS_homogeneous d m f)
  rw [componentS_componentS,componentS_of_homogeneous d _ hh]
  by_cases h : ℓ=m
  · subst m
    simp
  · simp only [ite_eq_right h,ite_eq_right (by omega : ℓ-1≠m-1),map_zero]

lemma derivativeB_component (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (ℓ : ℤ) (f : B a μ d) :
    derivativeB a μ d (componentB a μ d ℓ f)=componentB a μ d (ℓ-1) (derivativeB a μ d f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change derivativeB a μ d (quotientAlg a μ d (componentS d ℓ f))=
      componentB a μ d (ℓ-1) (derivativeB a μ d (quotientAlg a μ d f))
    rw [derivativeB_mk,derivativeB_mk]
    change quotientAlg a μ d (derivativeS d (componentS d ℓ f))=
      quotientAlg a μ d (componentS d (ℓ-1) (derivativeS d f))
    rw [derivativeS_component]

variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
lemma gradeDerivative_component (d : I → ℕ) (W ℓ : ℤ) (f : SourceAssociatedGrade a c η hc θ d W) :
    gradeDerivative a c η hc θ d W (associatedComponent a c η hc θ d W ℓ f)=
      associatedComponent a c η hc θ d W (ℓ-1) (gradeDerivative a c η hc θ d W f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    apply congrArg (LinearFiltration.mk (sourceFiltration a c η hc θ d W) (sourceFiltration a c η hc θ d (W+1)))
    apply Subtype.ext
    exact derivativeB_component a (SlopeArithmetic.slope c η) d ℓ f.val

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)

noncomputable local instance instAddCommGroupSubtypeSourceAssociatedGradeMemSubmoduleRatPrimitiveSpace : AddCommGroup (primitiveSpace a c η hc θ hχ d W) := Submodule.addCommGroup _
noncomputable local instance instModuleRatSubtypeSourceAssociatedGradeMemSubmodulePrimitiveSpace : Module ℚ (primitiveSpace a c η hc θ hχ d W) := Submodule.module _
noncomputable local instance instAddCommGroupSubtypeSourceAssociatedGradeMemSubmoduleRatPrimitiveSpaceKerPrimitiveDerivative : AddCommGroup (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) := Submodule.addCommGroup _
noncomputable local instance instModuleRatSubtypeSourceAssociatedGradeMemSubmodulePrimitiveSpaceKerPrimitiveDerivative : Module ℚ (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) := Submodule.module _

noncomputable def primitiveComponent (ℓ : ℤ) :
    Module.End ℚ (primitiveSpace a c η hc θ hχ d W) :=
  LinearFiltration.restrict _ _ (associatedComponent a c η hc θ d W ℓ)
    (associatedComponent_primitive a c η hc θ hχ d W ℓ)

lemma primitiveDerivative_component (ℓ : ℤ) (x : primitiveSpace a c η hc θ hχ d W) :
    primitiveDerivative a c η hc θ hχ d W (primitiveComponent a c η hc θ hχ d W ℓ x)=
      primitiveComponent a c η hc θ hχ d W (ℓ-1) (primitiveDerivative a c η hc θ hχ d W x) :=
  Subtype.ext (gradeDerivative_component a c η hc θ d W ℓ x.val)

lemma primitiveComponent_ker (ℓ : ℤ) (x : primitiveSpace a c η hc θ hχ d W)
    (hx : x∈LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) :
    primitiveComponent a c η hc θ hχ d W ℓ x∈LinearMap.ker (primitiveDerivative a c η hc θ hχ d W) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [primitiveDerivative_component,hx,map_zero]

noncomputable def stringBaseComponent (ℓ : ℤ) :
    Module.End ℚ (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) :=
  LinearFiltration.restrict _ _ (primitiveComponent a c η hc θ hχ d W ℓ)
    (primitiveComponent_ker a c η hc θ hχ d W ℓ)

lemma stringBaseComponent_twice (ℓ m : ℤ)
    (x : LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) :
    stringBaseComponent a c η hc θ hχ d W ℓ (stringBaseComponent a c η hc θ hχ d W m x)=
      if ℓ=m then stringBaseComponent a c η hc θ hχ d W m x else 0 := by
  split_ifs with h
  · apply Subtype.ext; apply Subtype.ext
    exact (associatedComponent_twice a c η hc θ d W ℓ m x.val.val).trans (ite_eq_left h)
  · apply Subtype.ext; apply Subtype.ext
    exact (associatedComponent_twice a c η hc θ d W ℓ m x.val.val).trans (ite_eq_right h)

noncomputable def homogeneousStringBases : Set (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) :=
  {x | ∃ ℓ,stringBaseComponent a c η hc θ hχ d W ℓ x=x}

lemma homogeneousStringBases_span :
    ⊤ ≤ Submodule.span ℚ (homogeneousStringBases a c η hc θ hχ d W) := by
  intro x hx
  obtain ⟨s,hs,he⟩:=associatedComponent_finite_decomposition a c η hc θ d W x.val.val
  have he' : (∑ ℓ∈s,stringBaseComponent a c η hc θ hχ d W ℓ x)=x := by
    apply Subtype.ext; apply Subtype.ext
    simp only [Submodule.coe_sum]
    exact he
  rw [←he']
  apply Submodule.sum_mem
  intro ℓ hℓ
  apply Submodule.subset_span
  exact ⟨ℓ,(stringBaseComponent_twice a c η hc θ hχ d W ℓ ℓ x).trans (ite_eq_left rfl)⟩

noncomputable def StringBaseIndex : Type _ :=
  (linearIndepOn_empty ℚ (id : LinearMap.ker (primitiveDerivative a c η hc θ hχ d W) → _)).extend
    (Set.empty_subset (homogeneousStringBases a c η hc θ hχ d W))

noncomputable def homogeneousStringBaseBasis :
    Module.Basis (StringBaseIndex a c η hc θ hχ d W) ℚ
      (LinearMap.ker (primitiveDerivative a c η hc θ hχ d W)) :=
  Module.Basis.ofSpan (homogeneousStringBases_span a c η hc θ hχ d W)

lemma homogeneousStringBaseBasis_exists_degree (i : StringBaseIndex a c η hc θ hχ d W) :
    ∃ ℓ,stringBaseComponent a c η hc θ hχ d W ℓ (homogeneousStringBaseBasis a c η hc θ hχ d W i)=
      homogeneousStringBaseBasis a c η hc θ hχ d W i :=
  Module.Basis.ofSpan_subset (homogeneousStringBases_span a c η hc θ hχ d W) (Set.mem_range_self i)

noncomputable def stringBaseDegree (i : StringBaseIndex a c η hc θ hχ d W) : ℤ :=
  (homogeneousStringBaseBasis_exists_degree a c η hc θ hχ d W i).choose

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPrimitiveGeneration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

def convPreservesWeight (f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ)) : Prop :=
  ∀ k (x : unitalComponent a c η hc θ k),
    f.ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x) ∈ globalHomogeneous a c η hc θ k

lemma convPreservesWeight_one : convPreservesWeight a c η hc θ 1 := by
  intro k x
  change algebraMap ℚ (UnitalShuffle a c η hc θ)
    (globalCounit a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)) ∈ _
  by_cases hk : k=0
  · subst k
    rw [Algebra.algebraMap_eq_smul_one]
    apply Submodule.smul_mem
    exact ⟨unitalGradeOne a c η hc θ,rfl⟩
  · rw [globalCounit_lof_ne a c η hc θ k hk,map_zero]
    exact Submodule.zero_mem _

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma convPreservesWeight_id : convPreservesWeight a c η hc θ (toConv LinearMap.id) :=
  fun _ x=>⟨x,rfl⟩

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma convPreservesWeight_sub
    {f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ)}
    (hf : convPreservesWeight a c η hc θ f) (hg : convPreservesWeight a c η hc θ g) :
    convPreservesWeight a c η hc θ (f-g) :=
  fun k x=>(globalHomogeneous a c η hc θ k).sub_mem (hf k x) (hg k x)

lemma globalTensorGrade_map_homogeneous (d e : slopeDimensions c η hc θ) (W : ℤ)
    (f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ))
    (hf : convPreservesWeight a c η hc θ f) (hg : convPreservesWeight a c η hc θ g)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    LinearMap.mul' ℚ (UnitalShuffle a c η hc θ)
      (TensorProduct.map f.ofConv g.ofConv (globalTensorGradeInclusion a c η hc θ d e W x)) ∈
        globalHomogeneous a c η hc θ (d+e,W) := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simpa only [map_zero] using (globalHomogeneous a c η hc θ (d+e,W)).zero_mem
  | ha x y hx hy => simpa only [map_add] using (globalHomogeneous a c η hc θ (d+e,W)).add_mem hx hy
  | ht u x y =>
    rw [globalTensorGradeInclusion_part,TensorProduct.map_tmul,LinearMap.mul'_apply]
    have h := globalHomogeneous_mul a c η hc θ (hf (d,u) x) (hg (e,W-u) y)
    have heq : (d,u)+(e,W-u)=(d+e,W) := by ext <;> simp
    rwa [heq] at h

lemma convPreservesWeight_mul
    {f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ)}
    (hf : convPreservesWeight a c η hc θ f) (hg : convPreservesWeight a c η hc θ g) :
    convPreservesWeight a c η hc θ (f*g) := by
  intro k x
  rw [LinearMap.convMul_apply]
  change LinearMap.mul' ℚ (UnitalShuffle a c η hc θ) (TensorProduct.map f.ofConv g.ofConv
    (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))) ∈ _
  rw [globalCoproduct_lof]
  simp only [map_sum]
  apply Submodule.sum_mem
  intro s hs
  have h := globalTensorGrade_map_homogeneous a c η hc θ
    ⟨left s.val,s.property.1⟩ ⟨right s.val,s.property.2⟩ k.2 f g hf hg
    (unitalGradeCoproduct a c η hc θ (left s.val) (right s.val)
      (s.property.1.compatible s.property.2) k.2
      (unitalGradeCast a c η hc θ (left_add_right s.val).symm rfl x))
  have heq : (⟨left s.val,s.property.1⟩+⟨right s.val,s.property.2⟩ : slopeDimensions c η hc θ)=k.1 :=
    Subtype.ext (left_add_right s.val)
  rw [heq] at h
  exact h

lemma convPreservesWeight_pow
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ)}
    (hf : convPreservesWeight a c η hc θ f) (n : ℕ) :
    convPreservesWeight a c η hc θ (f^n) := by
  induction n with
  | zero => exact convPreservesWeight_one a c η hc θ
  | succ n ih => rw [pow_succ]; exact convPreservesWeight_mul a c η hc θ ih hf

lemma globalPrimitiveLog_homogeneous :
    convPreservesWeight a c η hc θ (toConv (globalPrimitiveLog a c η hc θ)) := by
  intro k x
  change (convSeries a c η hc θ (convolutionJ a c η hc θ) (PowerSeries.log ℚ)).ofConv _ ∈ _
  rw [convSeries_lof]
  apply Submodule.sum_mem
  intro r hr
  exact Submodule.smul_mem _ _ (convPreservesWeight_pow a c η hc θ
    (convPreservesWeight_sub a c η hc θ (convPreservesWeight_id a c η hc θ)
      (convPreservesWeight_one a c η hc θ)) r k x)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_DirectSumSubtype
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open scoped DirectSum
universe u v
variable {K : Type u} [DecidableEq K] (M : K → Type v) [∀ k,AddCommGroup (M k)] [∀ k,Module ℚ (M k)]
  (p : K → Prop)
attribute [local instance] Classical.propDecidable

noncomputable def subfamilyInclusion : (⨁ k : {k // p k},M k.val) →ₗ[ℚ] ⨁ k,M k :=
  DirectSum.toModule ℚ _ _ (fun k=>DirectSum.lof ℚ K M k.val)

lemma subfamilyInclusion_lof (k : {k // p k}) (x : M k.val) :
    subfamilyInclusion M p (DirectSum.lof ℚ _ (fun k : {k // p k}=>M k.val) k x)=
      DirectSum.lof ℚ K M k.val x := by
  simp [subfamilyInclusion]

end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPrimitiveStrings
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable local instance instAddCommGroupSubtypeSourceAssociatedGradeMemSubmoduleRatPrimitiveSpace_1_red2bee_1 (d : I → ℕ) (W : ℤ) : AddCommGroup (primitiveSpace a c η hc θ Fact.out d W) := Submodule.addCommGroup _
noncomputable local instance instModuleRatSubtypeSourceAssociatedGradeMemSubmodulePrimitiveSpace_1 (d : I → ℕ) (W : ℤ) : Module ℚ (primitiveSpace a c η hc θ Fact.out d W) := Submodule.module _

abbrev NonzeroSlopeWeight := {k : SlopeWeight c η hc θ // k.1.val≠0}

abbrev GlobalStringIndex := Σ k : NonzeroSlopeWeight c η hc θ,
  Σ _ : ℕ,StringBaseIndex a c η hc θ Fact.out k.val.1.val k.val.2

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable instance globalStringIndexLinearOrder : LinearOrder (GlobalStringIndex a c η hc θ) :=
  linearOrderOfSTO WellOrderingRel

end ElementaryPositivity.RawShuffle

end

end OAI
end

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

lemma unitalSourceFiltration_component_mem (d : I → ℕ) (W ℓ : ℤ)
    (f : B a (slope c η) d) (hf : f∈unitalSourceFiltration a c η hc θ d W) :
    componentB a (slope c η) d ℓ f∈unitalSourceFiltration a c η hc θ d W := by
  classical
  by_cases hd : d=0
  · by_cases hw : W≤0
    · simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_left hw,Submodule.mem_top]
    · simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_right hw,Submodule.mem_bot] at hf ⊢
      rw [hf,map_zero]
  · rw [unitalSourceFiltration_nonzero a c η hc θ d hd W] at hf ⊢
    exact sourceFiltration_component_mem a c η hc θ d W ℓ f hf

noncomputable def unitalAssociatedComponent (d : I → ℕ) (W ℓ : ℤ) :
    Module.End ℚ (UnitalSourceGrade a c η hc θ d W) :=
  LinearFiltration.map _ _ _ _ (componentB a (slope c η) d ℓ)
    (unitalSourceFiltration_component_mem a c η hc θ d W ℓ)
    (unitalSourceFiltration_component_mem a c η hc θ d (W+1) ℓ)

noncomputable def unitalOriginalHomogeneous (d : I → ℕ) (W ℓ : ℤ) :
    Submodule ℚ (UnitalSourceGrade a c η hc θ d W) :=
  LinearMap.ker (unitalAssociatedComponent a c η hc θ d W ℓ-LinearMap.id)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [hχ : Fact (SlopeEulerSymmetric a c η θ)]

noncomputable def globalOriginalHomogeneous (k : SlopeWeight c η hc θ) (ℓ : ℤ) :
    Submodule ℚ (UnitalShuffle a c η hc θ) :=
  (unitalOriginalHomogeneous a c η hc θ k.1.val k.2 ℓ).map
    (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k)

noncomputable def globalStringPolynomialDegree (i : GlobalStringIndex a c η hc θ) : ℤ :=
  stringBaseDegree a c η hc θ hχ.out i.1.val.1.val i.1.val.2 i.2.2+i.2.1

variable {J : Type*}
noncomputable def wordPolynomialDegree (w : J → SlopeWeight c η hc θ) (p : J → ℤ) : List J → ℤ
  | [] => 0
  | i::l => p i + wordPolynomialDegree w p l-eulerForm a (w i).1.val (wordWeight c η hc θ w l).1.val

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalHilbertGrading
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

abbrev StringPBWIndex := PBWWord a c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val)

noncomputable def stringPBWGrade (l : StringPBWIndex a c η hc θ) : SlopeWeight c η hc θ × ℤ :=
  (wordWeight c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val) l.val,
   wordPolynomialDegree a c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val)
     (globalStringPolynomialDegree a c η hc θ) l.val)

abbrev StringPBWGradedIndex (k : SlopeWeight c η hc θ) (m : ℤ) :=
  {l : StringPBWIndex a c η hc θ // stringPBWGrade a c η hc θ l=(k,m)}

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PrimitiveStringBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

abbrev SlopeStringCoefficient (d : I → ℕ) (hs : slope c η d=θ) (k : ℤ) :=
  Σ W : ℤ,StringPBWGradedIndex a c η hc θ (⟨d,Or.inr hs⟩,W) k

end ElementaryPositivity.RawShuffle

end

end OAI
end


