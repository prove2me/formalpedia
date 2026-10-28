-- Prove2me | Definitions.Def_OAIQ068A007
-- name    : OAIQ068A007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:40:10.590997+00:00
-- url     : https://prove2.me/theorems/da1c4432-b7d4-48e8-9957-862fa596f9da
-- title:
--   Definitions bundle OAIQ068A007 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 146 declarations of OpenAI's Lean: 70 definitions, 7 instances and 69 theorems. The definitions and types are `OAI.PiExponent.CurveContactFamily.fibre`, `OAI.PiExponent.CurveCycle.componentLocalCutLength`, `OAI.PiExponent.CurveCycle.componentLocalPrime`, `OAI.PiExponent.CurveCycle.componentMultiplicity`, `OAI.PiExponent.CurveCycle.cutQuotientEquivOfSurjective`, `OAI.PiExponent.CurveCycle.genericPointsEmbeddingEquiv`, `OAI.PiExponent.CurveCycle.genericPointsThroughEquiv`, `OAI.PiExponent.CurveCycle.localMinimalPrimeGenericStalkIso`, `OAI.PiExponent.CurveCycle.minimalPrimesGenericEquiv`, `OAI.PiExponent.CurveCycle.reducedComponent`, `OAI.PiExponent.CurveCycle.reducedComponentStalkPrime`, `OAI.PiExponent.CurveCycle.reducedComponentι`, `OAI.PiExponent.CurveCycle.stalkLength`, `OAI.PiExponent.CurveCycle.stalkMinimalPrimesEquivComponentsThrough`, `OAI.PiExponent.CurveFieldRigidity.coordinateKernel`, `OAI.PiExponent.CurveGeometricFunctionField.coordinates`, `OAI.PiExponent.CurveGeometricFunctionField.intrinsicFunctionFieldAlgebra`, `OAI.PiExponent.CurveGeometricFunctionField.intrinsicSectionAlgebra`, `OAI.PiExponent.CurveImageAffineCoordinates.presentation`, `OAI.PiExponent.CurveNormalizationMorphism.structureFieldAlgebra`, `OAI.PiExponent.CurveZeroPole.fiberDegree`, `OAI.PiExponent.DerivativeIdeals.derivativeCore`, `OAI.PiExponent.DerivativeIdeals.derivativeIdeal`, `OAI.PiExponent.DerivativeIdeals.wordCost`, `OAI.PiExponent.DerivativeIdeals.wordDerivative`, `OAI.PiExponent.EventualLowerBound`, `OAI.PiExponent.FormalJetDerivatives.jetFrame`, `OAI.PiExponent.FormalJetDerivatives.jetFrameWord`, `OAI.PiExponent.FormalLogTruncation.shiftEquiv`, `OAI.PiExponent.FormalLogTruncation.shiftMap`, `OAI.PiExponent.FormalLogTruncation.shiftVars`, `OAI.PiExponent.FrameEquationFamily.BoundedWords`, `OAI.PiExponent.GradedCech.degreeRestriction`, `OAI.PiExponent.GradedCech.restriction`, `OAI.PiExponent.GradedCech.tupleSet`, `OAI.PiExponent.GradedLocalizationExact.degreePiece`, `OAI.PiExponent.GradedLocalizationExact.fraction`, `OAI.PiExponent.GradedLocalizationExact.localizedMap`, `OAI.PiExponent.GradedLocalizationExact.pieceMap`, `OAI.PiExponent.GradedLocalizationExact.powerDenominator` and 30 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_ExceptionalAffineChartRestriction`, `PiExponent_Analysis_FormalLogTruncation`, `PiExponent_Approximation_FrameEquationFamily`, `PiExponent_Approximation_InterpolationMatrix`, `PiExponent_Approximation_MatrixArithmetic`, `PiExponent_Approximation_MatrixCounting`, `PiExponent_Approximation_SectionImageSupport`, `PiExponent_Cohomology_GradedCech`, `PiExponent_Geometry_CurveComponentLocalLengths`, `PiExponent_Geometry_CurveComponentMultiplicity`, `PiExponent_Geometry_CurveComponentStalks`, `PiExponent_Geometry_CurveContact`, `PiExponent_Geometry_CurveContactFamily`, `PiExponent_Geometry_CurveCutQuotient`, `PiExponent_Geometry_CurveCycleLengths`, `PiExponent_Geometry_CurveFieldRigidity`, `PiExponent_Geometry_CurveGeometricFunctionField`, `PiExponent_Geometry_CurveImageAffineCoordinates`, `PiExponent_Geometry_CurveLocalMultiplicity`, `PiExponent_Geometry_CurveNormalizationMorphism`, `PiExponent_Geometry_CurveStalkGluing`, `PiExponent_Geometry_CurveZeroPole`, `PiExponent_Geometry_FromSpecStalkLocalIso`, `PiExponent_Geometry_IntegralCurveExistence`, `PiExponent_Geometry_ReducedComponentStalk`, `PiExponent_Jets_ConormalPairing`, `PiExponent_Jets_DerivativeIdeals`, `PiExponent_Jets_FormalJetDerivatives`, `PiExponent_Jets_NormalBasisRigidity`, `PiExponent_Jets_NormalFrameBasis`, `PiExponent_Jets_PolynomialTangentDifferential`, `PiExponent_Jets_PrimeNormalCotangent`, `PiExponent_Jets_ResidueConormalPairing`, `PiExponent_Jets_TransverseMultiplicity`, `PiExponent_LocalAlgebra_FiniteGlobalPresentation`, `PiExponent_LocalAlgebra_IntegralAffineOpenDimension`, `PiExponent_Polynomials_GradedLocalizationExact`, `PiExponent_Statement`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A017` and `OAIQ068A018`; the statements `OAI_PiExponent_CoordinateSliceComparison_length_eq_sliceFamily_of_normalBasis`, `OAI.PiExponent.CoordinateSliceComparison.length_eq_sliceFamily_of_normalBasis_q68`, `OAI_PiExponent_CoordinateSliceComparison_sliceFamily_mem_minimalPrimes_of_normalBasis`, `OAI.PiExponent.CoordinateSliceComparison.sliceFamily_mem_minimalPrimes_of_normalBasis_q68`, `OAI_PiExponent_CurveFieldRigidity_logarithmic_coordinate_eq_one`, `OAI_PiExponent_CurveInequality_excess_implies_zeroth_eq_one`, `OAI.PiExponent.CurveInequality.excess_implies_zeroth_eq_one_q68`, `OAI_PiExponent_CurveInequality_no_fibre_excess_of_constant_coordinate`, `OAI.PiExponent.CurveInequality.no_fibre_excess_of_constant_coordinate_q68`, `OAI_PiExponent_CurveNormalizationMorphism_exists_intrinsic_normalization_morphism`, `OAI.PiExponent.CurveNormalizationMorphism.exists_intrinsic_normalization_morphism_q68`, `OAI_PiExponent_PrimeWeightedBezout_weighted_prime_length_bound` and `OAI.PiExponent.PrimeWeightedBezout.weighted_prime_length_bound_q68`; the proof of `OAI_PiExponent_CurveInequality_excess_implies_fibre_coordinate_constant`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalAffineChartRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalAffineChart
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

section Functions
variable {A B : Type} [CommRing A] [CommRing B] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (j' : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j']
  (θ : A →+* B) (h : Spec.map (CommRingCat.ofHom θ) ≫ j = j')

include h in
lemma opensRange_le : j'.opensRange ≤ j.opensRange := by
  change Set.range j' ⊆ Set.range j
  rintro y ⟨b,rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom θ) b, ?_⟩
  exact congr($(h) b)

lemma chart_square :
    j'.isoOpensRange.hom ≫ Y.homOfLE (opensRange_le j j' θ h) =
      Spec.map (CommRingCat.ofHom θ) ≫ j.isoOpensRange.hom := by
  apply (cancel_mono j.opensRange.ι).mp
  simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι, h]

lemma topIso_restriction {U V : Y.Opens} (hUV : U ≤ V) (s : Γ(Y,V)) :
    U.topIso.inv (Y.presheaf.map (homOfLE hUV).op s) =
      (Y.homOfLE hUV).appTop (V.topIso.inv s) := by
  change (Y.presheaf.map (homOfLE hUV).op ≫ U.topIso.inv) s =
    (V.topIso.inv ≫ (Y.homOfLE hUV).appTop) s
  congr 1
  simp only [Scheme.Opens.topIso_inv, Scheme.homOfLE_appTop]
  congr 1
  exact (Y.presheaf.map_comp _ _).symm.trans
    ((congrArg (fun g => Y.presheaf.map g) (Subsingleton.elim _ _)).trans
      (Y.presheaf.map_comp _ _))

end Functions

end
end PiExponent.ExceptionalAffineChart

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalJetDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.FormalJetDerivatives
open MvPowerSeries

variable {σ R : Type*} [CommRing R]

def jetFrame (m : ℕ) (i : Fin (m + 1)) :
    Derivation R (MvPowerSeries (Fin (m + 1)) R) (MvPowerSeries (Fin (m + 1)) R) :=
  if i = 0 then (1 + X (0 : Fin (m + 1)) : MvPowerSeries (Fin (m+1)) R) • pderiv R 0 else pderiv R i

@[simp] theorem jetFrame_zero (m : ℕ) (f : MvPowerSeries (Fin (m + 1)) R) :
    jetFrame m 0 f = (1 + X 0) * pderiv R 0 f := by
  simp [jetFrame, Derivation.smul_apply, smul_eq_mul]

@[simp] theorem jetFrame_pos (m : ℕ) (i : Fin (m + 1)) (hi : i ≠ 0)
    (f : MvPowerSeries (Fin (m + 1)) R) : jetFrame m i f = pderiv R i f := by
  simp [jetFrame, hi]

def jetFrameWord (m : ℕ) (word : List (Fin (m + 1)))
    (f : MvPowerSeries (Fin (m + 1)) R) : MvPowerSeries (Fin (m + 1)) R :=
  word.foldr (fun i g => jetFrame m i g) f

end PiExponent.FormalJetDerivatives

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_FormalLogTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.FormalLogTruncation

open MvPowerSeries
open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable def shiftVars {m : ℕ} (tail : Fin m → PowerSeries R) :
    Fin (m+1) → MvPowerSeries (Fin (m+1)) R :=
  Fin.cases (X 0) (fun i => X i.succ + (tail i).toMvPowerSeries 0)

theorem shiftVars_hasSubst {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) : HasSubst (shiftVars tail) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  cases i using Fin.cases with
  | zero => simp [shiftVars]
  | succ i =>
      simp only [shiftVars, Fin.cases_succ, map_add, constantCoeff_X,
        PowerSeries.toMvPowerSeries_apply, constantCoeff_rename, zero_add]
      exact ht i

noncomputable def shiftMap {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) :
    MvPowerSeries (Fin (m+1)) R →ₐ[R] MvPowerSeries (Fin (m+1)) R :=
  substAlgHom (shiftVars_hasSubst tail ht)

@[simp] theorem shiftMap_X_zero {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) :
    shiftMap tail ht (X 0) = X 0 := by
  rw [shiftMap, substAlgHom_X]
  rfl

@[simp] theorem shiftMap_X_succ {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (i : Fin m) :
    shiftMap tail ht (X i.succ) = X i.succ + (tail i).toMvPowerSeries 0 := by
  rw [shiftMap, substAlgHom_X]
  rfl

@[simp] theorem shiftMap_toMvPowerSeries {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f : PowerSeries R) :
    shiftMap tail ht (f.toMvPowerSeries (0 : Fin (m+1))) = f.toMvPowerSeries 0 := by
  rw [shiftMap, substAlgHom_apply, PowerSeries.subst_toMvPowerSeries (shiftVars_hasSubst tail ht)]
  change PowerSeries.subst (X (0 : Fin (m+1))) f = f.toMvPowerSeries 0
  exact PowerSeries.toMvPowerSeries_eq_subst.symm

@[simp] theorem shiftMap_apply {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f) :
    shiftMap tail ht f = subst (shiftVars tail) f := substAlgHom_apply _ _

theorem shiftMap_inverse {m : ℕ} (s t : Fin m → PowerSeries R)
    (hs : ∀ i, PowerSeries.constantCoeff (s i) = 0)
    (ht : ∀ i, PowerSeries.constantCoeff (t i) = 0)
    (hst : ∀ i, s i + t i = 0) (f : MvPowerSeries (Fin (m+1)) R) :
    shiftMap s hs (shiftMap t ht f) = f := by
  simp only [shiftMap_apply]
  rw [subst_comp_subst_apply (shiftVars_hasSubst t ht) (shiftVars_hasSubst s hs)]
  have hvars : (fun i => subst (shiftVars s) (shiftVars t i)) = X := by
    funext i
    rw [← shiftMap_apply s hs]
    cases i using Fin.cases with
    | zero => exact shiftMap_X_zero s hs
    | succ i =>
      change shiftMap s hs (X i.succ + (t i).toMvPowerSeries 0) = X i.succ
      rw [map_add, shiftMap_X_succ, shiftMap_toMvPowerSeries, add_assoc,
        ← map_add, hst i, map_zero, add_zero]
  rw [hvars]
  exact congrFun subst_self f

noncomputable def shiftEquiv {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) :
    MvPowerSeries (Fin (m+1)) R ≃ₐ[R] MvPowerSeries (Fin (m+1)) R := by
  let hn : ∀ i, PowerSeries.constantCoeff (-tail i) = 0 := by simp [ht]
  refine AlgEquiv.ofAlgHom (shiftMap tail ht) (shiftMap (fun i => -tail i) hn) ?_ ?_
  · apply AlgHom.ext
    intro f
    exact shiftMap_inverse tail (fun i => -tail i) ht hn (fun i => add_neg_cancel _) f
  · apply AlgHom.ext
    intro f
    exact shiftMap_inverse (fun i => -tail i) tail hn ht (fun i => neg_add_cancel _) f

@[simp] theorem shiftEquiv_apply {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f) :
    shiftEquiv tail ht f = shiftMap tail ht f := rfl

@[simp] theorem shiftEquiv_symm_apply {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f) :
    (shiftEquiv tail ht).symm f =
      shiftMap (fun i => -tail i) (by simp [ht]) f := rfl

end PiExponent.FormalLogTruncation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox

noncomputable section

def frameWordCost {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (word : List (Fin (m + 1))) : ℝ := (word.map cost).sum

@[simp] theorem frameWordCost_nil {m : ℕ} (cost : Fin (m + 1) → ℝ) :
    frameWordCost cost [] = 0 := rfl

@[simp] theorem frameWordCost_cons {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) (word : List (Fin (m + 1))) :
    frameWordCost cost (i :: word) = cost i + frameWordCost cost word := rfl

end
end PiExponentApprox

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_FrameEquationFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.FrameEquationFamily

open scoped BigOperators
open PiExponentApprox

abbrev BoundedWords {m : ℕ} (cost : Fin (m + 1) → ℝ) (bound : ℝ) :=
  {word : List (Fin (m + 1)) // frameWordCost cost word ≤ bound}

end PiExponent.FrameEquationFamily

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_InterpolationMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent.InterpolationMatrix

noncomputable def exponentVector {m : ℕ} (a : Fin m → ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm a

@[simp] theorem exponentVector_apply {m : ℕ} (a : Fin m → ℕ) (i : Fin m) :
    exponentVector a i = a i := by
  simp [exponentVector]

noncomputable def truncatedLog (T : ℕ) : Polynomial ℂ :=
  PowerSeries.trunc T (PowerSeries.log ℂ)

@[simp] theorem truncatedLog_coeff (T k : ℕ) :
    (truncatedLog T).coeff k =
      if k < T then
        if k = 0 then 0 else algebraMap ℚ ℂ ((-1 : ℚ) ^ (k + 1) / k)
      else 0 := by
  simp [truncatedLog, PowerSeries.coeff_trunc]

noncomputable def monomialImage {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (Polynomial ℂ) :=
  MvPolynomial.C ((1 + Polynomial.X) ^ h) *
    ∏ i, (MvPolynomial.C (Polynomial.C ((j : ℂ) * r i) + G i) +
      MvPolynomial.X i) ^ a i

noncomputable def entry {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s : ℕ) (b : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) : ℂ :=
  ((monomialImage r G j h a).coeff (exponentVector b)).coeff s

def columnWeights {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases w0 w

noncomputable def rowWeights {m : ℕ} (v0 θ : ℝ) (w : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases v0 (fun i => w i / θ)

end PiExponent.InterpolationMatrix

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_MatrixArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

open scoped BigOperators

namespace MatrixArithmetic

noncomputable def logWeights {m : ℕ} (q : Fin m → ℕ) (i : Fin m) : ℝ :=
  (⌈Real.log (q i)⌉₊ : ℝ)

noncomputable def truncationOrders {m : ℕ} (q : Fin m → ℕ) (F v0 : ℝ) : Fin m → ℕ :=
  fun i => ⌈F * logWeights q i / v0⌉₊

end MatrixArithmetic

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_MatrixCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent.MatrixCounting

noncomputable def rationalLogWeights {m : ℕ} (q : Fin m → ℕ) (i : Fin m) : ℚ :=
  (⌈Real.log (q i)⌉₊ : ℚ)

@[simp] theorem rationalLogWeights_cast {m : ℕ} (q : Fin m → ℕ) (i : Fin m) :
    (rationalLogWeights q i : ℝ) = MatrixArithmetic.logWeights q i := by
  simp [rationalLogWeights, MatrixArithmetic.logWeights]

end PiExponent.MatrixCounting

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_FiniteGlobalPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.FiniteGlobalPresentation
noncomputable section
universe u v₁ v₂ u₁ u₂
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

section PresentationMap
variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S : Sheaf J' RingCat.{u}} [HasSheafify J' AddCommGrpCat.{u}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

instance presentation_map_isFinite (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u,u} F]
    (η : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R)) :
    (P.map F η).IsFinite where
  isFiniteType_generators := ⟨by
    rw [SheafOfModules.Presentation.map_generators_I]
    infer_instance⟩
  isFiniteType_relations := ⟨by
    rw [SheafOfModules.Presentation.map_relations_I]
    infer_instance⟩

end PresentationMap

end
end PiExponent.FiniteGlobalPresentation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SectionImageSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.SectionImageSupport
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X : Scheme.{0}} {M : X.Modules}

lemma preimage_basicOpen_topIso_hom (U : X.Opens) (a : Γ(U.toScheme,⊤)) :
    U.ι ⁻¹ᵁ X.basicOpen (U.topIso.hom a) = U.toScheme.basicOpen a := by
  rw [← U.ι_image_basicOpen_topIso_inv (U.topIso.hom a), U.ι.preimage_image_eq]
  rw [Iso.hom_inv_id_apply]

end
end PiExponent.SectionImageSupport

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_GradedLocalizationExact
attribute [-instance] _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedLocalizationExact

noncomputable section

variable {R M N P σR σM σN σP : Type*}
  [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  [SetLike σN N] [AddSubgroupClass σN N]
  [SetLike σP P] [AddSubgroupClass σP P]

def powerDenominator (a : R) (n : ℕ) : Submonoid.powers a :=
  ⟨a ^ n, ⟨n, rfl⟩⟩

@[simp] theorem powerDenominator_val (a : R) (n : ℕ) :
    (powerDenominator a n : R) = a ^ n := rfl

@[simp] theorem powerDenominator_zero (a : R) : powerDenominator a 0 = 1 := by
  apply Subtype.ext
  simp [powerDenominator]

theorem powerDenominator_add (a : R) (n k : ℕ) :
    powerDenominator a (n + k) = powerDenominator a n * powerDenominator a k := by
  apply Subtype.ext
  exact pow_add a n k

def fraction (a : R) (m : M) (n : ℕ) : LocalizedModule (Submonoid.powers a) M :=
  LocalizedModule.mk m (powerDenominator a n)

@[simp] theorem fraction_zero (a : R) (n : ℕ) : fraction a (0 : M) n = 0 :=
  LocalizedModule.zero_mk _

@[simp] theorem fraction_neg (a : R) (m : M) (n : ℕ) :
    fraction a (-m) n = -fraction a m n := LocalizedModule.mk_neg

theorem fraction_add (a : R) (m m' : M) (n k : ℕ) :
    fraction a m n + fraction a m' k =
      fraction a (a ^ k • m + a ^ n • m') (n + k) := by
  simp only [fraction, powerDenominator_add, LocalizedModule.mk_add_mk,
    Submonoid.smul_def, powerDenominator_val]

variable (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
  (a : R) (e : ℤ) (ha : a ∈ 𝒜 e)

omit [AddSubgroupClass σM M] in
include ha in
theorem power_smul_mem {d : ℤ} {m : M} (hm : m ∈ 𝓜 d) (n : ℕ) :
    a ^ n • m ∈ 𝓜 (d + (n : ℤ) * e) := by
  have h := SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded n ha) hm
  simpa only [nsmul_eq_mul, vadd_eq_add, add_comm] using h

def degreePiece (d : ℤ) : AddSubgroup (LocalizedModule (Submonoid.powers a) M) where
  carrier := {z | ∃ (n : ℕ) (m : M), m ∈ 𝓜 (d + (n : ℤ) * e) ∧ z = fraction a m n}
  zero_mem' := ⟨0, 0, zero_mem _, (fraction_zero a 0).symm⟩
  add_mem' := by
    rintro z z' ⟨n, m, hm, rfl⟩ ⟨k, m', hm', rfl⟩
    refine ⟨n + k, a ^ k • m + a ^ n • m', ?_, fraction_add a m m' n k⟩
    apply add_mem
    · have h := power_smul_mem 𝒜 𝓜 a e ha hm k
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      push_cast
      ring_nf
    · have h := power_smul_mem 𝒜 𝓜 a e ha hm' n
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      push_cast
      ring_nf
  neg_mem' := by
    rintro z ⟨n, m, hm, rfl⟩
    exact ⟨n, -m, neg_mem hm, (fraction_neg a m n).symm⟩

@[simp] theorem mem_degreePiece (d : ℤ) (z : LocalizedModule (Submonoid.powers a) M) :
    z ∈ degreePiece 𝒜 𝓜 a e ha d ↔
      ∃ (n : ℕ) (m : M), m ∈ 𝓜 (d + (n : ℤ) * e) ∧ z = fraction a m n := Iff.rfl

def localizedMap (f : M →ₗ[R] N) :
    LocalizedModule (Submonoid.powers a) M →ₗ[R] LocalizedModule (Submonoid.powers a) N :=
  IsLocalizedModule.map (Submonoid.powers a) (LocalizedModule.mkLinearMap _ M)
    (LocalizedModule.mkLinearMap _ N) f

@[simp] theorem localizedMap_fraction (f : M →ₗ[R] N) (m : M) (n : ℕ) :
    localizedMap a f (fraction a m n) = fraction a (f m) n :=
  IsLocalizedModule.map_LocalizedModules _ f m _

variable (𝓝 : ℤ → σN) [SetLike.GradedSMul 𝒜 𝓝]

def pieceMap (d : ℤ) (f : M →ₗ[R] N)
    (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 i) :
    degreePiece 𝒜 𝓜 a e ha d →+ degreePiece 𝒜 𝓝 a e ha d where
  toFun z := ⟨localizedMap a f z.val, by
    obtain ⟨n, m, hm, hz⟩ := z.property
    refine ⟨n, f m, hf _ _ hm, ?_⟩
    rw [hz, localizedMap_fraction]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' z z' := Subtype.ext (map_add _ _ _)

@[simp] theorem pieceMap_coe (d : ℤ) (f : M →ₗ[R] N)
    (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 i)
    (z : degreePiece 𝒜 𝓜 a e ha d) :
    (pieceMap 𝒜 𝓜 a e ha 𝓝 d f hf z).val = localizedMap a f z.val := rfl

end
end PiExponent.GradedLocalizationExact

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedCech
attribute [-instance] _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedCech
noncomputable section
open scoped BigOperators
open GradedLocalizationExact

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem divisor_isUnit (a c : R) (hac : a ∣ c) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule (Submonoid.powers c) M)) a) := by
  obtain ⟨b, rfl⟩ := hac
  have h := IsLocalizedModule.Away.isUnit_algebraMap
    (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M) (a * b)
  rw [map_mul] at h
  exact (((Commute.all a b).map (algebraMap R
    (Module.End R (LocalizedModule (Submonoid.powers (a * b)) M)))).isUnit_mul_iff.mp h).1

theorem divisor_powers_isUnit (a c : R) (hac : a ∣ c) (s : Submonoid.powers a) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule (Submonoid.powers c) M)) s) := by
  obtain ⟨n, hn⟩ := s.property
  rw [← hn, map_pow]
  exact (divisor_isUnit (M := M) a c hac).pow n

def restriction (a c : R) (hac : a ∣ c) :
    LocalizedModule (Submonoid.powers a) M →ₗ[R]
      LocalizedModule (Submonoid.powers c) M :=
  LocalizedModule.lift (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers c) M)
    (divisor_powers_isUnit a c hac)

@[simp] theorem restriction_mk_one (a c : R) (hac : a ∣ c) (m : M) :
    restriction a c hac (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
  exact LocalizedModule.lift_mk_one _ _ _ m

@[simp] theorem restriction_fraction_zero (a c : R) (hac : a ∣ c) (m : M) :
    restriction a c hac (fraction a m 0) = fraction c m 0 := by
  simpa only [fraction, powerDenominator_zero] using restriction_mk_one a c hac m

theorem power_smul_fraction (a : R) (m : M) (n : ℕ) :
    a ^ n • fraction a m n = fraction a m 0 := by
  simp only [fraction, powerDenominator_zero, LocalizedModule.smul'_mk]
  exact LocalizedModule.mk_cancel (powerDenominator a n) m

theorem restriction_fraction (a b : R) (m : M) (n : ℕ) :
    restriction a (a * b) (dvd_mul_right a b) (fraction a m n) =
      fraction (a * b) (b ^ n • m) n := by
  have hu := (divisor_isUnit (M := M) a (a * b) (dvd_mul_right a b)).pow n
  rw [← map_pow] at hu
  apply ((Module.End.isUnit_iff _).mp hu).injective
  change a ^ n • restriction a (a * b) (dvd_mul_right a b) (fraction a m n) =
    a ^ n • fraction (a * b) (b ^ n • m) n
  rw [← map_smul, power_smul_fraction, restriction_fraction_zero]
  change fraction (a * b) m 0 =
    a ^ n • LocalizedModule.mk (b ^ n • m) (powerDenominator (a * b) n)
  rw [LocalizedModule.smul'_mk, smul_smul, ← mul_pow]
  simpa only [fraction, LocalizedModule.smul'_mk] using
    (power_smul_fraction (a * b) m n).symm

variable {σR σM : Type*} [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

def degreeRestriction (a c : R) (ea ec : ℤ)
    (ha : a ∈ 𝒜 ea) (hc : c ∈ 𝒜 ec)
    (hfactor : ∃ b : R, b ∈ 𝒜 (ec - ea) ∧ c = a * b) (d : ℤ) :
    degreePiece 𝒜 𝓜 a ea ha d →+ degreePiece 𝒜 𝓜 c ec hc d where
  toFun z := ⟨restriction a c (by obtain ⟨b, _, hb⟩ := hfactor; exact ⟨b, hb⟩) z.val, by
    obtain ⟨n, m, hm, hz⟩ := z.property
    obtain ⟨b, hb, rfl⟩ := hfactor
    refine ⟨n, b ^ n • m, ?_, ?_⟩
    · have h := power_smul_mem 𝒜 𝓜 b (ec - ea) hb hm n
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      ring_nf
    · rw [hz]
      exact restriction_fraction a b m n⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' z z' := Subtype.ext (map_add _ _ _)

@[simp] theorem degreeRestriction_coe (a c : R) (ea ec : ℤ)
    (ha : a ∈ 𝒜 ea) (hc : c ∈ 𝒜 ec)
    (hfactor : ∃ b : R, b ∈ 𝒜 (ec - ea) ∧ c = a * b) (d : ℤ)
    (z : degreePiece 𝒜 𝓜 a ea ha d) :
    (degreeRestriction 𝒜 𝓜 a c ea ec ha hc hfactor d z).val =
      restriction a c (by obtain ⟨b, _, hb⟩ := hfactor; exact ⟨b, hb⟩) z.val := rfl

section Cover
variable {J : Type*} [DecidableEq J] (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1)

def tupleSet {n : ℕ} (t : Fin n → J) : Finset J := Finset.univ.image t

theorem tupleSet_comp_subset {m n : ℕ} (t : Fin n → J) (f : Fin m → Fin n) :
    tupleSet (t ∘ f) ⊆ tupleSet t := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_image.mpr ⟨f i, Finset.mem_univ _, rfl⟩

end Cover

end
end PiExponent.GradedCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_IntegralCurveExistence
attribute [-instance] _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Order

namespace PiExponent.NumericalAmpleness

noncomputable section

theorem isReduced_vanishingIdeal_subscheme {X : Scheme} (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  apply (IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover).mpr
  intro U
  change X.affineOpens at U
  change IsReduced (Spec (CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U)))
  have hI : (I.ideal U).IsRadical := by
    simpa only [I, Scheme.IdealSheafData.vanishingIdeal_ideal] using
      PrimeSpectrum.isRadical_vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X))
  have : _root_.IsReduced (Γ(X, U.1) ⧸ I.ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp hI
  infer_instance

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveComponentMultiplicity
attribute [-instance] _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

def componentMultiplicity (X : Scheme.{0}) (C : irreducibleComponents X) : ℕ :=
  (Module.length (X.presheaf.stalk (genericPoints.ofComponent C).val)
    (X.presheaf.stalk (genericPoints.ofComponent C).val)).toNat

def reducedComponent (X : Scheme.{0}) (C : irreducibleComponents X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)).subscheme

def reducedComponentι (X : Scheme.{0}) (C : irreducibleComponents X) :
    reducedComponent X C ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)).subschemeι

instance reducedComponent_closed (X : Scheme.{0}) (C : irreducibleComponents X) :
    IsClosedImmersion (reducedComponentι X C) := by
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)
  change IsClosedImmersion I.subschemeι
  infer_instance

instance reducedComponent_integral (X : Scheme.{0}) (C : irreducibleComponents X) :
    IsIntegral (reducedComponent X C) := by
  let Z : Closeds X := ⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hI : (I.support : Set X) = C.val := by
    simp only [I,Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let : IsReduced I.subscheme := NumericalAmpleness.isReduced_vanishingIdeal_subscheme Z
  let : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    rw [hI]
    exact Subtype.irreducibleSpace C.property.1
  change IsIntegral I.subscheme
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveComponentStalks
attribute [-instance] _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

theorem generic_iff_no_proper_generalization {T : Type*} [TopologicalSpace T] [QuasiSober T]
    (x : T) : x ∈ genericPoints T ↔ ∀ y : T, y ⤳ x → x ⤳ y := by
  constructor
  · intro hx y hy
    apply specializes_iff_closure_subset.mpr
    exact hx.2 isIrreducible_singleton.closure hy.closure_subset
  · intro hx
    let C : irreducibleComponents T :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    let y := (genericPoints.ofComponent C).val
    have hy : y ⤳ x := (genericPoints.isGenericPoint_ofComponent C).specializes
      mem_irreducibleComponent
    have he : closure ({x} : Set T) = C.val := by
      apply Set.Subset.antisymm
      · exact closure_minimal (Set.singleton_subset_iff.mpr mem_irreducibleComponent)
          (isClosed_of_mem_irreducibleComponents C.val C.property)
      · rw [← (genericPoints.isGenericPoint_ofComponent C).def]
        exact (hx y hy).closure_subset
    change closure ({x} : Set T) ∈ irreducibleComponents T
    rw [he]
    exact C.property

theorem generic_embedding_iff {T S : Type*} [TopologicalSpace T] [QuasiSober T]
    [TopologicalSpace S] [QuasiSober S] {f : S → T} (hf : IsEmbedding f)
    (hstable : ∀ y : S, ∀ x : T, x ⤳ f y → x ∈ Set.range f) (y : S) :
    y ∈ genericPoints S ↔ f y ∈ genericPoints T := by
  rw [generic_iff_no_proper_generalization, generic_iff_no_proper_generalization]
  constructor
  · intro hy x hx
    obtain ⟨z,rfl⟩ := hstable y x hx
    exact (hy z (hf.isInducing.specializes_iff.mp hx)).map hf.continuous
  · intro hy z hz
    exact hf.isInducing.specializes_iff.mp (hy (f z) (hz.map hf.continuous))

def genericPointsEmbeddingEquiv {T S : Type*} [TopologicalSpace T] [QuasiSober T]
    [TopologicalSpace S] [QuasiSober S] {f : S → T} (hf : IsEmbedding f)
    (hstable : ∀ y : S, ∀ x : T, x ⤳ f y → x ∈ Set.range f) :
    genericPoints S ≃ {x : genericPoints T // x.val ∈ Set.range f} := by
  let g : genericPoints S → {x : genericPoints T // x.val ∈ Set.range f} := fun y =>
    ⟨⟨f y.val, (generic_embedding_iff hf hstable y.val).mp y.property⟩, ⟨y.val,rfl⟩⟩
  apply Equiv.ofBijective g
  constructor
  · intro x y h
    exact Subtype.ext (hf.injective (congrArg (fun z => z.val.val) h))
  · intro x
    obtain ⟨y,hy⟩ := x.property
    have hgen : y ∈ genericPoints S :=
      (generic_embedding_iff hf hstable y).mpr (hy ▸ x.val.property)
    exact ⟨⟨y,hgen⟩, Subtype.ext (Subtype.ext hy)⟩

def minimalPrimesGenericEquiv (A : CommRingCat) :
    minimalPrimes A ≃ genericPoints (Spec A) where
  toFun P := ⟨⟨P.val,P.property.1.1⟩, by
    change closure ({⟨P.val,P.property.1.1⟩} : Set (PrimeSpectrum A)) ∈
      irreducibleComponents (PrimeSpectrum A)
    rw [← PrimeSpectrum.vanishingIdeal_mem_minimalPrimes,
      PrimeSpectrum.vanishingIdeal_singleton]
    exact P.property⟩
  invFun y := ⟨y.val.asIdeal, by
    rw [← PrimeSpectrum.vanishingIdeal_singleton y.val]
    exact PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mpr y.property⟩
  left_inv P := rfl
  right_inv y := by rfl

theorem fromSpecStalk_generizing (X : Scheme.{0}) (x : X)
    (y : Spec (X.presheaf.stalk x)) (z : X) (hz : z ⤳ X.fromSpecStalk x y) :
    z ∈ Set.range (X.fromSpecStalk x) := by
  rw [Scheme.range_fromSpecStalk]
  have hy : X.fromSpecStalk x y ⤳ x := by
    have hmem : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y,rfl⟩
    rw [Scheme.range_fromSpecStalk] at hmem
    exact hmem
  exact hz.trans hy

def genericPointsThroughEquiv (X : Scheme.{0}) (x : X) :
    {y : genericPoints X // y.val ∈ Set.range (X.fromSpecStalk x)} ≃
      {C : irreducibleComponents X // x ∈ C.val} where
  toFun y := ⟨genericPoints.component y.val, by
    have hmem : y.val.val ⤳ x :=
      (congrArg (fun S : Set X => y.val.val ∈ S)
        (Scheme.range_fromSpecStalk (X := X) (x := x))).mp y.property
    exact hmem.mem_closure⟩
  invFun C := ⟨genericPoints.ofComponent C.val, by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoints.isGenericPoint_ofComponent C.val).specializes C.property⟩
  left_inv y := by
    apply Subtype.ext
    exact genericPoints.ofComponent_component y.val
  right_inv C := by
    apply Subtype.ext
    exact genericPoints.component_ofComponent C.val

def stalkMinimalPrimesEquivComponentsThrough (X : Scheme.{0}) (x : X) :
    minimalPrimes (X.presheaf.stalk x) ≃
      {C : irreducibleComponents X // x ∈ C.val} :=
  (minimalPrimesGenericEquiv (X.presheaf.stalk x)).trans
    ((genericPointsEmbeddingEquiv (X.fromSpecStalk x).isEmbedding
      (fromSpecStalk_generizing X x)).trans (genericPointsThroughEquiv X x))

theorem stalkMinimalPrimesEquivComponentsThrough_point (X : Scheme.{0}) (x : X)
    (P : minimalPrimes (X.presheaf.stalk x)) :
    X.fromSpecStalk x (⟨P.val,P.property.1.1⟩ : Spec (X.presheaf.stalk x)) =
      (genericPoints.ofComponent
        (stalkMinimalPrimesEquivComponentsThrough X x P).val).val := by
  symm
  exact congrArg Subtype.val (genericPoints.ofComponent_component
    ((genericPointsEmbeddingEquiv (X.fromSpecStalk x).isEmbedding
      (fromSpecStalk_generizing X x))
        (minimalPrimesGenericEquiv (X.presheaf.stalk x) P)).val)

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_FromSpecStalkLocalIso
attribute [-instance] _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace PiExponent

universe u

theorem specMap_stalkMap_isIso_of_isLocalization
    (R S : CommRingCat.{u}) [Algebra R S] (M : Submonoid R)
    [IsLocalization M S] (y : Spec S) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap y) := by
  let e := IsLocalization.algEquiv M (Localization M) S
  have he : IsIso (CommRingCat.ofHom e.toRingHom) :=
    inferInstanceAs (IsIso e.toRingEquiv.toCommRingCatIso.hom)
  have hmap : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := inferInstance
  have hstalk : IsIso ((Spec.map (CommRingCat.ofHom e.toRingHom)).stalkMap y) :=
    inferInstance
  have h : Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization M))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact e.toAlgHom.comp_algebraMap.symm
  rw [h, Scheme.Hom.stalkMap_comp]
  have hloc : IsIso ((Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization M)))).stalkMap
        (Spec.map (CommRingCat.ofHom e.toRingHom) y)) :=
    isIso_SpecMap_stakMap_localization R M _
  exact (asIso ((Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization M)))).stalkMap
        (Spec.map (CommRingCat.ofHom e.toRingHom) y)) ≪≫
    asIso ((Spec.map (CommRingCat.ofHom e.toRingHom)).stalkMap y)).isIso_hom

instance fromSpecStalk_stalkMap_isIso (X : Scheme.{u}) (x : X)
    (y : Spec (X.presheaf.stalk x)) :
    IsIso ((X.fromSpecStalk x).stalkMap y) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top x)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk,
    Scheme.Hom.stalkMap_comp]
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : IsIso ((Spec.map (X.presheaf.germ U x hxU)).stalkMap y) :=
    specMap_stalkMap_isIso_of_isLocalization Γ(X, U) (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl y
  exact (asIso (hU.fromSpec.stalkMap ((Spec.map (X.presheaf.germ U x hxU)) y)) ≪≫
    asIso ((Spec.map (X.presheaf.germ U x hxU)).stalkMap y)).isIso_hom

def fromSpecStalkStalkIso (X : Scheme.{u}) (x : X)
    (y : Spec (X.presheaf.stalk x)) :
    X.presheaf.stalk (X.fromSpecStalk x y) ≅
      (Spec (X.presheaf.stalk x)).presheaf.stalk y :=
  asIso ((X.fromSpecStalk x).stalkMap y)

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveLocalMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

def localMinimalPrimeGenericStalkIso (X : Scheme.{0}) (x : X)
    (P : minimalPrimes (X.presheaf.stalk x)) :
    letI : P.val.IsPrime := P.property.1.1
    X.presheaf.stalk (genericPoints.ofComponent
      (stalkMinimalPrimesEquivComponentsThrough X x P).val).val ≅
      CommRingCat.of (Localization.AtPrime P.val) := by
  let y : Spec (X.presheaf.stalk x) := ⟨P.val,P.property.1.1⟩
  let e := (PiExponent.fromSpecStalkStalkIso X x y) ≪≫
    (Spec.stalkIso (X.presheaf.stalk x) y)
  simpa only [y,stalkMinimalPrimesEquivComponentsThrough_point] using e

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveComponentLocalLengths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

instance finite_componentsThrough {X : Scheme.{0}} [IsLocallyNoetherian X] (x : X) :
    Finite {C : irreducibleComponents X // x ∈ C.val} := by
  let : Finite (minimalPrimes (X.presheaf.stalk x)) :=
    ((⊥ : Ideal (X.presheaf.stalk x)).finite_minimalPrimes_of_isNoetherianRing _).to_subtype
  exact Finite.of_equiv _ (stalkMinimalPrimesEquivComponentsThrough X x)

def componentLocalPrime (X : Scheme.{0}) (x : X)
    (C : {C : irreducibleComponents X // x ∈ C.val}) :
    Ideal (X.presheaf.stalk x) :=
  ((stalkMinimalPrimesEquivComponentsThrough X x).symm C).val

def componentLocalCutLength (X : Scheme.{0}) (x : X)
    (C : {C : irreducibleComponents X // x ∈ C.val})
    (c : X.presheaf.stalk x) : ℕ∞ :=
  Module.length (X.presheaf.stalk x)
    ((X.presheaf.stalk x) ⧸ (componentLocalPrime X x C ⊔ Ideal.span {c}))

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveZeroPole
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Polynomial nonZeroDivisors

namespace PiExponent.CurveZeroPole

def fiberDegree {R : Type*} [CommRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Algebra.QuasiFinite R S] (p : Ideal R) : ℕ :=
  let := (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) p).fintype
  ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R

theorem baseParameter_nonzero (F S E : Type*) [Field F] [CommRing S] [IsDomain S]
    [Field E] [Algebra F[X] S] [FaithfulSMul F[X] S]
    [Algebra S E] [IsFractionRing S E] [Algebra F[X] E] [IsScalarTower F[X] S E] :
    algebraMap F[X] E Polynomial.X ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply F[X] S E]
  exact (map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective F[X] S)).mpr Polynomial.X_ne_zero)

end PiExponent.CurveZeroPole

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_DerivativeIdeals
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.DerivativeIdeals

variable {C R ι : Type*} [CommRing C] [CommRing R] [Algebra C R]

def wordDerivative (D : ι → Derivation C R R) (word : List ι) (f : R) : R :=
  word.foldr (fun i g => D i g) f

@[simp] theorem wordDerivative_nil (D : ι → Derivation C R R) (f : R) :
    wordDerivative D [] f = f := rfl

@[simp] theorem wordDerivative_cons (D : ι → Derivation C R R) (i : ι)
    (word : List ι) (f : R) : wordDerivative D (i :: word) f = D i (wordDerivative D word f) := rfl

def wordCost (cost : ι → ℝ) (word : List ι) : ℝ := (word.map cost).sum

@[simp] theorem wordCost_nil (cost : ι → ℝ) : wordCost cost [] = 0 := rfl
@[simp] theorem wordCost_cons (cost : ι → ℝ) (i : ι) (word : List ι) :
    wordCost cost (i :: word) = cost i + wordCost cost word := rfl

def derivativeIdeal (D : ι → Derivation C R R) (cost : ι → ℝ) (bound : ℝ) (f : R) :
    Ideal R := Ideal.span {g | ∃ word, wordCost cost word ≤ bound ∧ wordDerivative D word f = g}

def derivativeCore (D : Derivation C R R) (I : Ideal R) : Ideal R where
  carrier := {f | f ∈ I ∧ D f ∈ I}
  zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact ⟨I.zero_mem, I.zero_mem⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨I.add_mem hf.1 hg.1, ?_⟩
    rw [map_add]
    exact I.add_mem hf.2 hg.2
  smul_mem' := by
    intro r f hf
    change r * f ∈ I ∧ D (r * f) ∈ I
    refine ⟨I.mul_mem_left r hf.1, ?_⟩
    rw [Derivation.leibniz]
    exact I.add_mem (I.mul_mem_left r hf.2) (by
      simpa only [smul_eq_mul, mul_comm] using I.mul_mem_left (D r) hf.1)

end PiExponent.DerivativeIdeals
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveContactFamily
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveContactFamily

variable {E : Type*} [Field E] {m K : ℕ}

def fibre (x : Fin m → E) : Fin (m+1) → E := Fin.cases 1 x

@[simp] theorem fibre_zero (x : Fin m → E) : fibre x 0 = 1 := rfl
@[simp] theorem fibre_succ (x : Fin m → E) (i : Fin m) : fibre x i.succ = x i := rfl

end PiExponent.CurveContactFamily
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ReducedComponentStalk
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

theorem reducedComponentι_range (X : Scheme.{0}) (C : irreducibleComponents X) :
    Set.range (reducedComponentι X C) = C.val := by
  let Z : Closeds X := ⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z
  exact I.range_subschemeι.trans (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

theorem reducedComponentι_mem (X : Scheme.{0}) (C : irreducibleComponents X)
    (z : reducedComponent X C) : reducedComponentι X C z ∈ C.val := by
  rw [← reducedComponentι_range]
  exact ⟨z,rfl⟩

def reducedComponentStalkPrime (X : Scheme.{0}) (C : irreducibleComponents X)
    (z : reducedComponent X C) : minimalPrimes (X.presheaf.stalk (reducedComponentι X C z)) :=
  (stalkMinimalPrimesEquivComponentsThrough X (reducedComponentι X C z)).symm
    ⟨C,reducedComponentι_mem X C z⟩

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveCutQuotient
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

def cutQuotientEquivOfSurjective {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (a : A) :
    A ⧸ (RingHom.ker f ⊔ Ideal.span {a}) ≃+* B ⧸ Ideal.span {f a} := by
  let g := (Ideal.Quotient.mk (Ideal.span {f a})).comp f
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hf
  have hk : RingHom.ker g = RingHom.ker f ⊔ Ideal.span {a} := by
    have he : RingHom.ker g = (Ideal.span {f a}).comap f := by
      ext b
      change Ideal.Quotient.mk (Ideal.span {f a}) (f b) = 0 ↔ f b ∈ Ideal.span {f a}
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [he]
    rw [← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_of_surjective f hf]
    rw [← RingHom.ker_eq_comap_bot,sup_comm]
  exact (Ideal.quotEquivOfEq hk.symm).trans (g.quotientKerEquivOfSurjective hg)

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveCycleLengths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

def stalkLength (Y : Scheme.{0}) (y : Y) : ℕ∞ :=
  Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y)

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_NormalBasisRigidity
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.NormalBasisRigidity

open Set Submodule Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

def IsNormalBasis (v : ι → V) (A : Finset ι) : Prop :=
  LinearIndepOn K v (A : Set ι) ∧ span K (v '' (A : Set ι)) = ⊤

end PiExponent.NormalBasisRigidity

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_NormalFrameBasis
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.NormalBasisRigidity
open Module

variable {K : Type*} [Field K] (m : ℕ) (y : K) (hy : y ≠ 0)

def frameEquiv : (Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) → K) where
  toFun c := Fin.cases (y * c 0) (fun i => c i.succ + c 0)
  invFun t := Fin.cases (t 0 / y) (fun i => t i.succ - t 0 / y)
  left_inv c := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hy]
    · simp [hy]
  right_inv t := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change y * (t 0 / y) = t 0
      field_simp
    · simp
  map_add' c d := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [mul_add]
    · simp only [Pi.add_apply, Fin.cases_succ]
      ring
  map_smul' a c := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.smul_apply, Fin.cases_zero, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [mul_add]

def frameBasis : Basis (Fin (m + 1)) K (Fin (m + 1) → K) :=
  (Pi.basisFun K _).map (frameEquiv m y hy)

@[simp] lemma frameBasis_repr_zero (t : Fin (m + 1) → K) :
    (frameBasis m y hy).repr t 0 = t 0 / y := by
  change (Pi.basisFun K _).repr ((frameEquiv m y hy).symm t) 0 = _
  rw [Pi.basisFun_repr]
  rfl

@[simp] lemma frameBasis_repr_succ (t : Fin (m + 1) → K) (i : Fin m) :
    (frameBasis m y hy).repr t i.succ = t i.succ - t 0 / y := by
  change (Pi.basisFun K _).repr ((frameEquiv m y hy).symm t) i.succ = _
  rw [Pi.basisFun_repr]
  rfl

@[simp] lemma frameBasis_succ (i : Fin m) :
    frameBasis m y hy i.succ = Pi.basisFun K _ i.succ := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [frameBasis, frameEquiv, Pi.basisFun_apply]
  · simp [frameBasis, frameEquiv, Pi.basisFun_apply, Pi.single_apply]

@[simp] lemma frameBasis_zero_zero : frameBasis m y hy 0 0 = y := by
  simp [frameBasis, frameEquiv, Pi.basisFun_apply]

@[simp] lemma frameBasis_zero_succ (i : Fin m) : frameBasis m y hy 0 i.succ = 1 := by
  simp [frameBasis, frameEquiv, Pi.basisFun_apply]

end PiExponent.NormalBasisRigidity

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_PolynomialTangentDifferential
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open MvPolynomial KaehlerDifferential

section PolynomialMap
variable {C E ι : Type*} [Field C] [Field E] [Algebra C E] [Fintype ι]

def polynomialJacobian (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) : (ι → E) →ₗ[E] (Q → E) where
  toFun t p := ∑ i, φ (pderiv i p.1) * t i
  map_add' t u := by ext p; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a t := by ext p; simp [Finset.mul_sum, mul_left_comm]

def polynomialTangent (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) : Submodule E (ι → E) :=
  LinearMap.ker (polynomialJacobian φ Q)

end PolynomialMap

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_ConormalPairing
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegel.W58

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable (I : Ideal R) (D : Derivation K R (R ⧸ I))

theorem ideal_smul_quotient_zero (x : I) (z : R ⧸ I) : (x : R) • z = 0 := by
  rw [Algebra.smul_def]
  change Ideal.Quotient.mk I (x : R) * z = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.property, zero_mul]

def normalRestriction : I →ₗ[R] R ⧸ I where
  toFun x := D x
  map_add' x y := D.map_add x y
  map_smul' r x := by
    change D (r * (x : R)) = r • D (x : R)
    rw [D.leibniz, ideal_smul_quotient_zero I x, add_zero]

theorem normalRestriction_product_zero (x y : I) : normalRestriction I D (x * y) = 0 := by
  change D ((x : R) * (y : R)) = 0
  rw [D.leibniz, ideal_smul_quotient_zero I x, ideal_smul_quotient_zero I y, add_zero]

def conormalPairing : I.Cotangent →ₗ[R] R ⧸ I :=
  Ideal.Cotangent.lift (normalRestriction I D) (normalRestriction_product_zero I D)

@[simp] theorem conormalPairing_toCotangent (x : I) :
    conormalPairing I D (I.toCotangent x) = D x := rfl

end PiExponentSiegel.W58

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_ResidueConormalPairing
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegel.W58

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable (I : Ideal R) (D : Derivation K R (R ⧸ I))

instance cotangentQuotientScalarTower : IsScalarTower R (R ⧸ I) I.Cotangent :=
  inferInstance

def residueConormalPairing : I.Cotangent →ₗ[R ⧸ I] R ⧸ I :=
  (conormalPairing I D).extendScalarsOfSurjective
    (show Function.Surjective (algebraMap R (R ⧸ I)) from Ideal.Quotient.mk_surjective)

@[simp] theorem residueConormalPairing_apply (x : I.Cotangent) :
    residueConormalPairing I D x = conormalPairing I D x := rfl

@[simp] theorem residueConormalPairing_toCotangent (x : I) :
    residueConormalPairing I D (I.toCotangent x) = D x := rfl

end PiExponentSiegel.W58

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_PrimeNormalCotangent
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open KaehlerDifferential
open scoped TensorProduct

def extendModuleDerivation
    {C R A E : Type*} [CommRing C] [CommRing R] [CommRing A] [CommRing E]
    [Algebra C R] [Algebra C A] [Algebra C E]
    [Algebra R A] [Algebra R E] [Algebra A E]
    [IsScalarTower C R A] [IsScalarTower C R E] [IsScalarTower C A E]
    [IsScalarTower R A E] [Algebra.FormallyEtale R A]
    (d : Derivation C R E) : Derivation C A E :=
  ((LinearMap.liftBaseChange A d.liftKaehlerDifferential).comp
    (tensorKaehlerEquivOfFormallyEtale C R A).symm.toLinearMap).compDer (D C A)

@[simp]
theorem extendModuleDerivation_algebraMap
    {C R A E : Type*} [CommRing C] [CommRing R] [CommRing A] [CommRing E]
    [Algebra C R] [Algebra C A] [Algebra C E]
    [Algebra R A] [Algebra R E] [Algebra A E]
    [IsScalarTower C R A] [IsScalarTower C R E] [IsScalarTower C A E]
    [IsScalarTower R A E] [Algebra.FormallyEtale R A]
    (d : Derivation C R E) (r : R) :
    extendModuleDerivation (A := A) d (algebraMap R A r) = d r := by
  simp [extendModuleDerivation, LinearMap.compDer,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Derivation.liftKaehlerDifferential_comp_D]

variable {C ι : Type*} [Field C] [Fintype ι]
variable (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]

abbrev PrimeLocalCotangent := IsLocalRing.CotangentSpace (Localization.AtPrime Q)

def primeResidueMap : MvPolynomial ι C →ₐ[C] Q.ResidueField :=
  IsScalarTower.toAlgHom C (MvPolynomial ι C) Q.ResidueField

def primeLocalPartial (i : ι) : Derivation C (Localization.AtPrime Q) Q.ResidueField := by
  let : Algebra.FormallyEtale (MvPolynomial ι C) (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization Q.primeCompl
  exact extendModuleDerivation
    ((Algebra.linearMap (MvPolynomial ι C) Q.ResidueField).compDer (MvPolynomial.pderiv i))

omit [Fintype ι] in
@[simp]
theorem primeLocalPartial_polynomial (i : ι) (p : MvPolynomial ι C) :
    primeLocalPartial Q i (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p) =
      algebraMap (MvPolynomial ι C) Q.ResidueField (MvPolynomial.pderiv i p) := by
  let : Algebra.FormallyEtale (MvPolynomial ι C) (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization Q.primeCompl
  change extendModuleDerivation _ (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p) = _
  rw [extendModuleDerivation_algebraMap]
  rfl

def primePartialNormal (i : ι) : PrimeLocalCotangent Q →ₗ[Q.ResidueField] Q.ResidueField :=
  PiExponentSiegel.W58.residueConormalPairing
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) (primeLocalPartial Q i)

def primeNormalPairing : (ι → Q.ResidueField) →ₗ[Q.ResidueField]
    (PrimeLocalCotangent Q →ₗ[Q.ResidueField] Q.ResidueField) where
  toFun v := ∑ i, v i • primePartialNormal Q i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, smul_smul]

def primePolynomialCotangent (p : Q) : PrimeLocalCotangent Q :=
  (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent
    ⟨algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p.1,
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q p.1).mpr p.2⟩

@[simp]
theorem primeNormalPairing_polynomial (v : ι → Q.ResidueField) (p : Q) :
    primeNormalPairing Q v (primePolynomialCotangent Q p) =
      ∑ i, v i * primeResidueMap Q (MvPolynomial.pderiv i p.1) := by
  change (∑ i, v i • primePartialNormal Q i) (primePolynomialCotangent Q p) = _
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change v i * primeLocalPartial Q i
    (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p.1) = _
  rw [primeLocalPartial_polynomial]
  rfl

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_TransverseMultiplicity
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox.TransverseMultiplicity

noncomputable section

open MvPowerSeries

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

def RectIndex (n : σ → ℕ) := {d : σ →₀ ℕ // ∀ i, d i < n i}

def rectangularPacket (n : σ → ℕ) :
    MvPowerSeries σ K →ₗ[K] (RectIndex n → K) where
  toFun f d := coeff d.val f
  map_add' f g := by ext d; exact map_add _ _ _
  map_smul' a f := by ext d; exact map_smul _ _ _

end
end PiExponentApprox.TransverseMultiplicity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveFieldRigidity
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveFieldRigidity

open scoped BigOperators
open PiExponentApprox

variable {E : Type*} [Field E] [Algebra ℂ E]

def coordinateKernel {n : ℕ} (x : Fin n → E) : Ideal (MvPolynomial (Fin n) ℂ) :=
  RingHom.ker (MvPolynomial.aeval x).toRingHom

instance coordinateKernel_isPrime {n : ℕ} (x : Fin n → E) : (coordinateKernel x).IsPrime :=
  RingHom.ker_isPrime _

@[simp] theorem mem_coordinateKernel {n : ℕ} (x : Fin n → E)
    (p : MvPolynomial (Fin n) ℂ) : p ∈ coordinateKernel x ↔ MvPolynomial.aeval x p = 0 :=
  Iff.rfl

end PiExponent.CurveFieldRigidity
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveGeometricFunctionField
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveGeometricFunctionField

open CategoryTheory AlgebraicGeometry

variable (k A E : Type*) [Field k] [CommRing A] [IsDomain A] [Field E]
  [Algebra k A] [Algebra k E] [Algebra A E] [IsScalarTower k A E]
  [IsFractionRing A E]

def coordinates {ι : Type*} (φ : MvPolynomial ι k →ₐ[k] A) : ι → E :=
  fun i => algebraMap A E (φ (MvPolynomial.X i))

@[instance_reducible] def intrinsicSectionAlgebra (X : Scheme) [IsIntegral X] :
    Algebra Γ(X, ⊤) X.functionField := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  exact (X.germToFunctionField ⊤).hom.toAlgebra

attribute [local instance] intrinsicSectionAlgebra

@[instance_reducible] def intrinsicFunctionFieldAlgebra (k : Type*) [Field k]
    (X : Scheme) [IsIntegral X] [Algebra k Γ(X, ⊤)] :
    Algebra k X.functionField :=
  ((algebraMap Γ(X, ⊤) X.functionField).comp (algebraMap k Γ(X, ⊤))).toAlgebra

end PiExponent.CurveGeometricFunctionField

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IntegralAffineOpenDimension
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.IntegralAffineOpenDimension
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (p : X ⟶ Spec (.of k))

def chartConstants (U : X.affineOpens) : k →+* Γ(X, U.1) :=
  (Spec.preimage (U.2.fromSpec ≫ p)).hom

@[instance_reducible] def chartAlgebra (U : X.affineOpens) : Algebra k Γ(X, U.1) :=
  (chartConstants p U).toAlgebra

end PiExponent.IntegralAffineOpenDimension

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveImageAffineCoordinates
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveImageAffineCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {C X : Scheme.{0}} [IsIntegral C]
variable {ι : Type}

def presentation (p : C ⟶ Spec (.of ℂ)) (U : C.affineOpens)
    (q : Spec Γ(C,U.1) ⟶ Spec (.of (MvPolynomial ι ℂ)))
    (hq : q ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)) =
      U.2.fromSpec ≫ p) :
    letI := IntegralAffineOpenDimension.chartAlgebra p U
    MvPolynomial ι ℂ →ₐ[ℂ] Γ(C,U.1) := by
  letI := IntegralAffineOpenDimension.chartAlgebra p U
  refine ⟨(Spec.preimage q).hom,?_⟩
  intro c
  have h : CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ) ≫
      Spec.preimage q = Spec.preimage (U.2.fromSpec ≫ p) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    exact hq
  exact congrArg (fun φ : CommRingCat.of ℂ ⟶ Γ(C,U.1) => φ c) h

end PiExponent.CurveImageAffineCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveStalkGluing
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace PiExponent.CurveStalkGluing

universe u

variable {X Y S : Scheme.{u}} [IsIntegral X]

@[reassoc]
theorem specMap_stalkFunctionField_fromSpecStalk (x : X) :
    Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ X.fromSpecStalk x =
      X.fromSpecStalk (genericPoint X) := by
  change Spec.map (X.presheaf.stalkSpecializes
    ((genericPoint_spec X).specializes trivial)) ≫ X.fromSpecStalk x = _
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _

theorem genericPoint_mem (U : X.Opens) (x : X) (hx : x ∈ U) :
    genericPoint X ∈ U :=
  (genericPoint_specializes x).mem_open U.isOpen hx

@[reassoc]
theorem specMap_stalkFunctionField_fromSpecStalkOfMem
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        U.fromSpecStalkOfMem x hx =
      U.fromSpecStalkOfMem (genericPoint X) (genericPoint_mem U x hx) := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    specMap_stalkFunctionField_fromSpecStalk]


end PiExponent.CurveStalkGluing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationMorphism
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurveNormalizationMorphism
open AlgebraicGeometry CategoryTheory

@[instance_reducible] def structureFieldAlgebra
    {F : Type u} [Field F] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of F)) : Algebra F X.functionField :=
  (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra

end PiExponent.CurveNormalizationMorphism

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Statement
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

def EventualLowerBound (x : ℝ) : Prop :=
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
    ∀ (p : ℤ) (q : ℕ), Q ≤ q → (q : ℝ) ^ (-ν) ≤ |x - (p : ℝ) / (q : ℝ)|

end PiExponent

end OAI
end


