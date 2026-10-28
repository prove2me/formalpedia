-- Prove2me | Definitions.Def_OAIQ068A008
-- name    : OAIQ068A008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:40:43.548257+00:00
-- url     : https://prove2.me/theorems/b8e8c70b-8511-4002-b5e3-ffdb0d7b5344
-- title:
--   Definitions bundle OAIQ068A008 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 138 declarations of OpenAI's Lean: 67 definitions, 1 inductive type or structure, 8 instances and 62 theorems. The definitions and types are `OAI.PiExponent.FormalMatrixBridge.flatten`, `OAI.PiExponent.FormalMatrixBridge.nestedPolynomialSwap`, `OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation`, `OAI.PiExponent.GeometrySupport.TwistPresentations.schemeUnit`, `OAI.PiExponent.GradedCech.globalPieceMap`, `OAI.PiExponent.GradedH0.PolynomialExponent`, `OAI.PiExponent.GradedPolynomialLaurent.GroupAlgebra`, `OAI.PiExponent.GradedPolynomialLaurent.grading`, `OAI.PiExponent.GradedPolynomialLaurent.moduleRingEquiv`, `OAI.PiExponent.GradedPolynomialLaurent.natExponentHom`, `OAI.PiExponent.GradedPolynomialLaurent.polynomialToGroupAlgebra`, `OAI.PiExponent.GradedPolynomialLaurent.product`, `OAI.PiExponent.GradedPolynomialLaurent.productExponent`, `OAI.PiExponent.GradedPolynomialLaurent.ringLocalizationMap`, `OAI.PiExponent.HomogeneousSubmoduleGrading.component`, `OAI.PiExponent.HomogeneousSubmoduleGrading.decompositionMap`, `OAI.PiExponent.HomogeneousSubmoduleGrading.piece`, `OAI.PiExponent.IntegerEventualLowerBound`, `OAI.PiExponent.JetGeometry.coordinatePowerIdeal`, `OAI.PiExponent.JetGeometry.rationalWeightedIdeal`, `OAI.PiExponent.JetGeometry.weightedIdeal`, `OAI.PiExponent.LocalLengthTransport.localLength`, `OAI.PiExponent.LocalizedAlgebraEvaluation.denominatorMap`, `OAI.PiExponent.LocalizedAlgebraEvaluation.evaluation`, `OAI.PiExponent.LogTailAnalytic.logTail`, `OAI.PiExponent.MatrixArithmetic.columnScale`, `OAI.PiExponent.MatrixArithmetic.rowScale`, `OAI.PiExponent.MatrixTranslation.periodCoordinate`, `OAI.PiExponent.MatrixTranslation.periodMonomial`, `OAI.PiExponent.MatrixTranslationBounds.truncationOrder`, `OAI.PiExponent.MatrixTranslationBounds.weight`, `OAI.PiExponent.NatToIntGrading.component`, `OAI.PiExponent.NatToIntGrading.decompositionMap`, `OAI.PiExponent.NatToIntGrading.piece`, `OAI.PiExponent.NatToIntGrading.support`, `OAI.PiExponent.NormalBasisProducts.enumeration`, `OAI.PiExponent.NumericalAmpleness.irreducibleClosedRestrict`, `OAI.PiExponent.NumericalAmpleness.irreducibleClosedsBelowEquiv`, `OAI.PiExponent.NumericalAmpleness.mixedSlopePolynomial`, `OAI.PiExponent.OrdinaryAuxiliaryJet.branchCoordinates` and 28 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_GlobalBlowupAffineSquare`, `PiExponent_Ampleness_GlobalExceptionalComparison`, `PiExponent_Ampleness_GlobalReesRecoveryComparison`, `PiExponent_Analysis_LogTailAnalytic`, `PiExponent_Analysis_PeriodAnalytic`, `PiExponent_Analysis_TranslationCountLimit`, `PiExponent_Approximation_ApproximationCenters`, `PiExponent_Approximation_FormalMatrixBridge`, `PiExponent_Approximation_MatrixArithmetic`, `PiExponent_Approximation_MatrixTranslation`, `PiExponent_Approximation_MatrixTranslationBounds`, `PiExponent_Approximation_PersistentWeightComparison`, `PiExponent_Approximation_RectangularVolume`, `PiExponent_Approximation_RowTranslation`, `PiExponent_Approximation_SerreAssembly`, `PiExponent_Approximation_TwistPresentations`, `PiExponent_Cohomology_CartierEulerPair`, `PiExponent_Cohomology_CechOneConverse`, `PiExponent_Cohomology_EulerSupportDimension`, `PiExponent_Cohomology_EulerZeroDimensional`, `PiExponent_Cohomology_GradedCech`, `PiExponent_Cohomology_GradedH0`, `PiExponent_Cohomology_GradedPolynomialLaurent`, `PiExponent_Geometry_IntegralCurveExistence`, `PiExponent_Jets_FormalJetIndices`, `PiExponent_Jets_JetGeometry`, `PiExponent_Jets_NormalBasisProducts`, `PiExponent_Jets_OrdinaryBranchEvaluation`, `PiExponent_Jets_OrdinaryDerivativeIdeals`, `PiExponent_Jets_TransverseMultiplicity`, `PiExponent_LocalAlgebra_IdealPullbackOpenSquare`, `PiExponent_LocalAlgebra_InvertibleIdealAway`, `PiExponent_LocalAlgebra_LocalLengthTransport`, `PiExponent_LocalAlgebra_LocalizedAlgebraEvaluation`, `PiExponent_LocalAlgebra_SerreDimensionShift`, `PiExponent_Polynomials_GradedLocalizationExact`, `PiExponent_Polynomials_GradedSerre`, `PiExponent_Polynomials_HomogeneousSubmoduleGrading`, `PiExponent_Polynomials_MixedSlopePolynomial`, `PiExponent_Polynomials_NatToIntGrading`, `PiExponent_Polynomials_NestedPolynomialSwap`, `PiExponent_Polynomials_PowerCoverBasis`, `PiExponent_Polynomials_PowerCoverExponents`, `PiExponent_Polynomials_PowerCoverSubstitution`, `PiExponent_Polynomials_ShiftedFreeGrading`, `PiExponent_Polynomials_TranslatedPowerCover`, `PiExponent_Statement`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A017` and `OAIQ068A018`; the statements `OAI_PiExponentJets_W22_ActualRegularCutHistory_local_length_bound`, `OAI_PiExponent_CurveInequality_excess_implies_zeroth_eq_one` and `OAI.PiExponent.CurveInequality.excess_implies_zeroth_eq_one_q68`; the proofs of `OAI_PiExponent_CurveFieldRigidity_ordinary_coordinate_constant` and `OAI_PiExponent_CurveInequality_excess_implies_fibre_coordinate_constant`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_GlobalExceptionalComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSeshadri.BlowupGluing
open CategoryTheory AlgebraicGeometry
variable {X : Scheme.{0}} (I : X.IdealSheafData) (U : X.affineOpens)

abbrev affineCenterIdeal :=
  (I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩

end PiExponentSeshadri.BlowupGluing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_GlobalBlowupAffineSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.BlowupGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme.{0}} (I : X.IdealSheafData) (U : X.affineOpens)

def baseChart : Spec (CommRingCat.of Γ(U.1.toScheme, ⊤)) ⟶ X :=
  U.1.toScheme.isoSpec.inv ≫ U.1.ι

instance baseChart_isOpenImmersion : IsOpenImmersion (baseChart (X := X) U) := by
  dsimp [baseChart]
  infer_instance

end
end PiExponentSeshadri.BlowupGluing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealPullbackOpenSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.IdealSectionRestriction
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

theorem squareIdeal {X Y X' Y' : Scheme.{0}} (f : Y ⟶ X)
    (j : X' ⟶ X) (k : Y' ⟶ Y) (f' : Y' ⟶ X') (h : k ≫ f = f' ≫ j)
    (I : X.IdealSheafData) :
    (I.comap f).comap k = (I.comap j).comap f' := by
  rw [← I.comap_comp k f, ← I.comap_comp f' j, h]

end PiExponent.IdealSectionRestriction

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_GlobalReesRecoveryComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.GlobalReesRecoveryComparison
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

local instance affineChartNoetherian {X : Scheme.{0}} [IsLocallyNoetherian X]
    (U : X.affineOpens) : IsNoetherianRing Γ(U.1.toScheme, ⊤) := by
  let : IsAffine U.1.toScheme := U.2
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.1.toScheme⟩

end PiExponent.GlobalReesRecoveryComparison

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_RowTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.RowTranslation

open scoped BigOperators
open MvPolynomial

section FormalSeriesRow
variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]

noncomputable def rowScalar (ε : σ → R) (τ : σ → PowerSeries R)
    (β a : σ →₀ ℕ) (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) : R :=
  ((∏ i, (a i).choose (β i) * (a i - β i).choose (d i) : ℕ) : R) *
    (∏ i, ε i ^ (a i - β i - d i)) *
      PowerSeries.coeff k (∏ i, τ i ^ (d i : ℕ))

end FormalSeriesRow

section FiniteExpansion
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

abbrev RowChoices (S : Finset (σ →₀ ℕ)) (β : σ →₀ ℕ) (s : ℕ) :=
  Σ a : S, (∀ i, Fin (a.1 i - β i + 1)) × Fin (s + 1)

end FiniteExpansion

variable {R : Type*} [CommRing R]

noncomputable def tail (T : ℕ) (f : PowerSeries R) : PowerSeries R :=
  (PowerSeries.trunc T f : PowerSeries R) - f

@[simp] theorem coeff_tail_of_lt (T k : ℕ) (f : PowerSeries R) (hk : k < T) :
    PowerSeries.coeff k (tail T f) = 0 := by
  simp [tail, PowerSeries.coeff_trunc, hk]

end PiExponent.RowTranslation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_LogTailAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent.LogTailAnalytic

noncomputable def logTail (T : ℕ) (z : ℂ) : ℂ :=
  Complex.logTaylor T z - Complex.log (1 + z)

end PiExponent.LogTailAnalytic

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_MatrixTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.MatrixTranslation

open scoped BigOperators
open MvPolynomial
open RowTranslation

noncomputable def periodCoordinate (j : ℕ) (ω : ℂ) : PowerSeries ℂ :=
  PowerSeries.C ((j : ℂ) * ω) + PowerSeries.log ℂ

noncomputable def periodMonomial {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) : MvPolynomial (Fin m) (PowerSeries ℂ) :=
  C ((1 + PowerSeries.X) ^ h) *
    ∏ i, (C (periodCoordinate j ω) + X i) ^ a i

end PiExponent.MatrixTranslation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_PeriodAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open PiExponent.LogTailAnalytic

namespace PiExponent.PeriodAnalytic

noncomputable def periodSeries (b center : ℂ) (h d : ℕ) : PowerSeries ℂ :=
  PowerSeries.C b * (1 + PowerSeries.X) ^ h *
    (PowerSeries.C center + PowerSeries.log ℂ) ^ d

noncomputable def periodFunction (b center : ℂ) (h d : ℕ) (t : ℂ) : ℂ :=
  b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d

end PiExponent.PeriodAnalytic

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_TranslationCountLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PiExponent

noncomputable def translationTermCount (m : ℕ) (v H : ℝ) : ℕ :=
  (⌊H⌋₊ + 1) ^ (2 * m) * (⌊H / v⌋₊ + 1)

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ApproximationCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

noncomputable def logarithmicPeriod : ℂ := 2 * (Real.pi : ℂ) * Complex.I

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_JetGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.JetGeometry

noncomputable section

open MvPowerSeries

variable {σ R : Type*} [CommRing R]

def weightedIdeal (w : σ → ℕ) (N : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {f | (N : ℕ∞) ≤ f.weightedOrder w}
  zero_mem' := by simp
  add_mem' hf hg := (le_min hf hg).trans (min_weightedOrder_le_add w)
  smul_mem' a f hf := by
    change (N : ℕ∞) ≤ weightedOrder w (a * f)
    exact hf.trans (le_add_self.trans (le_weightedOrder_mul w))

@[simp] theorem mem_weightedIdeal (w : σ → ℕ) (N : ℕ)
    (f : MvPowerSeries σ R) :
    f ∈ weightedIdeal w N ↔ (N : ℕ∞) ≤ f.weightedOrder w := Iff.rfl

def coordinatePowerIdeal (e : σ → ℕ) : Ideal (MvPowerSeries σ R) :=
  Ideal.span (Set.range (fun i => (X i : MvPowerSeries σ R) ^ e i))

theorem rational_weight_nonneg (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (d : σ →₀ ℕ) : 0 ≤ Finsupp.weight v d := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_nonneg (fun i _ => nsmul_nonneg (hv i) (d i))

def rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ) :
    Ideal (MvPowerSeries σ R) where
  carrier := {f | ∀ d, Finsupp.weight v d < H → coeff d f = 0}
  zero_mem' := by simp
  add_mem' hf hg := by
    intro d hd
    rw [map_add, hf d hd, hg d hd, add_zero]
  smul_mem' a f hf := by
    classical
    intro d hd
    change coeff d (a * f) = 0
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    have he : ij.1 + ij.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hw : Finsupp.weight v ij.2 ≤ Finsupp.weight v d := by
      rw [← he, map_add]
      exact le_add_of_nonneg_left (rational_weight_nonneg v hv ij.1)
    rw [hf ij.2 (hw.trans_lt hd), mul_zero]

@[simp] theorem mem_rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f : MvPowerSeries σ R) :
    f ∈ rationalWeightedIdeal v hv H ↔
      ∀ d, Finsupp.weight v d < H → coeff d f = 0 := Iff.rfl

end

end PiExponent.JetGeometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_NestedPolynomialSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.FormalMatrixBridge

def nestedPolynomialSwap (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) (Polynomial R) ≃ₐ[R] Polynomial (MvPolynomial (Fin m) R) :=
  (MvPolynomial.mapAlgEquiv (Fin m) (MvPolynomial.uniqueAlgEquiv R Unit).symm).trans
    ((MvPolynomial.commAlgEquiv R (Fin m) Unit).trans
      ((MvPolynomial.uniqueAlgEquiv (MvPolynomial (Fin m) R) Unit).restrictScalars R))

end PiExponent.FormalMatrixBridge

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_FormalMatrixBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.FormalMatrixBridge

open MvPowerSeries
open scoped BigOperators

def flatten (m : ℕ) :
    MvPolynomial (Fin m) (Polynomial ℂ) →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  (MvPolynomial.coeToMvPowerSeries.algHom ℂ).comp
    ((MvPolynomial.finSuccEquiv ℂ m).symm.toAlgHom.comp
      (nestedPolynomialSwap ℂ m).toAlgHom)

end PiExponent.FormalMatrixBridge

end

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

noncomputable def columnScale {m : ℕ} (q : Fin m → ℕ) (a : Fin m → ℕ) : ℝ :=
  ∏ i, (q i : ℝ) ^ a i

noncomputable def rowScale {m : ℕ} (q : Fin m → ℕ) (b : Fin m → ℕ) : ℝ :=
  (columnScale q b)⁻¹

end MatrixArithmetic

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_MatrixTranslationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.MatrixTranslationBounds

open scoped BigOperators
open RowTranslation

noncomputable def weight {σ : Type*} [Fintype σ] (w : σ → ℝ) (a : σ → ℕ) : ℝ :=
  ∑ i, w i * a i

noncomputable def truncationOrder (F v w : ℝ) : ℕ := ⌈F * w / v⌉₊

end PiExponent.MatrixTranslationBounds

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_OrdinaryDerivativeIdeals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryDerivatives

open scoped BigOperators

abbrev Polynomial (n : ℕ) := MvPolynomial (Fin n) ℂ

def partialFrame (n : ℕ) (i : Fin n) : Derivation ℚ (Polynomial n) (Polynomial n) :=
  (MvPolynomial.pderiv i).restrictScalars ℚ

@[simp] theorem partialFrame_apply (n : ℕ) (i : Fin n) (p : Polynomial n) :
    partialFrame n i p = MvPolynomial.pderiv i p := rfl

end PiExponent.OrdinaryDerivatives
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_RectangularVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent

noncomputable def rectangularCutoff {k : ℕ} (κ : Fin k → ℝ) (T : ℝ) (i : Fin k) : ℕ :=
  ⌈T / ((k : ℝ) * κ i)⌉₊

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_TransverseMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox.TransverseMultiplicity

noncomputable section

open MvPowerSeries

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

def rectangularIdeal (n : σ → ℕ) : Ideal (MvPowerSeries σ K) where
  carrier := {f | ∀ d, (∀ i, d i < n i) → coeff d f = 0}
  zero_mem' := by intro d hd; exact map_zero _
  add_mem' := by
    intro f g hf hg d hd
    rw [map_add, hf d hd, hg d hd, zero_add]
  smul_mem' := by
    intro a f hf d hd
    change coeff d (a * f) = 0
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro ab hab
    have heq : ab.1 + ab.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hb : ∀ i, ab.2 i < n i := by
      intro i
      have hdi := hd i
      rw [← heq, Finsupp.add_apply] at hdi
      omega
    rw [hf ab.2 hb, mul_zero]

end
end PiExponentApprox.TransverseMultiplicity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_NormalBasisProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.NormalBasisProducts

open scoped BigOperators

variable {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def enumeration (A B : Finset ι) (hcard : A.card = B.card) : Fin A.card → ι :=
  fun i => (B.equivFin.symm (Fin.cast hcard i)).val

end PiExponent.NormalBasisProducts
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalLengthTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.LocalLengthTransport

abbrev localLength {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsPrime] (I : Ideal R) : ℕ∞ :=
  Module.length (Localization.AtPrime P)
    (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))

end PiExponent.LocalLengthTransport

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PowerCoverExponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.PowerCover

noncomputable section

variable {σ : Type*} [Fintype σ]

def scale (w : σ → ℕ) (q : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => w i * q i)

def quotient (w : σ → ℕ) (a : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => a i / w i)

def residue (w : σ → ℕ) (hw : ∀ i, 0 < w i) (a : σ →₀ ℕ) :
    ∀ i, Fin (w i) :=
  fun i => ⟨a i % w i, Nat.mod_lt _ (hw i)⟩

def combine (w : σ → ℕ) (p : (σ →₀ ℕ) × (∀ i, Fin (w i))) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => w i * p.1 i + (p.2 i).val)

@[simp] theorem scale_apply (w : σ → ℕ) (q : σ →₀ ℕ) (i : σ) :
    scale w q i = w i * q i := by simp [scale]

@[simp] theorem quotient_apply (w : σ → ℕ) (a : σ →₀ ℕ) (i : σ) :
    quotient w a i = a i / w i := by simp [quotient]

omit [Fintype σ] in
@[simp] theorem residue_apply (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a : σ →₀ ℕ) (i : σ) :
    (residue w hw a i).val = a i % w i := rfl

@[simp] theorem combine_apply (w : σ → ℕ)
    (p : (σ →₀ ℕ) × (∀ i, Fin (w i))) (i : σ) :
    combine w p i = w i * p.1 i + (p.2 i).val := by simp [combine]

@[simp] theorem combine_quotient_residue (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a : σ →₀ ℕ) :
    combine w (quotient w a, residue w hw a) = a := by
  ext i
  simp only [combine_apply, quotient_apply, residue_apply]
  exact Nat.div_add_mod (a i) (w i)

@[simp] theorem quotient_combine (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : (σ →₀ ℕ) × (∀ i, Fin (w i))) :
    quotient w (combine w p) = p.1 := by
  ext i
  simp only [quotient_apply, combine_apply]
  rw [Nat.mul_add_div (hw i)]
  simp [Nat.div_eq_of_lt (p.2 i).isLt]

@[simp] theorem residue_combine (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : (σ →₀ ℕ) × (∀ i, Fin (w i))) :
    residue w hw (combine w p) = p.2 := by
  funext i
  apply Fin.ext
  simp [Nat.add_mod, Nat.mod_eq_of_lt (p.2 i).isLt]

def exponentEquiv (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    (σ →₀ ℕ) ≃ ((σ →₀ ℕ) × (∀ i, Fin (w i))) where
  toFun a := (quotient w a, residue w hw a)
  invFun := combine w
  left_inv := combine_quotient_residue w hw
  right_inv p := by simp [quotient_combine w hw]

@[simp] theorem exponentEquiv_apply (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a : σ →₀ ℕ) : exponentEquiv w hw a = (quotient w a, residue w hw a) := rfl

@[simp] theorem exponentEquiv_symm_apply (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : (σ →₀ ℕ) × (∀ i, Fin (w i))) :
    (exponentEquiv w hw).symm p = combine w p := rfl

@[simp] theorem quotient_add_scale (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a q : σ →₀ ℕ) :
    quotient w (a + scale w q) = quotient w a + q := by
  ext i
  simp only [quotient_apply, Finsupp.add_apply, scale_apply]
  simp [Nat.add_mul_div_left, hw i]

@[simp] theorem residue_add_scale (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a q : σ →₀ ℕ) :
    residue w hw (a + scale w q) = residue w hw a := by
  funext i
  apply Fin.ext
  simp [Nat.add_mod]

@[simp] theorem exponentEquiv_add_scale (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a q : σ →₀ ℕ) :
    exponentEquiv w hw (a + scale w q) = (quotient w a + q, residue w hw a) := by
  simp [quotient_add_scale w hw]

@[simp] theorem combine_add (w : σ → ℕ) (q q' : σ →₀ ℕ)
    (r : ∀ i, Fin (w i)) :
    combine w (q + q', r) = combine w (q, r) + scale w q' := by
  ext i
  simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm]

@[simp] theorem scale_zero (w : σ → ℕ) : scale w 0 = 0 := by
  ext i
  simp

@[simp] theorem scale_add (w : σ → ℕ) (q q' : σ →₀ ℕ) :
    scale w (q + q') = scale w q + scale w q' := by
  ext i
  simp [Nat.mul_add]

end
end PiExponent.PowerCover

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PowerCoverSubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.PowerCover

noncomputable section

variable {σ k : Type*} [Fintype σ] [CommSemiring k]

def scaleHom (w : σ → ℕ) : (σ →₀ ℕ) →+ (σ →₀ ℕ) where
  toFun := scale w
  map_zero' := scale_zero w
  map_add' := scale_add w

def powerSubstitution (w : σ → ℕ) :
    MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun i => MvPolynomial.X i ^ w i)

omit [Fintype σ] in
@[simp] theorem powerSubstitution_X (w : σ → ℕ) (i : σ) :
    powerSubstitution (k := k) w (MvPolynomial.X i) = MvPolynomial.X i ^ w i := by
  simp [powerSubstitution]

end
end PiExponent.PowerCover

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PowerCoverBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.PowerCover
noncomputable section

variable {σ : Type*} [Fintype σ] {k : Type*} [CommSemiring k]

def decompositionAddEquiv (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    MvPolynomial σ k ≃+ ((∀ i, Fin (w i)) →₀ MvPolynomial σ k) :=
  (AddMonoidAlgebra.coeffAddEquiv : MvPolynomial σ k ≃+ ((σ →₀ ℕ) →₀ k)).trans <|
    (Finsupp.domCongr ((exponentEquiv w hw).trans (Equiv.prodComm _ _))).trans <|
      Finsupp.curryAddEquiv.trans <|
        Finsupp.mapRange.addEquiv AddMonoidAlgebra.coeffAddEquiv.symm

@[simp] theorem decompositionAddEquiv_monomial (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a : σ →₀ ℕ) (c : k) :
    decompositionAddEquiv w hw (MvPolynomial.monomial a c) =
      Finsupp.single (residue w hw a) (MvPolynomial.monomial (quotient w a) c) := by
  classical
  simp [decompositionAddEquiv, MvPolynomial.monomial, Finsupp.curry_single]

end

end PiExponent.PowerCover

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_TranslatedPowerCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.TranslatedPowerCover

open scoped BigOperators

noncomputable section

variable {σ k : Type*} [Fintype σ] [Field k]

def Ring (_weights : σ → ℕ) (_center : σ → k) := MvPolynomial σ k

end
end PiExponent.TranslatedPowerCover

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_PersistentWeightComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.PersistentWeightComparison

open scoped BigOperators
open PiExponentApprox NormalBasisProducts

def comparisonConstant (m : ℕ) (sigma : ℝ) : ℝ :=
  2 * ((m : ℝ) + 2) ^ (m + 2) * (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2)

def UniformRectangles (n : ℕ) (cost : Fin n → ℝ) (epsilon N : ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → k ≤ n → ∀ B : Fin k → Fin n, ∀ i,
    2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i

end PiExponent.PersistentWeightComparison
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_SerreDimensionShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.SerreDimensionShift

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w v u t
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem ext_eq_zero_of_biproduct (A : C) {J : Type*} [Fintype J]
    {B : J → C} {c : Bicone B} (hc : c.IsBilimit) (q : ℕ)
    (hzero : ∀ j, ∀ x : Ext.{w} A (B j) q, x = 0)
    (x : Ext.{w} A c.pt q) : x = 0 := by
  apply (Ext.addEquivBiproduct A hc q).injective
  ext j
  exact (hzero j _).trans ((map_zero (Ext.addEquivBiproduct A hc q)) ▸ rfl)

structure AcyclicPresentation {ι : Type t} (A : C) (F : ι → ℕ → C) (i : ι) where
  kernel : ι
  shift : ℕ
  middle : ℕ → C
  left : ∀ n, F kernel n ⟶ middle n
  right : ∀ n, middle n ⟶ F i (shift + n)
  comp_zero : ∀ n, left n ≫ right n = 0
  shortExact : ∀ n, (ShortComplex.mk (left n) (right n) (comp_zero n)).ShortExact
  acyclic : ∀ n q, 0 < q → ∀ x : Ext.{w} A (middle n) q, x = 0

end
end PiExponent.GeometrySupport.SerreDimensionShift

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TwistPresentations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.TwistPresentations
noncomputable section
universe w
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

abbrev schemeUnit (X : Scheme.{0}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

end
end PiExponent.GeometrySupport.TwistPresentations

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SerreAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.SerreAssembly

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open TwistPresentations

variable {X : Scheme.{0}} [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]

local instance instHasExtModules_solutions : HasExt.{1} X.Modules := HasExt.standard _

end
end PiExponent.GeometrySupport.SerreAssembly

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CartierEulerPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
variable {X : Scheme.{0}}

namespace CartierEulerPair

lemma iso_middle_comm {C : Type*} [Category C] {A B D : C}
    (f : A ⟶ B) (e : D ≅ B) : 𝟙 A ≫ f = (f ≫ e.inv) ≫ e.hom := by
  simp

end CartierEulerPair
end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechOneConverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.CechOneConverse

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
universe u
variable {Y : Scheme.{u}} {J : Type u} (U : J → Y.Opens) (M : Y.Modules)
local instance instHasExtModules_solutions : HasExt.{u+1} Y.Modules := HasExt.standard _

end PiExponent.GeometrySupport.CechOneConverse

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EulerSupportDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

theorem dimension_le_of_local_bound {T : Type*} [TopologicalSpace T] (d : ℕ)
    (h : ∀ x : T, ∃ U : Opens T, x ∈ U ∧ topologicalKrullDim U ≤ d) :
    topologicalKrullDim T ≤ d := by
  rw [← ENat.WithBot.lt_add_one_iff]
  suffices topologicalKrullDim T < ((d+1 : ℕ) : WithBot ℕ∞) by
    simpa only [Nat.cast_add, Nat.cast_one] using this
  apply Order.krullDim_lt_coe_iff.mpr
  intro c
  obtain ⟨x, hx⟩ := c.head.isIrreducible.nonempty
  obtain ⟨U, hxU, hU⟩ := h x
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding
    (Subtype.val : U → T) U.isOpen.isOpenEmbedding_subtypeVal
  have hm (i : Fin (c.length + 1)) :
      ((Subtype.val : U → T) ⁻¹' (c i : Set T)).Nonempty := by
    refine ⟨⟨x, hxU⟩, ?_⟩
    exact c.strictMono.monotone (Fin.zero_le i) hx
  let c' : LTSeries {Z : IrreducibleCloseds T |
      ((Subtype.val : U → T) ⁻¹' (Z : Set T)).Nonempty} :=
    ⟨c.length, fun i => ⟨c i, hm i⟩, fun i => c.step i⟩
  have hc := (Order.LTSeries.length_le_krullDim (c'.map e.symm e.symm.strictMono)).trans hU
  have hc' : c.length ≤ d := by exact_mod_cast hc
  omega

variable {X : Scheme.{0}}

theorem mono_comp_iso {C : Type*} [Category C] {A B D : C}
    (g : A ⟶ B) (e : B ≅ D) (hg : Mono g) : Mono (g ≫ e.hom) := by
  let : Mono g := hg
  infer_instance

theorem mono_iso_inv_comp_p1 {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (g : A ⟶ D) (hg : Mono g) : Mono (e.inv ≫ g) := by
  let : Mono g := hg
  infer_instance

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EulerZeroDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme.{0}}

theorem discreteTopology_of_dim_le_zero [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 0) : DiscreteTopology X := by
  let : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  infer_instance

theorem finite_of_dim_le_zero [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 0) : Finite X := by
  let : DiscreteTopology X := discreteTopology_of_dim_le_zero hdim
  exact finite_of_compact_of_discrete

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_ShiftedFreeGrading
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ShiftedFreeGrading
noncomputable section
open scoped BigOperators
open DirectSum
variable {A J σA : Type*} [AddCommGroup A] [Fintype J]
  [SetLike σA A] [AddSubgroupClass σA A]
  (𝒜 : ℤ → σA) [DirectSum.Decomposition 𝒜] (w : J → ℤ)

def piece (d : ℤ) : AddSubgroup (J → A) where
  carrier := {f | ∀ j, f j ∈ 𝒜 (d - w j)}
  zero_mem' := fun _j => zero_mem _
  add_mem' := fun hf hg j => add_mem (hf j) (hg j)
  neg_mem' := fun hf j => neg_mem (hf j)

def component (f : J → A) (d : ℤ) : piece 𝒜 w d :=
  ⟨fun j => (DirectSum.decompose 𝒜 (f j) (d - w j) : A),
    fun j => (DirectSum.decompose 𝒜 (f j) (d - w j)).property⟩

def support (f : J → A) : Finset ℤ := by
  classical
  exact Finset.univ.biUnion fun j =>
    (DirectSum.decompose 𝒜 (f j)).support.image (fun d => d + w j)

theorem component_eq_zero_of_not_mem (f : J → A) (d : ℤ)
    (hd : d ∉ support 𝒜 w f) : component 𝒜 w f d = 0 := by
  classical
  apply Subtype.ext
  funext j
  change (DirectSum.decompose 𝒜 (f j) (d - w j) : A) = 0
  have hh : d - w j ∉ (DirectSum.decompose 𝒜 (f j)).support := by
    intro h
    apply hd
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨d - w j, h, sub_add_cancel _ _⟩⟩
  rw [DFinsupp.notMem_support_iff.mp hh]
  rfl

def decompositionMap : (J → A) →+ ⨁ d, piece 𝒜 w d where
  toFun f := DFinsupp.mk' (component 𝒜 w f)
    (Trunc.mk ⟨(support 𝒜 w f).val, fun d => by
      classical
      by_cases hd : d ∈ support 𝒜 w f
      · exact Or.inl hd
      · exact Or.inr (component_eq_zero_of_not_mem 𝒜 w f d hd)⟩)
  map_zero' := by
    ext d j
    change (DirectSum.decompose 𝒜 (0 : A) (d - w j) : A) = 0
    rw [DirectSum.decompose_zero]
    rfl
  map_add' f g := by
    ext d j
    change (DirectSum.decompose 𝒜 (f j + g j) (d - w j) : A) =
      (DirectSum.decompose 𝒜 (f j) (d - w j) : A) +
      (DirectSum.decompose 𝒜 (g j) (d - w j) : A)
    rw [DirectSum.decompose_add]
    rfl

@[simp] theorem decompositionMap_apply (f : J → A) (d : ℤ) (j : J) :
    (decompositionMap 𝒜 w f d : J → A) j =
      (DirectSum.decompose 𝒜 (f j) (d - w j) : A) := rfl

theorem decompositionMap_injective : Function.Injective (decompositionMap 𝒜 w) := by
  intro f g h
  funext j
  apply (DirectSum.decompose 𝒜).injective
  ext d
  have hh := congrArg (fun z : ⨁ d, piece 𝒜 w d => (z (d + w j) : J → A) j) h
  change (DirectSum.decompose 𝒜 (f j) (d + w j - w j) : A) =
    (DirectSum.decompose 𝒜 (g j) (d + w j - w j) : A) at hh
  rw [show d + w j - w j = d by omega] at hh
  exact hh

theorem decompositionMap_homogeneous (d : ℤ) (f : piece 𝒜 w d) :
    decompositionMap 𝒜 w f.val = DirectSum.of (fun d => piece 𝒜 w d) d f := by
  classical
  ext e j
  by_cases he : d = e
  · subst e
    rw [DirectSum.of_eq_same]
    exact DirectSum.decompose_of_mem_same 𝒜 (f.property j)
  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm he)]
    change (DirectSum.decompose 𝒜 (f.val j) (e - w j) : A) = 0
    exact DirectSum.decompose_of_mem_ne 𝒜 (f.property j) (by omega)

instance decomposition : DirectSum.Decomposition (piece 𝒜 w) := by
  classical
  have hr : (decompositionMap 𝒜 w).comp (DirectSum.coeAddMonoidHom (piece 𝒜 w)) =
      AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro d f
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
      AddMonoidHom.id_apply, decompositionMap_homogeneous]
  apply DirectSum.Decomposition.ofAddHom (piece 𝒜 w) (decompositionMap 𝒜 w) ?_ hr
  apply AddMonoidHom.ext
  intro f
  apply decompositionMap_injective 𝒜 w
  exact DFunLike.congr_fun hr (decompositionMap 𝒜 w f)

@[simp] theorem decompose_apply (f : J → A) (d : ℤ) (j : J) :
    (DirectSum.decompose (piece 𝒜 w) f d : J → A) j =
      (DirectSum.decompose 𝒜 (f j) (d - w j) : A) := rfl

end
end PiExponent.ShiftedFreeGrading

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_GradedSerre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedSerre

noncomputable section
open scoped BigOperators

variable {R M ι σ : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq ι] [SetLike σ M] [AddSubmonoidClass σ M]
  (𝓜 : ι → σ) [DirectSum.Decomposition 𝓜]

theorem kernel_homogeneous
    {N τ : Type*} [AddCommMonoid N] [Module R N]
    [SetLike τ N] [AddSubmonoidClass τ N]
    (𝓝 : ι → τ) [DirectSum.Decomposition 𝓝]
    (f : M →ₗ[R] N)
    (hf : ∀ d x, f (DirectSum.decompose 𝓜 x d : M) =
      (DirectSum.decompose 𝓝 (f x) d : N)) :
    f.ker.IsHomogeneous 𝓜 := by
  intro d x hx
  change f (DirectSum.decompose 𝓜 x d : M) = 0
  rw [hf, LinearMap.mem_ker.mp hx, DirectSum.decompose_zero]
  rfl

section IntegerGrading
variable {A P σA σP : Type*} [Ring A] [AddCommGroup P] [Module A P]
  [SetLike σA A] [AddSubgroupClass σA A]
  [SetLike σP P] [AddSubgroupClass σP P]
  (𝒜 : ℤ → σA) (𝓟 : ℤ → σP)
  [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition 𝓟]
  [SetLike.GradedSMul 𝒜 𝓟]

instance shiftedFreeGradedSMul [SetLike.GradedMonoid 𝒜] {J : Type*} [Fintype J]
    (w : J → ℤ) : SetLike.GradedSMul 𝒜 (ShiftedFreeGrading.piece 𝒜 w) where
  smul_mem := by
    intro i d a f ha hf j
    change a * f j ∈ 𝒜 (i + d - w j)
    have h : a * f j ∈ 𝒜 (i + (d - w j)) :=
      SetLike.GradedMul.mul_mem ha (hf j)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    omega

end IntegerGrading

end
end PiExponent.GradedSerre

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_GradedLocalizationExact
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

variable (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
  (a : R) (e : ℤ) (ha : a ∈ 𝒜 e)

variable (𝓝 : ℤ → σN) [SetLike.GradedSMul 𝒜 𝓝]

section Decomposition
variable [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]

theorem preserves_of_compatible (f : M →ₗ[R] N)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N)) :
    ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 i := by
  intro i m hm
  have h := hf i m
  rw [DirectSum.decompose_of_mem_same 𝓜 hm] at h
  exact h.symm ▸ (DirectSum.decompose 𝓝 (f m) i).property

end Decomposition

end
end PiExponent.GradedLocalizationExact

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedCech
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

variable {σR σM : Type*} [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

section Cover
variable {J : Type*} [DecidableEq J] (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1)

section Maps
variable {N σN : Type*} [AddCommGroup N] [Module R N]
  [SetLike σN N] [AddSubgroupClass σN N]
  (𝓝 : ℤ → σN) [SetLike.GradedSMul 𝒜 𝓝]
  (f : M →ₗ[R] N) (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 i)

def globalPieceMap (d : ℤ) : 𝓜 d →+ 𝓝 d where
  toFun m := ⟨f m, hf d m m.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

end Maps

end Cover

end
end PiExponent.GradedCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedH0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedH0
noncomputable section
open scoped BigOperators
variable {ι R : Type*} [Fintype ι] [CommRing R]

def PolynomialExponent (n : ℕ) := {b : ι →₀ ℕ // b.degree = n}

theorem integer_grading_eq_homogeneous (n : ℕ) :
    MvPolynomial.weightedHomogeneousSubmodule R (1 : ι → ℤ) (n : ℤ) =
      MvPolynomial.homogeneousSubmodule ι R n := by
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported,
    MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  have hweight (b : ι →₀ ℕ) : Finsupp.weight (1 : ι → ℤ) b = (b.degree : ℤ) := by
    simp [Finsupp.weight_eq_sum, Finsupp.degree_eq_sum, Nat.cast_sum]
  congr 1
  ext b
  simp only [Set.mem_ofPred_eq, hweight, Int.natCast_inj]

end
end PiExponent.GradedH0

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedPolynomialLaurent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedPolynomialLaurent
noncomputable section
open scoped BigOperators
open PiExponent.GradedCech PiExponent.GradedLocalizationExact
attribute [local instance] Classical.propDecidable MvPolynomial.weightedGradedAlgebra
variable {J R : Type*} [CommRing R]

abbrev GroupAlgebra := AddMonoidAlgebra R (J → ℤ)

def natExponentHom : (J →₀ ℕ) →+ (J → ℤ) where
  toFun b j := b j
  map_zero' := by ext j; simp
  map_add' := by intro a b; ext j; simp

def polynomialToGroupAlgebra : MvPolynomial J R →+* GroupAlgebra (J := J) (R := R) :=
  AddMonoidAlgebra.mapDomainRingHom R natExponentHom

def product (s : Finset J) : MvPolynomial J R := ∏ j ∈ s, MvPolynomial.X j

def productExponent (s : Finset J) : J → ℤ := ∑ j ∈ s, natExponentHom (Finsupp.single j 1)

theorem single_isUnit (a : J → ℤ) :
    IsUnit (AddMonoidAlgebra.single a (1 : R) : GroupAlgebra (J := J) (R := R)) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨AddMonoidAlgebra.single (-a) 1, ?_⟩
  rw [AddMonoidAlgebra.single_mul_single]
  simp only [add_neg_cancel, one_mul]
  rfl

@[simp] theorem polynomialToGroupAlgebra_X (j : J) :
    polynomialToGroupAlgebra (R := R) (MvPolynomial.X j) =
      AddMonoidAlgebra.single (natExponentHom (Finsupp.single j 1)) 1 := by
  change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single _ _) = _
  exact AddMonoidAlgebra.mapDomain_single

@[simp] theorem polynomialToGroupAlgebra_product (s : Finset J) :
    polynomialToGroupAlgebra (R := R) (product s) =
      AddMonoidAlgebra.single (productExponent s) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [product, productExponent, Finset.prod_empty, Finset.sum_empty, map_one]
      rfl
  | @insert j s hj ih =>
      simp only [product, Finset.prod_insert hj, map_mul] at *
      rw [polynomialToGroupAlgebra_X, ih, AddMonoidAlgebra.single_mul_single]
      simp [productExponent, hj]

theorem product_isUnit (s : Finset J) :
    IsUnit (polynomialToGroupAlgebra (R := R) (product s)) := by
  rw [polynomialToGroupAlgebra_product]
  exact single_isUnit _

def ringLocalizationMap (s : Finset J) :
    Localization.Away (product (R := R) s) →+* GroupAlgebra (J := J) (R := R) :=
  Localization.awayLift polynomialToGroupAlgebra (product s) (product_isUnit s)

@[simp] theorem ringLocalizationMap_base (s : Finset J) (p : MvPolynomial J R) :
    ringLocalizationMap s (algebraMap _ _ p) = polynomialToGroupAlgebra p :=
  IsLocalization.Away.lift_eq (product s) (product_isUnit s) p

def moduleRingEquiv (s : Finset J) :
    LocalizedModule (Submonoid.powers (product (R := R) s)) (MvPolynomial J R) ≃ₗ[MvPolynomial J R]
      Localization.Away (product (R := R) s) :=
  IsLocalizedModule.iso _ (Algebra.linearMap _ _)

variable [Fintype J]

abbrev grading : ℤ → Submodule R (MvPolynomial J R) :=
  MvPolynomial.weightedHomogeneousSubmodule R (1 : J → ℤ)

omit [Fintype J] in
theorem variable_mem (j : J) : MvPolynomial.X j ∈ grading (R := R) (J := J) 1 :=
  MvPolynomial.isWeightedHomogeneous_X R (1 : J → ℤ) j

end
end PiExponent.GradedPolynomialLaurent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_IntegralCurveExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Order

namespace PiExponent.NumericalAmpleness

noncomputable section

def irreducibleClosedRestrict {X : Type*} [TopologicalSpace X]
    (Z : IrreducibleCloseds X) (W : Set.Iic Z) : IrreducibleCloseds (Z : Set X) where
  carrier := {x : ↥(Z : Set X) | x.val ∈ (W.val : Set X)}
  isIrreducible' := by
    have : IrreducibleSpace (W.val : Set X) := Subtype.irreducibleSpace W.val.isIrreducible
    have hi := (IrreducibleSpace.isIrreducible_univ (W.val : Set X)).image
      (Set.inclusion W.property) (continuous_inclusion W.property).continuousOn
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.property
  isClosed' := W.val.isClosed.preimage continuous_subtype_val

def irreducibleClosedsBelowEquiv {X : Type*} [TopologicalSpace X]
    (Z : IrreducibleCloseds X) :
    IrreducibleCloseds (Z : Set X) ≃o Set.Iic Z where
  toFun W := ⟨{
    carrier := Subtype.val '' (W : Set (Z : Set X))
    isIrreducible' := W.isIrreducible.image Subtype.val continuous_subtype_val.continuousOn
    isClosed' := Z.isClosed.isClosedMap_subtype_val _ W.isClosed }, by
      rintro _ ⟨x, _, rfl⟩
      exact x.property⟩
  invFun := irreducibleClosedRestrict Z
  left_inv W := by
    ext x
    change x.val ∈ Subtype.val '' (W : Set ↥(Z : Set X)) ↔ x ∈ (W : Set ↥(Z : Set X))
    constructor
    · rintro ⟨y, hy, hxy⟩
      have heq : y = x := Subtype.ext hxy
      exact heq ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  right_inv W := by
    apply Subtype.ext
    apply SetLike.coe_injective
    change (Subtype.val : ↥(Z : Set X) → X) '' {x : ↥(Z : Set X) | x.val ∈ (W.val : Set X)} = (W.val : Set X)
    apply Set.image_preimage_eq_of_subset
    simpa only [Subtype.range_coe] using (show (W.val : Set X) ⊆ Z from W.property)
  map_rel_iff' := by
    intro W V
    change Subtype.val '' (W : Set (Z : Set X)) ⊆ Subtype.val '' (V : Set (Z : Set X)) ↔ W ≤ V
    exact Set.image_subset_image_iff Subtype.val_injective

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalJetIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.FormalMatrixBridge

theorem cast_finsupp_weight {n : ℕ} (V : Fin n → ℚ) (d : Fin n →₀ ℕ) :
    (Finsupp.weight V d : ℝ) = ∑ i, (V i : ℝ) * (d i : ℝ) := by
  simp only [Finsupp.weight_eq_sum, nsmul_eq_mul, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_natCast, mul_comm]

end PiExponent.FormalMatrixBridge

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_OrdinaryBranchEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryAuxiliaryJet

open MvPowerSeries

def branchCoordinates {n : ℕ} (c : Fin n → ℂ) (x : Fin n → PowerSeries ℂ) :
    Fin n → PowerSeries ℂ := fun i => x i - PowerSeries.C (c i)

end PiExponent.OrdinaryAuxiliaryJet
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_InvertibleIdealAway
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.InvertibleIdealAway
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X B C : Scheme.{0}}

theorem isIso_of_comp_iso_hom {D : Type*} [Category D]
    {A B C : D} (f : A ⟶ B) (e : B ≅ C) (h : IsIso (f ≫ e.hom)) : IsIso f :=
  (isIso_comp_right_iff f e.hom).mp h

theorem pullback_map_isIso_of_factors
    {M N : B.Modules} (ι : M ⟶ N) (g : C ⟶ B)
    (U : B.Opens) (h : C ⟶ U.toScheme) (hfac : h ≫ U.ι = g)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map ι)] :
    IsIso ((Scheme.Modules.pullback g).map ι) := by
  have : IsIso ((Scheme.Modules.pullback U.ι).map ι) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) ι).mp inferInstance
  have : IsIso ((Scheme.Modules.pullback h).map ((Scheme.Modules.pullback U.ι).map ι)) :=
    inferInstance
  have hcomp : IsIso ((Scheme.Modules.pullback (h ≫ U.ι)).map ι) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp h U.ι) ι).mp (by
      change IsIso ((Scheme.Modules.pullback h).map ((Scheme.Modules.pullback U.ι).map ι))
      infer_instance)
  exact hfac ▸ hcomp

end PiExponent.InvertibleIdealAway

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalizedAlgebraEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.LocalizedAlgebraEvaluation
noncomputable section
variable {P A B : Type*} [CommRing P] [CommRing A] [CommRing B] [Algebra P A]
variable (S : Submonoid P) (T : Submonoid B) (f : A →+* B)
  (hf : ∀ s : S, f (algebraMap P A s.val) ∈ T)

def denominatorMap : S →* T where
  toFun s := ⟨f (algebraMap P A s.val), hf s⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp)

@[simp] theorem denominatorMap_val (s : S) :
    (denominatorMap S T f hf s).val = f (algebraMap P A s.val) := rfl

def evaluation : LocalizedModule S A →+ Localization T where
  toFun z := z.liftOn
    (fun p => IsLocalization.mk' (Localization T) (f p.1) (denominatorMap S T f hf p.2))
    (by
      rintro ⟨m,s⟩ ⟨m',s'⟩ ⟨u, hu⟩
      apply (IsLocalization.eq (M := T) (S := Localization T)).mpr
      refine ⟨denominatorMap S T f hf u, ?_⟩
      change f (algebraMap P A u.val) * (f (algebraMap P A s'.val) * f m) =
        f (algebraMap P A u.val) * (f (algebraMap P A s.val) * f m')
      simpa only [Submonoid.smul_def, Algebra.smul_def, map_mul] using congrArg f hu)
  map_zero' := by
    rw [← LocalizedModule.zero_mk (1 : S), LocalizedModule.liftOn_mk,
      map_zero, IsLocalization.mk'_zero]
  map_add' z w := by
    induction z, w using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      simp only [LocalizedModule.mk_add_mk, LocalizedModule.liftOn_mk,
        Submonoid.smul_def, Algebra.smul_def, map_add, map_mul]
      simpa only [denominatorMap_val, mul_comm] using
        (IsLocalization.mk'_add (M := T) (S := Localization T) (f m) (f m')
          (denominatorMap S T f hf s) (denominatorMap S T f hf s'))

@[simp] theorem evaluation_mk (m : A) (s : S) :
    evaluation S T f hf (LocalizedModule.mk m s) =
      IsLocalization.mk' (Localization T) (f m) (denominatorMap S T f hf s) :=
by
  simp only [evaluation, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LocalizedModule.liftOn_mk]

theorem evaluation_smul (p : P) (z : LocalizedModule S A) :
    evaluation S T f hf (p • z) =
      algebraMap B (Localization T) (f (algebraMap P A p)) * evaluation S T f hf z := by
  induction z using LocalizedModule.induction_on with
  | h m s =>
    rw [LocalizedModule.smul'_mk, evaluation_mk, evaluation_mk]
    simp only [Algebra.smul_def, map_mul]
    exact (IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _).symm

end
end PiExponent.LocalizedAlgebraEvaluation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousSubmoduleGrading
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.HomogeneousSubmoduleGrading
noncomputable section
open DirectSum
variable {R M σM : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝓜 : ℤ → σM) [DirectSum.Decomposition 𝓜]
  (K : Submodule R M) (hK : K.IsHomogeneous 𝓜)

def piece (_hK : K.IsHomogeneous 𝓜) (d : ℤ) : AddSubgroup K where
  carrier := {m | (m : M) ∈ 𝓜 d}
  zero_mem' := zero_mem _
  add_mem' := fun hm hn => add_mem hm hn
  neg_mem' := fun hm => neg_mem hm

def component (m : K) (d : ℤ) : piece 𝓜 K hK d :=
  ⟨⟨DirectSum.decompose 𝓜 (m : M) d, hK d m.property⟩,
    (DirectSum.decompose 𝓜 (m : M) d).property⟩

def decompositionMap : K →+ ⨁ d, piece 𝓜 K hK d where
  toFun m := by
    classical
    exact DFinsupp.mk' (component 𝓜 K hK m) (Trunc.mk
    ⟨(DirectSum.decompose 𝓜 (m : M)).support.val, fun d => by
      classical
      by_cases hd : d ∈ (DirectSum.decompose 𝓜 (m : M)).support
      · exact Or.inl hd
      · right
        apply Subtype.ext
        apply Subtype.ext
        change (DirectSum.decompose 𝓜 (m : M) d : M) = 0
        rw [DFinsupp.notMem_support_iff.mp hd]
        rfl⟩)
  map_zero' := by
    ext d
    change (DirectSum.decompose 𝓜 (0 : M) d : M) = 0
    rw [DirectSum.decompose_zero]
    rfl
  map_add' m n := by
    ext d
    change (DirectSum.decompose 𝓜 ((m : M) + (n : M)) d : M) =
      (DirectSum.decompose 𝓜 (m : M) d : M) + (DirectSum.decompose 𝓜 (n : M) d : M)
    rw [DirectSum.decompose_add]
    rfl

@[simp] theorem decompositionMap_apply (m : K) (d : ℤ) :
    (((decompositionMap 𝓜 K hK m) d : K) : M) =
      (DirectSum.decompose 𝓜 (m : M) d : M) := rfl

theorem decompositionMap_injective : Function.Injective (decompositionMap 𝓜 K hK) := by
  intro m n h
  apply Subtype.ext
  apply (DirectSum.decompose 𝓜).injective
  ext d
  exact congrArg (fun z : ⨁ d, piece 𝓜 K hK d => ((z d : K) : M)) h

theorem decompositionMap_homogeneous (d : ℤ) (m : piece 𝓜 K hK d) :
    decompositionMap 𝓜 K hK m.val = DirectSum.of (fun d => piece 𝓜 K hK d) d m := by
  classical
  ext e
  by_cases he : d = e
  · subst e
    rw [DirectSum.of_eq_same]
    exact DirectSum.decompose_of_mem_same 𝓜 m.property
  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm he)]
    exact DirectSum.decompose_of_mem_ne 𝓜 m.property he

instance decomposition : DirectSum.Decomposition (piece 𝓜 K hK) := by
  classical
  have hr : (decompositionMap 𝓜 K hK).comp (DirectSum.coeAddMonoidHom (piece 𝓜 K hK)) =
      AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro d m
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
      AddMonoidHom.id_apply, decompositionMap_homogeneous]
  apply DirectSum.Decomposition.ofAddHom (piece 𝓜 K hK) (decompositionMap 𝓜 K hK) ?_ hr
  apply AddMonoidHom.ext
  intro m
  apply decompositionMap_injective 𝓜 K hK
  exact DFunLike.congr_fun hr (decompositionMap 𝓜 K hK m)

variable {σR : Type*} [SetLike σR R] [AddSubgroupClass σR R]
  (𝒜 : ℤ → σR) [SetLike.GradedSMul 𝒜 𝓜]

instance gradedSMul : SetLike.GradedSMul 𝒜 (piece 𝓜 K hK) where
  smul_mem := by
    intro i d a m ha hm
    change a • (m : M) ∈ 𝓜 (i + d)
    exact SetLike.GradedSMul.smul_mem ha (show (m : M) ∈ 𝓜 d from hm)

end
end PiExponent.HomogeneousSubmoduleGrading

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_MixedSlopePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open Polynomial Finset

def mixedSlopePolynomial (d : ℕ) (c : ℕ → ℝ) : Polynomial ℝ :=
  ∑ k ∈ range (d+1), C ((d.choose k : ℝ) * c k) * X^k

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_NatToIntGrading
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NatToIntGrading
noncomputable section
open DirectSum
variable {M σM : Type*} [AddCommGroup M] [SetLike σM M] [AddSubgroupClass σM M]
  (𝓜 : ℕ → σM) [DirectSum.Decomposition 𝓜]

def piece : ℤ → AddSubgroup M
  | .ofNat n => AddSubgroup.ofClass (𝓜 n)
  | .negSucc _ => ⊥

def component (m : M) : ∀ d, piece 𝓜 d
  | .ofNat n => ⟨DirectSum.decompose 𝓜 m n, (DirectSum.decompose 𝓜 m n).property⟩
  | .negSucc _ => 0

def support (m : M) : Finset ℤ := by
  classical
  exact (DirectSum.decompose 𝓜 m).support.image (fun n : ℕ => (n : ℤ))

theorem component_eq_zero_of_not_mem (m : M) (d : ℤ) (hd : d ∉ support 𝓜 m) :
    component 𝓜 m d = 0 := by
  classical
  cases d with
  | ofNat n =>
      apply Subtype.ext
      have hn : n ∉ (DirectSum.decompose 𝓜 m).support := by
        intro hn
        exact hd (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
      change (DirectSum.decompose 𝓜 m n : M) = 0
      rw [DFinsupp.notMem_support_iff.mp hn]
      rfl
  | negSucc n => rfl

def decompositionMap : M →+ ⨁ d, piece 𝓜 d where
  toFun m := DFinsupp.mk' (component 𝓜 m) (Trunc.mk
    ⟨(support 𝓜 m).val, fun d => by
      classical
      by_cases hd : d ∈ support 𝓜 m
      · exact Or.inl hd
      · exact Or.inr (component_eq_zero_of_not_mem 𝓜 m d hd)⟩)
  map_zero' := by
    apply DFinsupp.ext
    intro d
    apply Subtype.ext
    cases d with
    | ofNat n =>
        change (DirectSum.decompose 𝓜 (0 : M) n : M) = 0
        rw [DirectSum.decompose_zero]
        rfl
    | negSucc n => rfl
  map_add' m n := by
    apply DFinsupp.ext
    intro d
    apply Subtype.ext
    cases d with
    | ofNat k =>
        change (DirectSum.decompose 𝓜 (m + n) k : M) =
          (DirectSum.decompose 𝓜 m k : M) + (DirectSum.decompose 𝓜 n k : M)
        rw [DirectSum.decompose_add]
        rfl
    | negSucc k => exact (zero_add (0 : M)).symm

@[simp] theorem decompositionMap_nat (m : M) (n : ℕ) :
    (decompositionMap 𝓜 m (n : ℤ) : M) = (DirectSum.decompose 𝓜 m n : M) := rfl

theorem decompositionMap_injective : Function.Injective (decompositionMap 𝓜) := by
  intro m n h
  apply (DirectSum.decompose 𝓜).injective
  ext k
  exact congrArg (fun z : ⨁ d, piece 𝓜 d => (z (k : ℤ) : M)) h

theorem decompositionMap_homogeneous (d : ℤ) (m : piece 𝓜 d) :
    decompositionMap 𝓜 m.val = DirectSum.of (fun d => piece 𝓜 d) d m := by
  classical
  cases d with
  | negSucc n =>
      have hm : m = 0 := Subtype.ext m.property
      subst m
      simp
  | ofNat n =>
      apply DFinsupp.ext
      intro e
      apply Subtype.ext
      cases e with
      | negSucc k =>
          rw [DirectSum.of_eq_of_ne _ _ _ (show Int.negSucc k ≠ Int.ofNat n from by intro h; cases h)]
          rfl
      | ofNat k =>
          by_cases hnk : n = k
          · subst k
            rw [DirectSum.of_eq_same]
            exact DirectSum.decompose_of_mem_same 𝓜 m.property
          · rw [DirectSum.of_eq_of_ne _ _ _ (show Int.ofNat k ≠ Int.ofNat n from
              fun h => hnk (Int.ofNat.inj h).symm)]
            exact DirectSum.decompose_of_mem_ne 𝓜 m.property hnk

instance decomposition : DirectSum.Decomposition (piece 𝓜) := by
  have hr : (decompositionMap 𝓜).comp (DirectSum.coeAddMonoidHom (piece 𝓜)) = AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro d m
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
      AddMonoidHom.id_apply, decompositionMap_homogeneous]
  apply DirectSum.Decomposition.ofAddHom (piece 𝓜) (decompositionMap 𝓜) ?_ hr
  apply AddMonoidHom.ext
  intro m
  apply decompositionMap_injective 𝓜
  exact DFunLike.congr_fun hr (decompositionMap 𝓜 m)

@[simp] theorem decompose_nat (m : M) (n : ℕ) :
    (DirectSum.decompose (piece 𝓜) m (n : ℤ) : M) = (DirectSum.decompose 𝓜 m n : M) := rfl

@[simp] theorem decompose_negSucc (m : M) (n : ℕ) :
    (DirectSum.decompose (piece 𝓜) m (.negSucc n) : M) = 0 := rfl

section Scalars
variable {R σR : Type*} [Ring R] [Module R M] [SetLike σR R] [AddSubgroupClass σR R]
  (𝒜 : ℕ → σR) [SetLike.GradedSMul 𝒜 𝓜]

instance gradedSMul : SetLike.GradedSMul (piece 𝒜) (piece 𝓜) where
  smul_mem := by
    intro i j a m ha hm
    cases i with
    | negSucc n =>
        have ha' : a = 0 := ha
        rw [ha', zero_smul]
        exact zero_mem _
    | ofNat n =>
        cases j with
        | negSucc k =>
            have hm' : m = 0 := hm
            rw [hm', smul_zero]
            exact zero_mem _
        | ofNat k =>
            change a • m ∈ 𝓜 (n + k)
            exact SetLike.GradedSMul.smul_mem (show a ∈ 𝒜 n from ha) (show m ∈ 𝓜 k from hm)
end Scalars

section Ring
variable {R σR : Type*} [Ring R] [SetLike σR R] [AddSubgroupClass σR R]
  (𝒜 : ℕ → σR) [SetLike.GradedMonoid 𝒜]

instance gradedMonoid : SetLike.GradedMonoid (piece 𝒜) where
  one_mem := by
    change (1 : R) ∈ 𝒜 0
    exact SetLike.GradedOne.one_mem
  mul_mem := by
    intro i j a b ha hb
    cases i with
    | negSucc n =>
        have ha' : a = 0 := ha
        rw [ha', zero_mul]
        exact zero_mem _
    | ofNat n =>
        cases j with
        | negSucc k =>
            have hb' : b = 0 := hb
            rw [hb', mul_zero]
            exact zero_mem _
        | ofNat k =>
            change a * b ∈ 𝒜 (n + k)
            exact SetLike.mul_mem_graded (show a ∈ 𝒜 n from ha) (show b ∈ 𝒜 k from hb)
end Ring

end
end PiExponent.NatToIntGrading

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Statement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

def IntegerEventualLowerBound (x : ℝ) : Prop :=
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
    ∀ (p q : ℤ), Q ≤ q → (q : ℝ) ^ (-ν) ≤ |x - (p : ℝ) / (q : ℝ)|

end PiExponent

end OAI
end


