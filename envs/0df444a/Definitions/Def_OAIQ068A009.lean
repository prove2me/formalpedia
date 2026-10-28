-- Prove2me | Definitions.Def_OAIQ068A009
-- name    : OAIQ068A009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:40:24.861289+00:00
-- url     : https://prove2.me/theorems/52128742-f826-41ee-9cc8-6f00416d6da0
-- title:
--   Definitions bundle OAIQ068A009 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 117 declarations of OpenAI's Lean: 61 definitions, 3 instances and 53 theorems. The definitions and types are `OAI.PiExponent.ProperAmpleFiniteDimension.projectivePrime`, `OAI.PiExponent.RamifiedLocalLength.basis_atPrime_of_unique_fibre`, `OAI.PiExponent.ReducedComponentAmple.closedBaseChange`, `OAI.PiExponent.ReesLocalizedIntersections.coefficientProduct`, `OAI.PiExponent.ReesLocalizedIntersections.coefficientRestriction`, `OAI.PiExponent.ReesSheafCechRecovery.groupAddZero`, `OAI.PiExponent.ReesSheafCechRecovery.groupAddZeroClass`, `OAI.PiExponent.RowTranslation.multiIndex`, `OAI.PiExponent.RowTranslation.shift`, `OAI.PiExponent.RowTranslation.shiftCoefficient`, `OAI.PiExponent.SeparablePointLength.coefficientBaseChangeEquiv`, `OAI.PiExponent.TaylorRectangular.derivativeWord`, `OAI.PiExponent.WeightedBezout.translation`, `OAI.PiExponent.WeightedBezout.translationEquiv`, `OAI.PiExponent.approximatePeriod`, `OAI.PiExponent.extendDerivation`, `OAI.PiExponent.holomorphicError`, `OAI.PiExponent.natWeightedSimplex`, `OAI.PiExponent.normalizedLogWeights`, `OAI.PiExponent.ratFuncDerivative`, `OAI.PiExponent.residueRectangle`, `OAI.PiExponent.unweightedSimplex`, `OAI.PiExponentApprox.HasWeightedDegreeLE`, `OAI.PiExponentApprox.geometricDegreeWeight`, `OAI.PiExponentApprox.geometricJetWeight`, `OAI.PiExponentApprox.monomialWeight`, `OAI.PiExponentJets.EndomorphismEuler.cokernelMap`, `OAI.PiExponentJets.EndomorphismEuler.connecting`, `OAI.PiExponentJets.EndomorphismEuler.kernelMap`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.LocalPolynomialResidue`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.RemainingCoordinate`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateBasisRenaming`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateIndexSplitting`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateSplitPrime`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.residueCoordinate`, `OAI.PiExponentJets.RegularSequenceQuotientTail.quotientTailEquiv`, `OAI.PiExponentJets.W18.augmentationRangeShortComplex`, `OAI.PiExponentJets.W18.differentialRangeShortComplex`, `OAI.PiExponentJets.W18.regularSequenceDifferentialRange`, `OAI.PiExponentJets.W22.HomogeneousPolynomialIdeal` and 21 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_ClosedAmpleBaseChange`, `PiExponent_Ampleness_ProperAmpleFiniteDimension`, `PiExponent_Ampleness_ReesLocalizedIntersections`, `PiExponent_Ampleness_ReesProductChart`, `PiExponent_Ampleness_ReesProductRestriction`, `PiExponent_Analysis_AlgebraicLogarithmicObstruction`, `PiExponent_Analysis_Collision`, `PiExponent_Analysis_ColonSeriesTelescope`, `PiExponent_Analysis_HilbertSeries`, `PiExponent_Approximation_ApproximationCenters`, `PiExponent_Approximation_RowTranslation`, `PiExponent_Approximation_SuccessiveApproximations`, `PiExponent_Approximation_WeightSeparation`, `PiExponent_Cohomology_EndomorphismEulerAdditivity`, `PiExponent_Cohomology_ReesSheafCechRecovery`, `PiExponent_Geometry_ConePrimeProperties`, `PiExponent_Jets_RectangularCotangent`, `PiExponent_Jets_TaylorRectangular`, `PiExponent_LocalAlgebra_ConeComplex`, `PiExponent_LocalAlgebra_CoordinateBasisSplitting`, `PiExponent_LocalAlgebra_HilbertDenominatorReduction`, `PiExponent_LocalAlgebra_HilbertZeroVariables`, `PiExponent_LocalAlgebra_KoszulFiniteFree`, `PiExponent_LocalAlgebra_PositiveDimensionalHilbert`, `PiExponent_LocalAlgebra_QuotientSections`, `PiExponent_LocalAlgebra_RamifiedLocalization`, `PiExponent_LocalAlgebra_RegularCutHistory`, `PiExponent_LocalAlgebra_RegularSequenceExtObstruction`, `PiExponent_LocalAlgebra_RegularSequenceQuotientTail`, `PiExponent_LocalAlgebra_RegularSequenceResolution`, `PiExponent_LocalAlgebra_RetainedIntersectionCycles`, `PiExponent_LocalAlgebra_RetainedMinimalPrimeFamily`, `PiExponent_LocalAlgebra_SeparablePointLength`, `PiExponent_LocalAlgebra_StabilizedColonPowers`, `PiExponent_LocalAlgebra_WeightedBezout`, `PiExponent_Polynomials_CoefficientLocalizationMaximal`, `PiExponent_Polynomials_CoordinateQuotientGrading`, `PiExponent_Polynomials_HilbertPolynomialBase`, `PiExponent_Polynomials_HomogeneousHilbertExistence`, `PiExponent_Polynomials_HomogeneousPrimeFactor`, `PiExponent_Polynomials_HomogeneousSections`, `PiExponent_Polynomials_PolynomialFrameDegree`, `PiExponent_Polynomials_PolynomialLocalResidueResolution`, `PiExponent_Polynomials_SimplexCounting`, `PiExponent_Polynomials_SimplexUnweighted`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A018` and `OAIQ068A019`; the statements `OAI_PiExponentJets_W22_ActualRegularCutHistory_local_length_bound`, `OAI_PiExponentSiegelAux_W30_iterateScalarCones_dual_low_exact`, `OAI.PiExponentSiegelAux.W30.iterateScalarCones_dual_low_exact_q68`, `OAI_PiExponent_CurveDerivativeVanishing_logarithmic_words_vanish` and `OAI.PiExponent.CurveDerivativeVanishing.logarithmic_words_vanish_q68`; the proofs of `OAI_PiExponent_CurveDerivativeVanishing_logarithmic_words_vanish`, `OAI.PiExponent.CurveDerivativeVanishing.logarithmic_words_vanish_q68`, `OAI_PiExponent_LiteralAnalytic_analyticAggregate`, `OAI.PiExponent.LiteralAnalytic.analyticAggregate_q68`, `OAI_PiExponent_LiteralAnalytic_norm_actual_summand_le`, `OAI.PiExponent.LiteralAnalytic.norm_actual_summand_le_q68`, `OAI_PiExponent_WeightedCurveRigidity_ordinary_coordinate_constant`, `OAI.PiExponent.WeightedCurveRigidity.ordinary_coordinate_constant_q68`, `OAI_PiExponent_exists_admissible_parameters`, `OAI.PiExponent.exists_admissible_parameters_q68`, `OAI_PiExponent_piEventualLowerBound_of_globalInterpolation` and `OAI.PiExponent.piEventualLowerBound_of_globalInterpolation_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ClosedAmpleBaseChange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ReducedComponentAmple
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable {X Y : Scheme.{0}}

def closedBaseChange (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).subscheme ⟶ I.subscheme :=
  (I.comapIso f).hom ≫ pullback.snd f I.subschemeι

instance closedBaseChange_isClosedImmersion (I : X.IdealSheafData)
    (f : Y ⟶ X) [IsClosedImmersion f] : IsClosedImmersion (closedBaseChange I f) := by
  unfold closedBaseChange
  infer_instance

@[reassoc]
theorem closedBaseChange_condition (I : X.IdealSheafData) (f : Y ⟶ X) :
    closedBaseChange I f ≫ I.subschemeι = (I.comap f).subschemeι ≫ f := by
  simp only [closedBaseChange, Category.assoc, ← pullback.condition,
    Scheme.IdealSheafData.comapIso_hom_fst_assoc]

end PiExponent.ReducedComponentAmple

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ProperAmpleFiniteDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProperAmpleFiniteDimension
open AlgebraicGeometry CategoryTheory TopologicalSpace

section Graded
variable {A S : Type*} [CommRing A] [SetLike S A] [AddSubmonoidClass S A]
    (G : ℕ → S) [GradedRing G]

def projectivePrime : ProjectiveSpectrum G → PrimeSpectrum A :=
  fun x => ⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩

end Graded

end PiExponent.ProperAmpleFiniteDimension

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesLocalizedIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesLocalizedIntersections
noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

def coefficientProduct (s : Finset J) : R := ∏ j ∈ s, (a j).val

def coefficientRestriction {s t : Finset J} (hst : s ⊆ t) :
    Localization.Away (coefficientProduct I a s) →+*
      Localization.Away (coefficientProduct I a t) :=
  IsLocalization.Away.lift (coefficientProduct I a s)
    (IsLocalization.Away.isUnit_of_dvd (coefficientProduct I a t) (by
      exact Finset.prod_dvd_prod_of_subset s t _ hst))

omit [Fintype J] [DecidableEq J] in
@[simp] theorem coefficientRestriction_algebraMap {s t : Finset J} (hst : s ⊆ t) (r : R) :
    coefficientRestriction I a hst (algebraMap R (Localization.Away (coefficientProduct I a s)) r) =
      algebraMap R (Localization.Away (coefficientProduct I a t)) r :=
  IsLocalization.Away.lift_eq _ _ _

end
end PiExponent.ReesLocalizedIntersections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesProductChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesProductChart
noncomputable section
open PiExponent.ReesLocalizedIntersections
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

variable {s : Finset J} {j : J} (hj : j ∈ s)
include hj

omit [Fintype J] in
theorem coefficientProduct_eq_pivot :
    coefficientProduct I a s = (a j).val * coefficientProduct I a (s.erase j) := by
  exact (Finset.mul_prod_erase s (fun i => (a i).val) hj).symm

end
end PiExponent.ReesProductChart

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesProductRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesProductRestriction
noncomputable section
open PiExponent.ReesLocalizedIntersections PiExponent.ReesProductChart
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

omit [Fintype J] in
theorem coefficientProduct_factor {s t : Finset J} (hst : s ⊆ t) :
    coefficientProduct I a t = coefficientProduct I a s * coefficientProduct I a (t \ s) := by
  exact (Finset.prod_sdiff hst).symm.trans (mul_comm _ _)

end
end PiExponent.ReesProductRestriction

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_AlgebraicLogarithmicObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open KaehlerDifferential
open scoped TensorProduct Polynomial nonZeroDivisors IntermediateField

def extendDerivation
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyEtale S T]
    (d : Derivation R S S) : Derivation R T T :=
  ((LinearMap.liftBaseChange T ((Algebra.linearMap S T).comp d.liftKaehlerDifferential)).comp
    (tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer (D R T)

def ratFuncDerivative {K : Type*} [Field K] : Derivation K (RatFunc K) (RatFunc K) := by
  letI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (K[X]⁰)
  exact extendDerivation Polynomial.derivative'

end PiExponent

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

section PolynomialShift
variable {σ R : Type*} [CommSemiring R]

noncomputable def shift (c : σ → R) : MvPolynomial σ R →+* MvPolynomial σ R :=
  eval₂Hom C (fun i => X i + C (c i))

@[simp] theorem shift_C (c : σ → R) (r : R) : shift c (C r) = C r := by
  simp [shift]

@[simp] theorem shift_X (c : σ → R) (i : σ) : shift c (X i) = X i + C (c i) := by
  simp [shift]

@[simp] theorem shift_zero (p : MvPolynomial σ R) : shift (fun _ => 0) p = p := by
  have h : shift (fun _ : σ => (0 : R)) = RingHom.id _ := by
    ext r i <;> simp
  exact DFunLike.congr_fun h p

noncomputable def shiftCoefficient (c : σ → R) (β a : σ →₀ ℕ) : R :=
  (shift c (monomial a 1)).coeff β

end PolynomialShift

section FiniteExpansion
variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]

noncomputable def multiIndex (a : σ → ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm a

omit [DecidableEq σ] in
@[simp] theorem multiIndex_apply (a : σ → ℕ) (i : σ) : multiIndex a i = a i := by
  simp [multiIndex]

end FiniteExpansion

end PiExponent.RowTranslation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_SimplexUnweighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent

def unweightedSimplex (d N : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (N + 1))).filter
    (fun a => ∑ i, a i ≤ N)

@[simp] theorem mem_unweightedSimplex {d N : ℕ} {a : Fin d → ℕ} :
    a ∈ unweightedSimplex d N ↔ ∑ i, a i ≤ N := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
    omega

open Filter Topology Asymptotics

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_SimplexCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent

def natWeightedSimplex {d : ℕ} (w : Fin d → ℕ) (N : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (N + 1))).filter
    (fun a => ∑ i, w i * a i ≤ N)

def residueRectangle {d : ℕ} (w : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (w i))

@[simp] theorem mem_residueRectangle {d : ℕ} {w r : Fin d → ℕ} :
    r ∈ residueRectangle w ↔ ∀ i, r i < w i := by
  simp [residueRectangle, Fintype.mem_piFinset]

@[simp] theorem card_residueRectangle {d : ℕ} (w : Fin d → ℕ) :
    (residueRectangle w).card = ∏ i, w i := by
  simp [residueRectangle, Fintype.card_piFinset]

open Filter Topology

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_Collision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology
open Filter

namespace PiExponent

noncomputable def holomorphicError (K : ℕ) (w0 v0 wstar : ℝ) : ℝ :=
  100 * K / w0 + Real.log 2 / v0 + Real.log (200 * K) / wstar

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

variable {k σ : Type*} [Field k] [Finite σ]

theorem finite_exponents_of_degree (n : ℕ) :
    {d : σ →₀ ℕ | d.degree = n}.Finite :=
  (Finsupp.finite_of_degree_le n).subset (fun _ h => le_of_eq h)

noncomputable instance homogeneousSection_finite (n : ℕ) :
    Module.Finite k (MvPolynomial.homogeneousSubmodule σ k n) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  let : Fintype {d : σ →₀ ℕ | d.degree = n} :=
    (finite_exponents_of_degree n).fintype
  exact Module.Finite.equiv
    (AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k)
      {d : σ →₀ ℕ | d.degree = n}).symm

theorem homogeneousSection_finrank (n : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule σ k n) =
      Nat.card {d : σ →₀ ℕ | d.degree = n} := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  let : Fintype {d : σ →₀ ℕ | d.degree = n} :=
    (finite_exponents_of_degree n).fintype
  calc
    _ = Module.finrank k ({d : σ →₀ ℕ | d.degree = n} →₀ k) :=
      (AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k)
        {d : σ →₀ ℕ | d.degree = n}).finrank_eq
    _ = Nat.card {d : σ →₀ ℕ | d.degree = n} := by
      simp only [Module.finrank_finsupp_self, Nat.card_eq_fintype_card]

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_QuotientSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def quotientSection (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Submodule k (MvPolynomial σ k ⧸ I) :=
  (MvPolynomial.homogeneousSubmodule σ k n).map (Ideal.Quotient.mkₐ k I).toLinearMap

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_HilbertSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def sectionHilbertSeries (I : Ideal (MvPolynomial σ k)) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (Module.finrank k (quotientSection I n) : ℤ))

omit [Finite σ] in
@[simp] theorem coeff_sectionHilbertSeries (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    PowerSeries.coeff n (sectionHilbertSeries I) =
      (Module.finrank k (quotientSection I n) : ℤ) :=
  PowerSeries.coeff_mk _ _

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousPrimeFactor
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem homogeneous_colon_singleton
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} {f : MvPolynomial σ k} (hf : f.IsHomogeneous d) :
    (I.colon {f}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  intro n a ha
  apply Submodule.mem_colon_singleton.mpr
  have haf : a * f ∈ I := by simpa only [smul_eq_mul] using
    (Submodule.mem_colon_singleton.mp ha)
  have h := hI (n + d) haf
  rw [DirectSum.coe_decompose_mul_add_of_right_mem
    (MvPolynomial.homogeneousSubmodule σ k) hf] at h
  exact h

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_ColonSeriesTelescope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k]

noncomputable def iteratedColon (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k) :
    ℕ → Ideal (MvPolynomial σ k)
  | 0 => I
  | n+1 => (iteratedColon I f n).colon {f}

@[simp] theorem iteratedColon_zero (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k) :
    iteratedColon I f 0 = I := rfl

@[simp] theorem iteratedColon_succ (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k)
    (n : ℕ) : iteratedColon I f (n+1) = (iteratedColon I f n).colon {f} := rfl

theorem iteratedColon_homogeneous (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    (iteratedColon I f n).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  induction n with
  | zero => exact hI
  | succ n ih => exact PiExponentJets.W22.homogeneous_colon_singleton _ ih hf

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ApproximationCenters
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

noncomputable def approximatePeriod (p : ℤ) (q : ℕ) : ℂ :=
  2 * Complex.I * (p : ℂ) / (q : ℂ)

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SuccessiveApproximations
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

noncomputable def normalizedLogWeights (q : ℕ → ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (Nat.ceil (Real.log (q n)) : ℝ)

@[simp] theorem normalizedLogWeights_zero (q : ℕ → ℕ) :
    normalizedLogWeights q 0 = 1 := rfl

@[simp] theorem normalizedLogWeights_succ (q : ℕ → ℕ) (n : ℕ) :
    normalizedLogWeights q (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ) := rfl

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightSeparation
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox

noncomputable section

def geometricDegreeWeight (w0 : ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then w0 else x i

def geometricJetWeight (v0 theta : ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then v0 else x i / theta

end
end PiExponentApprox

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EndomorphismEulerAdditivity
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.EndomorphismEuler

section InducedMaps

variable {A M N : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

def kernelMap (u : M →ₗ[A] M) (v : N →ₗ[A] N) (f : M →ₗ[A] N)
    (comm : f.comp u = v.comp f) : LinearMap.ker u →ₗ[A] LinearMap.ker v :=
  (f.domRestrict (LinearMap.ker u)).codRestrict (LinearMap.ker v) (by
    intro x
    change v (f x) = 0
    rw [← show f (u x) = v (f x) from DFunLike.congr_fun comm (x : M),
      show u x = 0 from x.property, map_zero])

@[simp] theorem kernelMap_apply (u : M →ₗ[A] M) (v : N →ₗ[A] N)
    (f : M →ₗ[A] N) (comm : f.comp u = v.comp f) (x : LinearMap.ker u) :
    (kernelMap u v f comm x : N) = f x := rfl

def cokernelMap (u : M →ₗ[A] M) (v : N →ₗ[A] N) (f : M →ₗ[A] N)
    (comm : f.comp u = v.comp f) :
    (M ⧸ LinearMap.range u) →ₗ[A] (N ⧸ LinearMap.range v) :=
  Submodule.mapQ (LinearMap.range u) (LinearMap.range v) f (by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, (DFunLike.congr_fun comm y).symm⟩)

@[simp] theorem cokernelMap_mk (u : M →ₗ[A] M) (v : N →ₗ[A] N)
    (f : M →ₗ[A] N) (comm : f.comp u = v.comp f) (x : M) :
    cokernelMap u v f comm ((LinearMap.range u).mkQ x) =
      (LinearMap.range v).mkQ (f x) := rfl

end InducedMaps

section ActualSnake

variable {A M₁ M₂ M₃ : Type*} [CommRing A]
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

variable (u₁ : M₁ →ₗ[A] M₁) (u₂ : M₂ →ₗ[A] M₂) (u₃ : M₃ →ₗ[A] M₃)
  (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hExact : Function.Exact f g)
  (hleft : f.comp u₁ = u₂.comp f) (hright : g.comp u₂ = u₃.comp g)
  (hf : Function.Injective f) (hg : Function.Surjective g)

noncomputable def connecting :
    LinearMap.ker u₃ →ₗ[A] (M₁ ⧸ LinearMap.range u₁) :=
  SnakeLemma.δ' u₁ u₂ u₃ f g hExact f g hExact hleft hright
    (LinearMap.ker u₃).subtype (LinearMap.exact_subtype_ker_map u₃)
    (LinearMap.range u₁).mkQ (LinearMap.exact_map_mkQ_range u₁) hg hf

end ActualSnake

end PiExponentJets.EndomorphismEuler

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesSheafCechRecovery
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesSheafCechRecovery
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance 1001] AddCommGroup.toAddCommMonoid
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

@[instance_reducible] def groupAddZero {A : Type*} (G : AddCommGroup A) : AddZero A := by
  letI := G
  infer_instance

@[instance_reducible] def groupAddZeroClass {A : Type*} (G : AddCommGroup A) : AddZeroClass A := by
  letI := G
  infer_instance

end
end PiExponent.ReesSheafCechRecovery

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ConePrimeProperties
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSiegel.W17.ConeLocalLength

attribute [local instance] MvPolynomial.gradedAlgebra

section General

variable {A B : Type*} [CommRing A] [CommRing B]

theorem minimalPrime_isHomogeneous {k σ : Type*} [CommRing k]
    (I Q : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : Q ∈ I.minimalPrimes) :
    Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := k)
  let C := Q.homogeneousCore (MvPolynomial.homogeneousSubmodule σ k)
  have hIC : I ≤ C.toIdeal := by
    rw [← hI.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hQ.1.2
  have hCQ : C.toIdeal ≤ Q := Ideal.toIdeal_homogeneousCore_le _ _
  have hQC : Q ≤ C.toIdeal := hQ.2 ⟨hQ.1.1.homogeneousCore, hIC⟩ hCQ
  have heq : C.toIdeal = Q := le_antisymm hCQ hQC
  exact heq ▸ C.isHomogeneous

end General

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_RectangularCotangent
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentApprox.TransverseMultiplicity

open MvPowerSeries

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

omit [Fintype σ] [DecidableEq σ] in
theorem rectangularPositive (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) : ∀ i, 0 < n i :=
  fun i => lt_of_lt_of_le (by norm_num) (hn i)

omit [Fintype σ] [DecidableEq σ] in

theorem firstCoeff_mul (f g : MvPowerSeries σ K) (i : σ) :
    coeff (Finsupp.single i 1) (f * g) =
      constantCoeff f * coeff (Finsupp.single i 1) g +
        constantCoeff g * coeff (Finsupp.single i 1) f := by
  have hh := congrArg (constantCoeff : MvPowerSeries σ K →+* K)
    ((MvPowerSeries.pderiv _ i).leibniz f g)
  simpa only [smul_eq_mul, map_add, map_mul,
    ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add,
    Finsupp.zero_apply, Nat.cast_zero, zero_add, mul_one] using hh

end PiExponentApprox.TransverseMultiplicity

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialFrameDegree
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox

noncomputable section

open MvPolynomial

def monomialWeight {m : ℕ} (w : Fin (m + 1) → ℝ)
    (d : Fin (m + 1) →₀ ℕ) : ℝ :=
  ∑ i, (d i : ℝ) * w i

def HasWeightedDegreeLE {m : ℕ} (w : Fin (m + 1) → ℝ) (N : ℝ)
    (p : MvPolynomial (Fin (m + 1)) ℂ) : Prop :=
  ∀ d ∈ p.support, monomialWeight w d ≤ N

end

end PiExponentApprox

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_TaylorRectangular
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.TaylorRectangular

open scoped BigOperators
open PiExponentApprox

def derivativeWord {ι : Type*} : (k : ℕ) → (Fin k → ι) → (Fin k →₀ ℕ) → List ι
  | 0, _, _ => []
  | k+1, B, α => derivativeWord k (fun i => B i.succ) α.tail ++ List.replicate (α 0) (B 0)

end PiExponent.TaylorRectangular

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularSequenceResolution
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30

variable {R X Y Z W Q : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable [AddCommGroup W] [AddCommGroup Q]
variable [Module R X] [Module R Y] [Module R Z] [Module R W] [Module R Q]

def coneDifferential (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) :
    (X × Y) →ₗ[R] (Y × Z) :=
  ((f.comp (LinearMap.fst R X Y)) + r • LinearMap.snd R X Y).prod
    (-(g.comp (LinearMap.snd R X Y)))

@[simp] theorem coneDifferential_apply (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (r : R) (x : X) (y : Y) :
    coneDifferential f g r (x, y) = (f x + r • y, -g y) := rfl

def coneBottom (g : Y →ₗ[R] Z) (r : R) : (Y × Z) →ₗ[R] Z :=
  g.comp (LinearMap.fst R Y Z) + r • LinearMap.snd R Y Z

@[simp] theorem coneBottom_apply (g : Y →ₗ[R] Z) (r : R) (y : Y) (z : Z) :
    coneBottom g r (y, z) = g y + r • z := rfl

theorem coneDifferential_comp (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : Z →ₗ[R] W) (r : R) (hgf : g.comp f = 0) (hhg : h.comp g = 0) :
    (coneDifferential g h r).comp (coneDifferential f g r) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change g (f x.1 + r • x.2) + r • (-g x.2) = 0
    have hz : g (f x.1) = 0 := LinearMap.congr_fun hgf x.1
    simp [map_add, map_smul, hz]
  · change -h (-g x.2) = 0
    have hz : h (g x.2) = 0 := LinearMap.congr_fun hhg x.2
    simp [hz]

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ConeComplex
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
open CategoryTheory

universe u
variable {R : Type u} [CommRing R]

lemma coneBottom_comp {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup Z] [Module R X] [Module R Y] [Module R Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) (hgf : g.comp f = 0) :
    (coneBottom g r).comp (coneDifferential f g r) = 0 := by
  apply LinearMap.ext
  intro xy
  have hz : g (f xy.1) = 0 := LinearMap.congr_fun hgf xy.1
  change g (f xy.1 + r • xy.2) + r • (-g xy.2) = 0
  simp [map_add, map_smul, hz]

def scalarConeObject (C : ChainComplex (ModuleCat.{u} R) ℕ) : ℕ → ModuleCat.{u} R
  | 0 => C.X 0
  | n + 1 => ModuleCat.of R (C.X (n + 1) × C.X n)

def scalarConeMap (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) :
    ∀ n, scalarConeObject C (n + 1) ⟶ scalarConeObject C n
  | 0 => ModuleCat.ofHom (coneBottom (C.d 1 0).hom r)
  | n + 1 => ModuleCat.ofHom
      (coneDifferential (C.d (n + 2) (n + 1)).hom (C.d (n + 1) n).hom r)

lemma chain_linear_comp_zero (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (C.d (n + 1) n).hom.comp (C.d (n + 2) (n + 1)).hom = 0 := by
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero] using
    congrArg (fun f => f.hom) (C.d_comp_d (n + 2) (n + 1) n)

theorem scalarConeMap_comp (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (n : ℕ) :
    scalarConeMap C r (n + 1) ≫ scalarConeMap C r n = 0 := by
  cases n with
  | zero =>
    apply ModuleCat.hom_ext
    exact coneBottom_comp _ _ r (chain_linear_comp_zero C 0)
  | succ n =>
    apply ModuleCat.hom_ext
    exact coneDifferential_comp _ _ _ r
      (chain_linear_comp_zero C (n + 1)) (chain_linear_comp_zero C n)

def scalarConeComplex (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (scalarConeObject C) (scalarConeMap C r) (scalarConeMap_comp C r)

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialLocalResidueResolution
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable (K : Type*) [Field K] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

abbrev LocalPolynomialResidue := Q.ResidueField

def residueCoordinate (i : Fin n) : LocalPolynomialResidue K n Q :=
  algebraMap (MvPolynomial (Fin n) K) (LocalPolynomialResidue K n Q) (MvPolynomial.X i)

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_CoefficientLocalizationMaximal
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

section MaximalKernel
variable {F A L : Type*} [Field F] [CommRing A] [Field L]
variable [Algebra F A] [Algebra F L] [Algebra.IsAlgebraic F L]

theorem algebraic_field_kernel_isMaximal (f : A →ₐ[F] L) :
    (RingHom.ker f.toRingHom).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  exact MulEquiv.isField (Subalgebra.isField_of_algebraic f.range)
    (Ideal.quotientKerEquivRange f).toRingEquiv.toMulEquiv

end MaximalKernel

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoordinateBasisSplitting
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable {n : ℕ} {T : Type*} (j : T → Fin n) (hj : Function.Injective j)

abbrev RemainingCoordinate := {i : Fin n // i ∉ Set.range j}

def coordinateIndexSplitting : RemainingCoordinate j ⊕ T ≃ Fin n := by
  classical
  exact (Equiv.sumCongr (Equiv.refl _) (Equiv.ofInjective j hj)).trans
    ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun i : Fin n => i ∈ Set.range j)))

@[simp] theorem coordinateIndexSplitting_inr (a : T) :
    coordinateIndexSplitting j hj (Sum.inr a) = j a := rfl

@[simp] theorem coordinateIndexSplitting_symm_selected (a : T) :
    (coordinateIndexSplitting j hj).symm (j a) = Sum.inr a := by
  rw [← coordinateIndexSplitting_inr j hj a, Equiv.symm_apply_apply]

def coordinateBasisRenaming (K : Type*) [Field K] : MvPolynomial (Fin n) K ≃ₐ[K]
    MvPolynomial (RemainingCoordinate j ⊕ T) K :=
  MvPolynomial.renameEquiv K (coordinateIndexSplitting j hj).symm

variable (K : Type*) [Field K] (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]
variable (t : Set Q.ResidueField) (j : t → Fin n) (hj : Function.Injective j)
variable (hcoord : ∀ a, residueCoordinate K n Q (j a) = (a : Q.ResidueField))
variable (ht : IsTranscendenceBasis K ((↑) : t → Q.ResidueField))

abbrev coordinateSplitPrime := Q.map (coordinateBasisRenaming j hj K).toRingHom

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_HilbertDenominatorReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def colonHilbertNumerator (P : ℕ → Polynomial ℤ) (m : ℕ) : Polynomial ℤ :=
  (∑ j ∈ Finset.range m, Polynomial.X ^ j * P j) * (1 - Polynomial.X) +
    Polynomial.X ^ m * P m

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HilbertPolynomialBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

variable {σ : Type*}

noncomputable def exponentDegreeEquivSym (n : ℕ) :
    {d : σ →₀ ℕ | d.degree = n} ≃ Sym σ n := by
  classical
  exact
    { toFun := fun d => ⟨d.1.toMultiset, by
        rw [Finsupp.card_toMultiset]
        exact d.2⟩
      invFun := fun m => ⟨Multiset.toFinsupp m.1, by
        have hc := Finsupp.card_toMultiset (Multiset.toFinsupp m.1)
        rw [Multiset.toFinsupp_toMultiset] at hc
        change (Multiset.toFinsupp m.1).degree = n
        exact hc.symm.trans m.2⟩
      left_inv := fun d => Subtype.ext (Multiset.toFinsupp.apply_symm_apply d.1)
      right_inv := fun m => Subtype.ext (Multiset.toFinsupp.symm_apply_apply m.1) }

theorem card_exponents_degree [Fintype σ] (n : ℕ) :
    Nat.card {d : σ →₀ ℕ | d.degree = n} = (Fintype.card σ).multichoose n := by
  classical
  rw [Nat.card_congr (exponentDegreeEquivSym n), Nat.card_eq_fintype_card]
  exact Sym.card_sym_eq_multichoose σ n

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_HilbertZeroVariables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

variable {k σ : Type*} [Field k] [Fintype σ]

theorem quotientSection_finrank_zero_of_no_variables
    (hσ : Fintype.card σ = 0) (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.finrank k (quotientSection I (n+1)) = 0 := by
  have h := Submodule.finrank_map_le (Ideal.Quotient.mkₐ k I).toLinearMap
    (MvPolynomial.homogeneousSubmodule σ k (n+1))
  rw [homogeneousSection_finrank, card_exponents_degree, hσ,
    Nat.multichoose_zero_succ] at h
  exact Nat.eq_zero_of_le_zero h

theorem sectionHilbertSeries_no_variables
    (hσ : Fintype.card σ = 0) (I : Ideal (MvPolynomial σ k)) :
    sectionHilbertSeries I = PowerSeries.C (Module.finrank k (quotientSection I 0) : ℤ) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_sectionHilbertSeries, quotientSection_finrank_zero_of_no_variables hσ I n]
    simp only [PowerSeries.coeff_C, Nat.succ_ne_zero, ite_false, Nat.cast_zero]

theorem exists_hilbert_numerator_no_variables
    (hσ : Fintype.card σ = 0) (I : Ideal (MvPolynomial σ k)) :
    ∃ P : Polynomial ℤ, sectionHilbertSeries I =
      (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  refine ⟨Polynomial.C (Module.finrank k (quotientSection I 0) : ℤ), ?_⟩
  simpa only [hσ, PowerSeries.invOneSubPow_zero, Units.val_one, mul_one,
    Polynomial.coe_C] using sectionHilbertSeries_no_variables hσ I

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_KoszulFiniteFree
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30

universe u
variable {R : Type u} [CommRing R]

def emptyKoszulObject : ℕ → ModuleCat.{u} R
  | 0 => ModuleCat.of R R
  | _ + 1 => ModuleCat.of R (Fin 0 → R)

def emptyKoszulComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of emptyKoszulObject (fun _ => 0) (fun _ => by simp)

def iterateScalarCones (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    List R → ChainComplex (ModuleCat.{u} R) ℕ
  | [] => C
  | r :: rs => iterateScalarCones (scalarConeComplex C r) rs

def regularSequenceComplex (rs : List R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  iterateScalarCones emptyKoszulComplex rs

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PositiveDimensionalHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

noncomputable def rationalSectionHilbertSeries (I : Ideal (MvPolynomial σ k)) :
    PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) (sectionHilbertSeries I)

omit [Fintype σ] in
@[simp] theorem coeff_rationalSectionHilbertSeries
    (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    PowerSeries.coeff n (rationalSectionHilbertSeries I) =
      (Module.finrank k (quotientSection I n) : ℚ) := by
  simp [rationalSectionHilbertSeries, PowerSeries.coeff_map]

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RamifiedLocalization
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.RamifiedLocalLength

open IsLocalRing

theorem scalarLocalization_isAtPrime_of_unique_fibre
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    (Rₚ Sₚ : Type*) [CommRing Rₚ] [CommRing Sₚ]
    [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
    [Algebra S Sₚ] [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
    [Algebra R Sₚ] [Algebra Rₚ Sₚ]
    [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]
    [Algebra.IsIntegral Rₚ Sₚ]
    (hunique : ∀ Q : Ideal S, Q.IsPrime → p ≤ Q.under R → Q = P) :
    IsLocalization.AtPrime Sₚ P := by
  let M := Algebra.algebraMapSubmonoid S p.primeCompl
  have hmapmax : (P.map (algebraMap S Sₚ)).IsMaximal := by
    letI := Ideal.Quotient.field P
    exact Ideal.Quotient.maximal_of_isField _
      ((IsLocalization.AtPrime.equivQuotientMapOfIsMaximal p Sₚ P).symm.toMulEquiv.isField
        (Field.toIsField _))
  have huniqueMax : ∀ Q : Ideal Sₚ, Q.IsMaximal → Q = P.map (algebraMap S Sₚ) := by
    intro Q hQ
    let : Q.IsMaximal := hQ
    have hQP : Q.LiesOver (maximalIdeal Rₚ) :=
      (IsLocalization.AtPrime.mem_primesOver_of_isPrime Rₚ Sₚ).2
    let : Q.LiesOver (maximalIdeal Rₚ) := hQP
    have hQp : (Q.under S).LiesOver p :=
      IsLocalization.AtPrime.liesOver_comap_of_liesOver p Rₚ Q
    let : (Q.under S).LiesOver p := hQp
    have hEq : Q.under S = P :=
      hunique (Q.under S) inferInstance (Ideal.over_def (Q.under S) p).le
    calc
      Q = (Q.under S).map (algebraMap S Sₚ) := (IsLocalization.map_under M Sₚ Q).symm
      _ = P.map (algebraMap S Sₚ) := by rw [hEq]
  let : IsLocalRing Sₚ := IsLocalRing.of_unique_max_ideal
    ⟨P.map (algebraMap S Sₚ), hmapmax, huniqueMax⟩
  have hmax : maximalIdeal Sₚ = P.map (algebraMap S Sₚ) :=
    (IsLocalRing.eq_maximalIdeal hmapmax).symm
  have hcomap : (maximalIdeal Sₚ).under S = P := by
    rw [hmax]
    exact IsLocalization.AtPrime.under_map_of_isMaximal S p Sₚ P
  apply IsLocalization.of_le M P.primeCompl
  · intro x hx
    exact fun hmem => Set.disjoint_left.mp (Ideal.disjoint_primeCompl_of_liesOver P p) hx hmem
  · intro r hr
    by_contra hu
    have hm : algebraMap S Sₚ r ∈ maximalIdeal Sₚ := hu
    have hrmem : r ∈ P := by
      rw [← hcomap]
      exact hm
    exact hr hrmem

noncomputable def basis_atPrime_of_unique_fibre
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
    [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime P)]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι R S)
    (hunique : ∀ Q : Ideal S, Q.IsPrime → p ≤ Q.under R → Q = P) :
    Module.Basis ι (Localization.AtPrime p) (Localization.AtPrime P) := by
  let : Module.Finite R S := Module.Finite.of_basis b
  let T := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let : IsLocalization.AtPrime T P :=
    scalarLocalization_isAtPrime_of_unique_fibre p P (Localization.AtPrime p) T hunique
  let e : T ≃ₐ[Localization.AtPrime p] Localization.AtPrime P :=
    ((IsLocalization.algEquiv P.primeCompl T (Localization.AtPrime P)).restrictScalars R).extendScalarsOfIsLocalization
       (Localization.AtPrime p) p.primeCompl
  exact (b.localizationLocalization (Localization.AtPrime p) p.primeCompl T).map e.toLinearEquiv

end PiExponent.RamifiedLocalLength

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_StabilizedColonPowers
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W06

section ColonPowers
variable {R : Type*} [CommRing R]

@[simp] theorem colon_pow_zero (I : Ideal R) (x : R) :
    I.colon {x ^ (0 : ℕ)} = I := by
  ext a
  simp [Submodule.mem_colon_singleton, smul_eq_mul]

theorem colon_pow_succ (I : Ideal R) (x : R) (j : ℕ) :
    I.colon {x ^ (j + 1)} = (I.colon {x ^ j}).colon {x} := by
  ext a
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, pow_succ,
    mul_assoc, mul_comm, mul_left_comm]

theorem colon_powers_monotone (I : Ideal R) (x : R) :
    Monotone (fun j : ℕ => I.colon {x ^ j}) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [colon_pow_succ]
  exact Ideal.le_colon

theorem exists_colon_powers_eventually_constant [IsNoetherianRing R]
    (I : Ideal R) (x : R) :
    ∃ m : ℕ, ∀ j : ℕ, m ≤ j → I.colon {x ^ j} = I.colon {x ^ m} := by
  let chain : ℕ →o Submodule R R :=
    ⟨fun j => I.colon {x ^ j}, colon_powers_monotone I x⟩
  obtain ⟨m, hm⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) chain
  exact ⟨m, fun j hj => (hm j hj).symm⟩

theorem exists_colon_pow_stable [IsNoetherianRing R] (I : Ideal R) (x : R) :
    ∃ m : ℕ, I.colon {x ^ (m + 1)} = I.colon {x ^ m} := by
  obtain ⟨m, hm⟩ := exists_colon_powers_eventually_constant I x
  exact ⟨m, hm (m + 1) (Nat.le_succ m)⟩

end ColonPowers

attribute [local instance] MvPolynomial.gradedAlgebra

end PiExponentJets.W06

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_CoordinateQuotientGrading
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PiExponentSiegel.W08

section

open MvPolynomial

variable {k σ τ : Type*} [Field k]

noncomputable def coordinateEval : MvPolynomial (Option σ) k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun o => Option.elim o 0 MvPolynomial.X)

noncomputable def coordinateInclude : MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k :=
  MvPolynomial.rename Option.some

@[simp] theorem coordinateEval_X_none :
    coordinateEval (k := k) (σ := σ) (X none) = 0 := by simp [coordinateEval]

@[simp] theorem coordinateEval_X_some (i : σ) :
    coordinateEval (k := k) (X (some i)) = X i := by simp [coordinateEval]

@[simp] theorem coordinateEval_include (p : MvPolynomial σ k) :
    coordinateEval (coordinateInclude p) = p := by
  have h : (coordinateEval (k := k) (σ := σ)).comp coordinateInclude = AlgHom.id k _ := by
    ext i
    simp [coordinateInclude]
  exact AlgHom.congr_fun h p

end

end PiExponentSiegel.W08

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousHilbertExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W64

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type v} [Field k]

theorem iteratedColon_eq_colon_power {σ : Type u} [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k) (n : ℕ) :
    iteratedColon I f n = I.colon {f^n} := by
  induction n with
  | zero => simp only [iteratedColon_zero, PiExponentJets.W06.colon_pow_zero]
  | succ n ih => rw [iteratedColon_succ, ih, PiExponentJets.W06.colon_pow_succ]

end PiExponentJets.W64

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RetainedIntersectionCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w

def ProjectiveComponent (k : Type u) (σ : Type v) [Field k] :=
  {P : Ideal (MvPolynomial σ k) // P.IsPrime ∧
    P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) ∧
    ∃ i : σ, MvPolynomial.X i ∉ P}

namespace ProjectiveComponent

variable {k : Type u} {σ : Type v} [Field k]

theorem homogeneous (P : ProjectiveComponent k σ) :
    P.val.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := P.property.2.1

noncomputable def coordinate (P : ProjectiveComponent k σ) : σ :=
  P.property.2.2.choose

end ProjectiveComponent

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RetainedMinimalPrimeFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {k σ : Type u} [Field k] [Fintype σ]

def RetainedMinimalPrime (I T : Ideal (MvPolynomial σ k)) :=
  {Q : Ideal (MvPolynomial σ k) // Q ∈ I.minimalPrimes ∧ Q ≤ T}

namespace RetainedMinimalPrime

variable {I T : Ideal (MvPolynomial σ k)}

instance instIsPrimeMvPolynomialValIdealAndMemSetMinimalPrimesLe (Q : RetainedMinimalPrime I T) : Q.val.IsPrime := Q.property.1.1.1

noncomputable def toComponent
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (v : σ) (hv : MvPolynomial.X v ∉ T) (Q : RetainedMinimalPrime I T) :
    ProjectiveComponent k σ :=
  ⟨Q.val, Q.property.1.1.1,
    PiExponentSiegel.W17.ConeLocalLength.minimalPrime_isHomogeneous I Q.val hI Q.property.1,
    v, fun h => hv (Q.property.2 h)⟩

omit [Fintype σ] in
@[simp] theorem toComponent_val
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (v : σ) (hv : MvPolynomial.X v ∉ T) (Q : RetainedMinimalPrime I T) :
    (toComponent hI v hv Q).val = Q.val := rfl

end RetainedMinimalPrime

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularCutHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

abbrev HomogeneousPolynomialIdeal (k σ : Type u) [Field k] :=
  {I : Ideal (MvPolynomial σ k) // I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)}

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularSequenceExtObstruction
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponentJets.W18
open CategoryTheory CategoryTheory.Abelian
open PiExponentSiegelAux

variable {R : Type u} [CommRing R]

section RangeSequences
variable {L M N : Type u} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
  [Module R L] [Module R M] [Module R N]

def differentialRangeShortComplex (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (hex : LinearMap.range f = LinearMap.ker g) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (LinearMap.range f).subtype g.rangeRestrict (by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (show x.val ∈ LinearMap.ker g from hex ▸ x.property))

def augmentationRangeShortComplex (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (hex : LinearMap.range f = LinearMap.ker g) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (LinearMap.range f).subtype g (by
    apply LinearMap.ext
    intro x
    exact (show x.val ∈ LinearMap.ker g from hex ▸ x.property))

end RangeSequences

def regularSequenceDifferentialRange (rs : List R) (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (LinearMap.range ((W30.regularSequenceComplex rs).d (n + 1) n).hom)

end PiExponentJets.W18

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularSequenceQuotientTail
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.RegularSequenceQuotientTail
open RingTheory.Sequence
open scoped Pointwise

variable {R : Type*} [CommRing R]

theorem principal_image_eq_scalar_top (I : Ideal R) (r : R) :
    Submodule.map I.mkQ (Ideal.span ({r} : Set R)) = r • (⊤ : Submodule R (R ⧸ I)) := by
  have h : r • (⊤ : Ideal R) = Ideal.span ({r} : Set R) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [← h, Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ]

def quotientTailEquiv (I : Ideal R) (r : R) :
    QuotSMulTop r (R ⧸ I) ≃ₗ[R] R ⧸ (I ⊔ Ideal.span ({r} : Set R)) :=
  (Submodule.quotEquivOfEq _ _ (principal_image_eq_scalar_top I r).symm).trans
    (Submodule.quotientQuotientEquivQuotientSup I (Ideal.span ({r} : Set R)))

@[simp] theorem quotientTailEquiv_mk (I : Ideal R) (r a : R) :
    quotientTailEquiv I r (Submodule.Quotient.mk (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk (I ⊔ Ideal.span ({r} : Set R)) a := rfl

end PiExponentJets.RegularSequenceQuotientTail

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_WeightedBezout
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.WeightedBezout

open scoped BigOperators

variable {k σ τ : Type*} [Field k]

noncomputable def translation (a : σ → k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (a i) + MvPolynomial.X i)

noncomputable def translationEquiv (a : σ → k) : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  AlgEquiv.ofAlgHom (translation a) (translation (-a))
    (by ext i; simp [translation])
    (by ext i; simp [translation])

end PiExponent.WeightedBezout

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_SeparablePointLength
attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.SeparablePointLength

open IsLocalRing TensorProduct

variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]

attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable def coefficientBaseChangeEquiv :
    (MvPolynomial ι K) ⊗[K] E ≃ₐ[MvPolynomial ι K] MvPolynomial ι E :=
  Algebra.IsPushout.equiv K (MvPolynomial ι K) E (MvPolynomial ι E)

end PiExponent.SeparablePointLength

end OAI
end


