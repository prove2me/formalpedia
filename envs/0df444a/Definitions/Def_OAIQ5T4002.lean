-- Prove2me | Definitions.Def_OAIQ5T4002
-- name    : OAIQ5T4002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T12:45:34.137758+00:00
-- url     : https://prove2.me/theorems/eb830b80-949f-40fd-be9f-b1c382696880
-- title:
--   Definitions bundle OAIQ5T4002 of the split of OpenAI, The Euclidean plane cannot be colored with five colors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EuclideanFiveColor.no_proper_five_coloring`, carved from OpenAI's openai/math development (OpenAI, *The Euclidean plane cannot be colored with five colors*, OpenAI Math Release, September 23, 2026, result family 158, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 221 declarations of OpenAI's Lean: 108 definitions, 34 instances and 79 theorems. The definitions and types are `OAI.EuclideanFiveColor.WeakColoring`, `OAI.EuclideanFiveColor.angleBoundary`, `OAI.EuclideanFiveColor.angleChart`, `OAI.EuclideanFiveColor.angleChartMeasure`, `OAI.EuclideanFiveColor.angleEssential`, `OAI.EuclideanFiveColor.angularSign`, `OAI.EuclideanFiveColor.angularSum`, `OAI.EuclideanFiveColor.annulusInner`, `OAI.EuclideanFiveColor.annulusOuter`, `OAI.EuclideanFiveColor.centerDisks`, `OAI.EuclideanFiveColor.circleAverage`, `OAI.EuclideanFiveColor.circleDifferenceRatio`, `OAI.EuclideanFiveColor.circleEndpoint`, `OAI.EuclideanFiveColor.circleEndpointDeriv`, `OAI.EuclideanFiveColor.circleInverse`, `OAI.EuclideanFiveColor.circleInverseHomeo`, `OAI.EuclideanFiveColor.circleMultiplier`, `OAI.EuclideanFiveColor.circleOperator`, `OAI.EuclideanFiveColor.circleSum`, `OAI.EuclideanFiveColor.circleSumDeriv`, `OAI.EuclideanFiveColor.circleSumDerivEquiv`, `OAI.EuclideanFiveColor.circleSymbol`, `OAI.EuclideanFiveColor.circleTarget`, `OAI.EuclideanFiveColor.circleTargetDeriv`, `OAI.EuclideanFiveColor.colorError`, `OAI.EuclideanFiveColor.colorMass`, `OAI.EuclideanFiveColor.crossingGraph`, `OAI.EuclideanFiveColor.diskAnnulus`, `OAI.EuclideanFiveColor.fiveRealState`, `OAI.EuclideanFiveColor.fiveState`, `OAI.EuclideanFiveColor.fiveSupport`, `OAI.EuclideanFiveColor.fiveSupportList`, `OAI.EuclideanFiveColor.fourInterfaceSign`, `OAI.EuclideanFiveColor.fourInterfaceWord`, `OAI.EuclideanFiveColor.fourNonSingleton`, `OAI.EuclideanFiveColor.fourRealState`, `OAI.EuclideanFiveColor.fourState`, `OAI.EuclideanFiveColor.fourStateDistance`, `OAI.EuclideanFiveColor.fourStateL2`, `OAI.EuclideanFiveColor.fourSupport` and 68 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/PlaneColoring, in whole or in part: `CompactFactors_ConditionalLimits`, `CompactFactors_RelativeCenters`, `CompactFactors_Stationary`, `PlaneColoring_Accumulation`, `PlaneColoring_AngularBoundary`, `PlaneColoring_BinaryPalettes`, `PlaneColoring_BorelTransfer`, `PlaneColoring_CircleMaps`, `PlaneColoring_CircleTransport`, `PlaneColoring_Coloring`, `PlaneColoring_Compactness`, `PlaneColoring_DiskExtension`, `PlaneColoring_Exclusion`, `PlaneColoring_FiveSupport`, `PlaneColoring_FourContinuity`, `PlaneColoring_FourTransport`, `PlaneColoring_GraphCuts`, `PlaneColoring_GraphPatches`, `PlaneColoring_GraphRealization`, `PlaneColoring_HoleApproximation`, `PlaneColoring_Interfaces`, `PlaneColoring_Palettes`, `PlaneColoring_Sectors`, `PlaneColoring_States`, `PlaneColoring_Transitions`, `PlaneColoring_WeakColoring`, `PlaneSpectrum_Basic`, `PlaneSpectrum_Characters`, `PlaneSpectrum_CircleDecay`, `PlaneSpectrum_CircleOperator`, `PlaneSpectrum_ConditionalSpectrum`, `PlaneSpectrum_Energy`, `PlaneSpectrum_Ergodicity`, `PlaneSpectrum_Fourier`, `PlaneSpectrum_InvariantMean`, `PlaneSpectrum_Multipliers`, `PlaneSpectrum_RadialEnergy`, `PlaneSpectrum_Representations`, `PlaneSpectrum_SpectralMeasure`.
--
--   **Imports.** It imports the bundles `OAIQ5T4000` and `OAIQ5T4001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.EuclideanFiveColor.ae_not_binary_circle`, `OAI.EuclideanFiveColor.annulus_maps_eventually_forest`, `OAI.EuclideanFiveColor.binary_centers_separated`, `OAI.EuclideanFiveColor.fiveState_diag`, `OAI.EuclideanFiveColor.five_local_palette`, `OAI.EuclideanFiveColor.five_sequence_no_accumulation`, `OAI.EuclideanFiveColor.fourCenter_compact_finite`, `OAI.EuclideanFiveColor.fourState_group`, `OAI.EuclideanFiveColor.four_interface_word_data`, `OAI.EuclideanFiveColor.four_realState_continuity`, `OAI.EuclideanFiveColor.four_realState_positive`, `OAI.EuclideanFiveColor.four_weak_limit_identify`, `OAI.EuclideanFiveColor.fullApprox_exists`, `OAI.EuclideanFiveColor.no_five_commonInterface`, `OAI.EuclideanFiveColor.no_triangle_commonInterface`, `OAI.EuclideanFiveColor.proper_to_borel_weak`, `OAI.EuclideanFiveColor.threeCenter_compact_finite`, `OAI.EuclideanFiveColor.triangleState_flip`, `OAI.EuclideanFiveColor.triangleState_local`, `OAI.EuclideanFiveColor.triangleState_palette`, `OAI.EuclideanFiveColor.triangle_boundary_one_orbit`, `OAI.PlaneFiveColor.Spectral.ambient_uniform_precision_contradiction`, `OAI.PlaneFiveColor.Spectral.exists_terminal_factor`, `OAI.PlaneFiveColor.Spectral.finite_uniform_precision_contradiction`, `OAI.PlaneFiveColor.Spectral.massReal_difference` and `OAI.PlaneFiveColor.Spectral.radial_positive_near_zero`; the proofs of `OAI.EuclideanFiveColor.ae_not_binary_circle`, `OAI.EuclideanFiveColor.annulus_maps_eventually_forest`, `OAI.EuclideanFiveColor.binary_centers_separated`, `OAI.EuclideanFiveColor.fiveState_diag`, `OAI.EuclideanFiveColor.five_local_palette`, `OAI.EuclideanFiveColor.five_sequence_no_accumulation`, `OAI.EuclideanFiveColor.fourCenter_compact_finite`, `OAI.EuclideanFiveColor.fourState_group`, `OAI.EuclideanFiveColor.four_interface_word_data`, `OAI.EuclideanFiveColor.four_realState_continuity`, `OAI.EuclideanFiveColor.four_realState_positive`, `OAI.EuclideanFiveColor.four_weak_limit_identify`, `OAI.EuclideanFiveColor.fullApprox_exists`, `OAI.EuclideanFiveColor.no_five_commonInterface`, `OAI.EuclideanFiveColor.no_proper_five_coloring`, `OAI.EuclideanFiveColor.no_triangle_commonInterface`, `OAI.EuclideanFiveColor.proper_to_borel_weak`, `OAI.EuclideanFiveColor.threeCenter_compact_finite`, `OAI.EuclideanFiveColor.triangleState_flip`, `OAI.EuclideanFiveColor.triangleState_local`, `OAI.EuclideanFiveColor.triangleState_palette`, `OAI.EuclideanFiveColor.triangle_boundary_one_orbit`, `OAI.PlaneFiveColor.Spectral.ambient_uniform_precision_contradiction`, `OAI.PlaneFiveColor.Spectral.exists_terminal_factor`, `OAI.PlaneFiveColor.Spectral.finite_uniform_precision_contradiction`, `OAI.PlaneFiveColor.Spectral.massReal_difference` and `OAI.PlaneFiveColor.Spectral.radial_positive_near_zero`.
-- source:
--   OpenAI, The Euclidean plane cannot be colored with five colors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 158; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/PlaneColoring at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ5T4000
import Definitions.Def_OAIQ5T4001

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Basic
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral

theorem K_pow_surjective (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun u : K => u ^ n) := by
  intro u
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u.val : ℂ) (Nat.pos_of_ne_zero hn)
  have ha : IsAlgebraic ℚ z := IsAlgebraic.of_pow (Nat.pos_of_ne_zero hn) (by
    rw [hz]; exact u.property)
  have hnrm : ‖z‖ = 1 := by
    have hpow : ‖z‖ ^ n = (1 : ℝ) ^ n := by
      simp only [← norm_pow, hz, Circle.norm_coe, one_pow]
    exact (pow_left_inj₀ (norm_nonneg z) zero_le_one hn).mp hpow
  refine ⟨⟨⟨z, mem_sphere_zero_iff_norm.mpr hnrm⟩, ha⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hz

instance K_rootable : RootableBy K ℕ := rootableByOfPowLeftSurj K ℕ (fun {n} hn => K_pow_surjective n hn)

instance instIsTopologicalGroupDiscreteE : IsTopologicalGroup DiscreteE := inferInstance

instance E_countable : Countable E := by
  apply Set.Countable.to_subtype
  have heq : (algebraicClosure ℚ ℂ : Set ℂ) = {x | IsAlgebraic ℚ x} := by
    ext z; exact mem_algebraicClosure_iff
  rw [heq]
  exact Algebraic.countable ℚ ℂ

instance instCountableDiscreteE : Countable DiscreteE := inferInstanceAs (Countable E)

instance instSecondCountableTopologyD : SecondCountableTopology D :=
  ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.secondCountableTopology

theorem measurableSet_C : MeasurableSet (C : Set D) := by
  change MeasurableSet (Set.range j)
  rw [← Set.image_univ, ← Metric.iUnion_closedBall_nat (0 : ℂ), Set.image_iUnion]
  exact MeasurableSet.iUnion fun n =>
    ((isCompact_closedBall (0 : ℂ) (n : ℝ)).image continuous_j).measurableSet

/-- The source's wild-law condition; probability is provided as a measure instance. -/
def IsWild (ν : MeasureTheory.Measure D) : Prop :=
  (∀ u : K, MeasureTheory.MeasurePreserving (fun d : D => u • d) ν ν) ∧
    ν (C : Set D) = 0

theorem continuous_scalar (a : E) : Continuous (scalar a) :=
  (scaleE a).continuous_comp_left

instance instIsTopologicalGroupDiscreteF : IsTopologicalGroup DiscreteF := inferInstance
instance instMeasurableSpaceDF : MeasurableSpace DF := borel DF
instance instBorelSpaceDF : BorelSpace DF := ⟨rfl⟩

def CF : Set DF := Set.range jF

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_RelativeCenters
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

open MeasureTheory
open scoped ENNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PlaneFiveColor.Spectral
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor.RelativeCenters

instance dualStandardBorelSpace : StandardBorelSpace D := by
  have : TopologicalSpace.IsCompletelyMetrizableSpace (DiscreteE → Circle) := inferInstance
  have : PolishSpace D := ContinuousMonoidHom.isClosedEmbedding_coe.polishSpace
  infer_instance

instance dualMulDistribAction : MulDistribMulAction K D where
  smul_one u := (scalarHom (kCoeff u)).map_one
  smul_mul u d e := (scalarHom (kCoeff u)).map_mul d e

instance dualMeasurableConstSMul : MeasurableConstSMul K D where
  measurable_const_smul u := (continuous_scalar (kCoeff u)).measurable

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Characters
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate

noncomputable section
open scoped BigOperators

namespace PlaneFiveColor.Spectral
open MeasureTheory

theorem lineCharacter_measurable (a : E) (t : F) :
    Measurable (fun d : D => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ)) := by
  apply Continuous.measurable
  apply continuous_subtype_val.comp
  exact (continuous_apply (Multiplicative.ofAdd (a * ofF t))).comp
    ContinuousMonoidHom.isClosedEmbedding_coe.continuous

end PlaneFiveColor.Spectral

end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_InvariantMean
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
/-! A discrete abelian invariant mean, constructed from weighted cube
averages. Repeated group elements keep their multiplicities. -/
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
namespace PlaneFiveColor.InvariantMean

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]

/-- Complexification of the same (not a separately chosen) real mean. -/
def cmean (f : G →ᵇ ℂ) : ℂ := (mean (realPart f) : ℂ) + (mean (imagPart f) : ℂ) * Complex.I

lemma cmean_add (f h : G →ᵇ ℂ) : cmean (f+h) = cmean f + cmean h := by
  have hr : realPart (f+h) = realPart f + realPart h := by ext x; simp
  have hi : imagPart (f+h) = imagPart f + imagPart h := by ext x; simp
  simp only [cmean, hr, hi, mean_add, Complex.ofReal_add]
  ring

lemma cmean_smul (c : ℂ) (f : G →ᵇ ℂ) : cmean (c • f) = c * cmean f := by
  have hr : realPart (c • f) = c.re • realPart f - c.im • imagPart f := by
    ext x; simp [Complex.mul_re]
  have hi : imagPart (c • f) = c.re • imagPart f + c.im • realPart f := by
    ext x; simp [Complex.mul_im]
  have hs (f h : G →ᵇ ℝ) : mean (f-h) = mean f - mean h := meanCLM.map_sub f h
  apply Complex.ext <;>
    simp [cmean, hr, hi, hs, mean_smul, mean_add, Complex.mul_re, Complex.mul_im]

lemma cmean_norm_le (f : G →ᵇ ℂ) : ‖cmean f‖ ≤ 2 * ‖f‖ := by
  calc
    _ ≤ ‖(mean (realPart f) : ℂ)‖ + ‖(mean (imagPart f) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = ‖mean (realPart f)‖ + ‖mean (imagPart f)‖ := by simp
    _ ≤ ‖f‖ + ‖f‖ := add_le_add ((mean_norm_le _).trans (realPart_norm_le f))
        ((mean_norm_le _).trans (imagPart_norm_le f))
    _ = _ := by ring

def cmeanCLM : (G →ᵇ ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := cmean, map_add' := cmean_add, map_smul' := cmean_smul }
    2 (by intro f; exact cmean_norm_le f)

@[simp] lemma cmeanCLM_apply (f : G →ᵇ ℂ) : cmeanCLM f = cmean f := rfl

open MeasureTheory AddCircle

def circleMean (ρ : G →+ UnitAddCircle) : C(UnitAddCircle, ℂ) →L[ℂ] ℂ :=
  cmeanCLM.comp (LinearMap.mkContinuous
    ({ toFun := circlePull ρ
       map_add' := by intro f h; ext x; rfl
       map_smul' := by intro c f; ext x; rfl } : C(UnitAddCircle, ℂ) →ₗ[ℂ] (G →ᵇ ℂ))
    1 (by intro f; change ‖circlePull ρ f‖ ≤ 1 * ‖f‖
          simpa only [one_mul] using circlePull_norm_le ρ f))

@[simp] lemma circleMean_apply (ρ : G →+ UnitAddCircle) (f : C(UnitAddCircle, ℂ)) :
    circleMean ρ f = cmean (circlePull ρ f) := rfl

lemma mean_mono (f h : G →ᵇ ℝ) (hf : ∀ x, f x ≤ h x) : mean f ≤ mean h := by
  have hn : 0 ≤ mean (h-f) := mean_nonneg _ (fun x => sub_nonneg.mpr (hf x))
  have he : mean (h-f) = mean h - mean f := meanCLM.map_sub h f
  rw [he] at hn
  exact sub_nonneg.mp hn

lemma mean_abs_le (f h : G →ᵇ ℝ) (hf : ∀ x, |f x| ≤ h x) : |mean f| ≤ mean h := by
  apply abs_le.mpr
  constructor
  · have he : mean (-h) = -mean h := meanCLM.map_neg h
    rw [← he]
    exact mean_mono _ _ (fun x => (abs_le.mp (hf x)).1)
  · exact mean_mono _ _ (fun x => (abs_le.mp (hf x)).2)

section WeakMean
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma pairing_mean_bound (V : G →ᵇ H) (v : H) :
    |mean (pairing V v)| ≤ ‖v‖ * mean (normFn V) := by
  rw [← mean_smul]
  apply mean_abs_le
  intro x
  exact norm_inner_le_norm (𝕜 := ℝ) v (V x)

def pairingMean (V : G →ᵇ H) : H →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun v => mean (pairing V v)
      map_add' := by
        intro v w
        have he : pairing V (v+w) = pairing V v + pairing V w := by
          ext x; simp [inner_add_left]
        rw [he, mean_add]
      map_smul' := by
        intro c v
        have he : pairing V (c • v) = c • pairing V v := by
          ext x; simp [real_inner_smul_left]
        rw [he, mean_smul]
        rfl }
    (mean (normFn V)) (by
      intro v
      change |mean (pairing V v)| ≤ mean (normFn V) * ‖v‖
      simpa only [mul_comm] using pairing_mean_bound V v)

/-- Hilbert-space weak mean; it exists by the proved scalar mean and Riesz,
without any real-variable measurability assumption on V. -/
def weakMean (V : G →ᵇ H) : H := (InnerProductSpace.toDual ℝ H).symm (pairingMean V)

end WeakMean

section Periodization
variable {H : Type*} [NormedAddCommGroup H]

/-- The scalar invariant integral in the manuscript, literally the invariant
mean of the period sum on F/Z. -/
def integralReal (h : AF → ℝ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : ℝ := mean (periodBCF h hs hb)

def integralComplex (h : AF → ℂ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : ℂ := cmean (periodBCF h hs hb)

variable [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Hilbert-space weak invariant integral of bounded, boundedly supported
functions, with no ordinary real-variable measurability hypothesis. -/
def weakIntegral (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : H := weakMean (periodBCF h hs hb)

end Periodization

section Smoothing
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable (U : AF → H ≃ₗᵢ[ℝ] H)

def smoothedVector (φ : AF → ℝ) {N : ℕ} {B : ℝ}
    (hφ : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) (v : H) : H :=
  weakIntegral (fun t => φ t • U t v) (smoothed_support U φ hφ v)
    (smoothed_bound U φ hb v)

end Smoothing
end PlaneFiveColor.InvariantMean
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Multipliers
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped ENNReal

def lineU (ν : Measure D) (a : E) (t : F) : Lp ℂ 2 ν ≃ₗᵢ[ℝ] Lp ℂ 2 ν :=
  LpMultiplier.mulEquiv (fun d => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ))
    (lineCharacter_measurable a t).aestronglyMeasurable (fun _ => Circle.norm_coe _)

end PlaneFiveColor.Spectral

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped ENNReal

lemma lineFourier_norm_le (ν : Measure D) [IsProbabilityMeasure ν] (a : E) (t : F) :
    ‖lineFourier ν a t‖ ≤ 1 := by
  simpa [lineFourier] using (norm_integral_le_of_norm_le_const (μ := ν)
    (C := (1 : ℝ)) (Eventually.of_forall (fun d => (Circle.norm_coe
      (lineCharacter a d (Multiplicative.ofAdd t))).le)))

end PlaneFiveColor.Spectral
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_ConditionalSpectrum
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace PlaneFiveColor.Spectral

section
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor
open scoped BigOperators ComplexConjugate

instance dualPolishSpace : PolishSpace D := by
  have : TopologicalSpace.SeparableSpace (DiscreteE → Circle) := inferInstance
  have : TopologicalSpace.IsCompletelyMetrizableSpace (DiscreteE → Circle) := inferInstance
  exact ContinuousMonoidHom.isClosedEmbedding_coe.polishSpace

end

end PlaneFiveColor.Spectral

namespace PlaneFiveColor.Spectral

section
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor
open scoped BigOperators

def momentArgument {M N : ℕ} (z : MomentTest M N) : E :=
  (z.1.val + 1) * ((z.2.val.1.val : E) - z.2.val.2.val)

end

open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators

variable {X Y W : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

def FiniteEncodingApproximationAt (μ : Measure X) [IsProbabilityMeasure μ] (p : X → Y) (q : Y → W)
    (b : X → D) (m : ℕ) (γ : ℝ) : Prop :=
  ∃ (r : ℕ) (B C : ℝ) (H : Fin r → Y → Fin m → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ y, ∑ i, ‖H i y‖ ≤ C) ∧
    ∀ k : K, ∃ coeff : W → Fin r → ℂ,
      (∀ w, ‖coeff w‖ ≤ B) ∧
      Integrable (fun x => dist
        (PhaseEncoding.kernelEncoding (condDistrib b p μ)
          (fun d => (eval (kCoeff k) d : ℂ)) m (p x))
        (∑ i, coeff (q (p x)) i • H i (p x)) ^ 2) μ ∧
      (∫ x, dist
        (PhaseEncoding.kernelEncoding (condDistrib b p μ)
          (fun d => (eval (kCoeff k) d : ℂ)) m (p x))
        (∑ i, coeff (q (p x)) i • H i (p x)) ^ 2 ∂μ) < γ^2

def FiniteEncodingApproximation (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → Y) (q : Y → W) (b : X → D) (m : ℕ) : Prop :=
  ∀ γ : ℝ, 0 < γ → FiniteEncodingApproximationAt μ p q b m γ

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_ConditionalLimits
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory

/-! Bounded finite-dimensional L² approximation at a generated limit factor.
The filtration is the pullback of an increasing sequence of earlier factors;
no martingale convergence theorem beyond Mathlib is assumed. -/

namespace PlaneFiveColor.Spectral

open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators ENNReal
variable {X Y W : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

def AmbientEncodingAt (μ : Measure X) [IsProbabilityMeasure μ] (p : X → Y) (q : X → W)
    (b : X → D) (m : ℕ) (γ : ℝ) : Prop :=
  ∃ (r : ℕ) (B C : ℝ) (H : Fin r → X → Fin m → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ y, ∑ i, ‖H i y‖ ≤ C) ∧
    ∀ k : K, ∃ coeff : W → Fin r → ℂ,
      (∀ w, ‖coeff w‖ ≤ B) ∧
      Integrable (fun x => dist
        (PhaseEncoding.kernelEncoding (condDistrib b p μ)
          (fun d => (eval (kCoeff k) d : ℂ)) m (p x))
        (∑ i, coeff (q x) i • H i x) ^ 2) μ ∧
      (∫ x, dist
        (PhaseEncoding.kernelEncoding (condDistrib b p μ)
          (fun d => (eval (kCoeff k) d : ℂ)) m (p x))
        (∑ i, coeff (q x) i • H i x) ^ 2 ∂μ) < γ^2

end PlaneFiveColor.Spectral

namespace PlaneFiveColor.Spectral

open MeasureTheory ProbabilityTheory EuclideanFiveColor
variable {X Y W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
  [MulAction K X] [MulAction K Y] [MulAction K W]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [MeasurableConstSMul K W]

def UniversalGood (μ : Measure X) [IsProbabilityMeasure μ] (p : X → Y) : Prop :=
  ∀ d : X → D, Measurable d → (∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x) →
    IsWild (μ.map d) → DifferenceFourier.differenceLaw (μ.map p) (condDistrib d p μ) C = 0

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Stationary
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory
open scoped BoundedContinuousFunction
open PlaneFiveColor.InvariantMean
namespace EuclideanFiveColor.StationaryMean
variable {A B X : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace X] [CompactSpace X]
  (t : A → X → X) (r : B → X → X) (x₀ : X)
variable [T2Space X] [MeasurableSpace X] [BorelSpace X]
instance instIsProbabilityMeasureMeasure : IsProbabilityMeasure (measure t r x₀) := by
  have he := integral t r x₀ (ContinuousMap.const X 1)
  rw [average_const] at he
  change (∫ _ : X, (1:ℝ) ∂measure t r x₀) = 1 at he
  simp only [integral_const,smul_eq_mul,mul_one] at he
  constructor
  exact (ENNReal.toReal_eq_one_iff _).mp he
lemma preserving_of_average (s : X ≃ₜ X)
    (hav : ∀ f : C(X,ℝ), average t r x₀ (f.comp ⟨s,s.continuous⟩) = average t r x₀ f) :
    MeasurePreserving s (measure t r x₀) (measure t r x₀) := by
  refine ⟨s.continuous.measurable,?_⟩
  have : (Measure.map s (measure t r x₀)).Regular := Measure.Regular.map s
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x, f.toContinuousMap x ∂(measure t r x₀).map s) = ∫ x, f.toContinuousMap x ∂measure t r x₀
  rw [integral_map s.continuous.measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  exact (integral t r x₀ (f.toContinuousMap.comp ⟨s,s.continuous⟩)).trans ((hav f.toContinuousMap).trans (integral t r x₀ f.toContinuousMap).symm)
end EuclideanFiveColor.StationaryMean
end

namespace PlaneFiveColor.Spectral
open MeasureTheory ProbabilityTheory EuclideanFiveColor
instance K_countable : Countable K := by
  let f : K → E := fun k => ⟨(k.val : ℂ), mem_algebraicClosure_iff.mpr k.property⟩
  apply Function.Injective.countable (f := f)
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : E => (z : ℂ)) h

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Coloring
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace EuclideanFiveColor
instance instIsAddHaarMeasureAnglesAngularMeasure : angularMeasure.IsAddHaarMeasure := inferInstanceAs (AddCircle.haarAddCircle (T := 2*Real.pi)).IsAddHaarMeasure
/-- Exactly the manuscript weak measurable condition, using normalized Haar angular measure.
A function is understood up to a plane-null set; no regularity is imposed on a proper coloring. -/
def WeakColoring (k : ℕ) (c : ℂ → Fin k) : Prop :=
  AEMeasurable c (volume : Measure ℂ) ∧ ∀ᵐ p ∂(volume : Measure ℂ).prod angularMeasure,
    c p.1 ≠ c (p.1+direction p.2)

end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_CircleMaps
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
def circleSum (r : ℝ) (p : RealPlane) : RealPlane :=
  (r*Real.cos p.1+Real.cos p.2,r*Real.sin p.1+Real.sin p.2)
def circleSumDeriv (r : ℝ) (p : RealPlane) : RealPlane →L[ℝ] RealPlane :=
  (r • ((-Real.sin p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (-Real.sin p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
  (r • (Real.cos p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) +
    Real.cos p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)
lemma circleSum_strict (r : ℝ) (p : RealPlane) : HasStrictFDerivAt (circleSum r) (circleSumDeriv r p) p := by
  have hc1 := (Real.hasStrictDerivAt_cos p.1).comp_hasStrictFDerivAt p
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasStrictFDerivAt
  have hc2 := (Real.hasStrictDerivAt_cos p.2).comp_hasStrictFDerivAt p
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasStrictFDerivAt
  have hs1 := (Real.hasStrictDerivAt_sin p.1).comp_hasStrictFDerivAt p
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasStrictFDerivAt
  have hs2 := (Real.hasStrictDerivAt_sin p.2).comp_hasStrictFDerivAt p
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasStrictFDerivAt
  exact ((hc1.const_smul r).add hc2).prodMk ((hs1.const_smul r).add hs2)
lemma circleSumDeriv_injective {r : ℝ} {p : RealPlane} (h : r*Real.sin (p.2-p.1) ≠ 0) :
    Function.Injective (circleSumDeriv r p) := by
  apply (circleSumDeriv r p).toLinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro q hq
  have h1 := congrArg Prod.fst hq
  have h2 := congrArg Prod.snd hq
  change r * (-Real.sin p.1 * q.1) + -Real.sin p.2 * q.2 = 0 at h1
  change r * (Real.cos p.1 * q.1) + Real.cos p.2 * q.2 = 0 at h2
  have ha : r*Real.sin (p.2-p.1)*q.1=0 := by
    rw [Real.sin_sub]
    linear_combination Real.cos p.2*h1+Real.sin p.2*h2
  have hb : r*Real.sin (p.2-p.1)*q.2=0 := by
    rw [Real.sin_sub]
    linear_combination -(r*Real.cos p.1)*h1-(r*Real.sin p.1)*h2
  exact Prod.ext ((mul_eq_zero.mp ha).resolve_left h) ((mul_eq_zero.mp hb).resolve_left h)
def circleSumDerivEquiv {r : ℝ} {p : RealPlane} (h : r*Real.sin (p.2-p.1) ≠ 0) :
    RealPlane ≃L[ℝ] RealPlane :=
  ContinuousLinearEquiv.ofBijective (circleSumDeriv r p)
    (LinearMap.ker_eq_bot.mpr (circleSumDeriv_injective h))
    (LinearMap.range_eq_top.mpr ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
      (circleSumDeriv_injective h)))
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {t u : ℝ} (h : Real.sin (u-t) ≠ 0)
def circleInverseHomeo : OpenPartialHomeomorph RealPlane RealPlane :=
  (show HasStrictFDerivAt (circleSum 1)
    (circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h) : RealPlane →L[ℝ] RealPlane)
    (t,u) from circleSum_strict 1 (t,u)).toOpenPartialHomeomorph (circleSum 1)
def circleInverse : RealPlane → RealPlane := by
  classical
  exact (circleInverseHomeo h).target.piecewise (circleInverseHomeo h).symm (fun _ => 0)
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
def jetCenter : CircleJet →L[ℝ] RealPlane :=
  (ContinuousLinearMap.fst ℝ RealPlane ℝ).comp (ContinuousLinearMap.fst ℝ CircleParameter ℝ)
def jetRadius : CircleJet →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ RealPlane ℝ).comp (ContinuousLinearMap.fst ℝ CircleParameter ℝ)
def jetAngle : CircleJet →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ CircleParameter ℝ
def circleTarget (q : CircleJet) : RealPlane := q.1.1+q.1.2 • (Real.cos q.2,Real.sin q.2)
def circleTargetDeriv (q : CircleJet) : CircleJet →L[ℝ] RealPlane :=
  jetCenter + (q.1.2 • (((-Real.sin q.2) • jetAngle).prod (Real.cos q.2 • jetAngle)) +
    jetRadius.smulRight (Real.cos q.2,Real.sin q.2))
variable {t u : ℝ} (h : Real.sin (u-t) ≠ 0)
def circleEndpoint (q : CircleJet) : ℝ := (circleInverse h (circleTarget q)).1
def circleEndpointDeriv (q : CircleJet) : CircleJet →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (((circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h)).symm : RealPlane →L[ℝ] RealPlane).comp
      (circleTargetDeriv q))
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
def angleChart (p : RealPlane) : Angles × Angles := ((p.1 : Angles),(p.2 : Angles))
def angleChartMeasure : Measure RealPlane :=
  volume.restrict (Ioc (0 : ℝ) (2*Real.pi) ×ˢ Ioc (0 : ℝ) (2*Real.pi))
instance instIsFiniteMeasureRealPlaneAngleChartMeasure : IsFiniteMeasure angleChartMeasure := by
  change IsFiniteMeasure (volume.restrict _)
  apply isFiniteMeasure_restrict.mpr
  apply ne_of_lt
  apply (measure_mono (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)).trans_lt
  exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_CircleTransport
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
def angularSum (x : ℂ) (r : ℝ) (p : Angles × Angles) :=
  x+(r : ℂ)*direction p.1+direction p.2
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set MeasureTheory
namespace EuclideanFiveColor
def samplingParameter (x y : ℂ) (r : ℝ) : CircleParameter := (Complex.equivRealProdCLM (y-x),r)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_WeakColoring
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
def shiftL2 (z : ℂ) (f : PlaneL2) : PlaneL2 :=
  Lp.compMeasurePreserving (fun x => x+z) (measurePreserving_add_right volume z) f
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
include hc
def truncatedVector (i : Fin k) (n : ℕ) : PlaneL2 :=
  (memLp_indicator_const 2 (truncatedClass_measurable c hc i n) (1 : ℝ) (Or.inr (truncatedClass_finite c i n))).toLp _
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Compactness
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
def oneL2 : RealL2 μ := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ Set.univ) 1
end EuclideanFiveColor
end

noncomputable section
open Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor.WeakBall
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E]
instance instCompactSpaceSpace : CompactSpace (Space E) := isCompact_iff_compactSpace.mp (WeakDual.isCompact_closedBall 0 1)
instance instMetrizableSpaceSpace : TopologicalSpace.MetrizableSpace (Space E) :=
  WeakDual.metrizable_of_isCompact ℝ E _ (WeakDual.isCompact_closedBall 0 1)
end EuclideanFiveColor.WeakBall
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Fourier
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
def planeTranslate (h : ℂ) : ComplexPlaneL2 →ₗᵢ[ℂ] ComplexPlaneL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x+h) (measurePreserving_add_right volume h)

def phaseMultiplier (h : ℂ) : ComplexPlaneL2 →L[ℂ] ComplexPlaneL2 :=
  Multiplier.clm volume (planePhase h) (planePhase_continuous h).aestronglyMeasurable
    (Eventually.of_forall fun ξ => (planePhase_norm h ξ).le)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_CircleDecay
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
def circleSymbol (ξ : ℂ) : ℂ := ∫ t, planePhase (direction t) ξ ∂angularMeasure
lemma circleSymbol_norm_le_one (ξ : ℂ) : ‖circleSymbol ξ‖≤1 := by
  simpa only [circleSymbol,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (Eventually.of_forall fun t => (planePhase_norm (direction t) ξ).le :
        ∀ᵐ t ∂angularMeasure, ‖planePhase (direction t) ξ‖ ≤ 1)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_CircleOperator
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
def circleOperator (g : ComplexPlaneL2) : ComplexPlaneL2 := ∫ t, planeTranslate (direction t) g ∂angularMeasure
lemma circleSymbol_stronglyMeasurable : StronglyMeasurable circleSymbol := by
  have h : Continuous (fun p : ℂ × Angles => planePhase (direction p.2) p.1) := by
    unfold planePhase
    exact (continuous_subtype_val.comp Real.continuous_fourierChar).comp
      ((direction_continuous.comp continuous_snd).inner continuous_fst)
  exact h.stronglyMeasurable.integral_prod_right'
def circleMultiplier : ComplexPlaneL2 →L[ℂ] ComplexPlaneL2 :=
  Multiplier.clm volume circleSymbol circleSymbol_stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall circleSymbol_norm_le_one)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor

def circleDifferenceRatio (h ξ : ℂ) : ℝ :=
  ‖circleSymbol ξ‖^2 * ‖1-planePhase h ξ‖^2 / ‖h‖
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology Set
namespace EuclideanFiveColor
def circleAverage (f : ℂ → ℂ) (q : ℂ) : ℂ := ∫ t, f (q+direction t) ∂angularMeasure
def colorMass {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (q : ℂ) : ℝ :=
  ∫ t, sampleFn c q 1 i t ∂angularMeasure
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Transitions
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
def colorError (i : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) : ComplexPlaneL2 :=
  let g := (colorCutoff_memLp c hc i x R).toLp (colorCutoff c i x R)
  circleOperator (g-planeTranslate h g)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Palettes
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma paletteGenerators_countable (x : ℂ) (i : Fin k) : (paletteGenerators c hc x i).Countable :=
  (exists_countable_essential_union angularMeasure (tracePositive c hc x i) (tracePositive_measurable c hc x i)).choose_spec.1
lemma paletteSet_measurable (x : ℂ) (i : Fin k) : MeasurableSet (paletteSet c hc x i) :=
  MeasurableSet.biUnion (paletteGenerators_countable c hc x i) (fun b _ => tracePositive_measurable c hc x i b)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_BinaryPalettes
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
instance anglesNontrivial : Nontrivial Angles := by
  have : Nontrivial Circle := ⟨⟨1,-1,by
    intro h
    have hh := congrArg (fun z : Circle => (z : ℂ)) h
    norm_num at hh⟩⟩
  exact AddCircle.homeomorphCircle'.toEquiv.nontrivial
instance angularMeasure_nullSingleton : NullSingletonClass angularMeasure := by
  exact Measure.IsAddHaarMeasure.nullSingletonClass angularMeasure
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
def sourceTriangle (x : ℂ) (t : ℝ) (j : Fin 3) : ℂ :=
  angularSum x 1 (angleChart (t+2*(j:ℝ)*(Real.pi/3),t+2*(j:ℝ)*(Real.pi/3)+Real.pi+triangleAngle))
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_States
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def fourState (x : ℂ) (t : Angles) : Fin 3 := fourCanonical (palette c hc x t)
lemma fourState_measurable (x : ℂ) : Measurable (fourState c hc x) := by
  change Measurable (fun t => if 4∈palette c hc x t then (0:Fin 3) else if 0∈palette c hc x t then 1 else 2)
  exact Measurable.ite (by simpa only [mem_palette,Set.ofPred_mem_eq] using paletteSet_measurable c hc x 4) measurable_const
    (Measurable.ite (by simpa only [mem_palette,Set.ofPred_mem_eq] using paletteSet_measurable c hc x 0) measurable_const measurable_const)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_AngularBoundary
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace EuclideanFiveColor
instance instDecidableFourWordValid (w : Fin 6 → Fin 3) : Decidable (FourWordValid w) := inferInstanceAs (Decidable (_∧_))
instance instDecidableFourWordMixed (w : Fin 6 → Fin 3) : Decidable (FourWordMixed w) := inferInstanceAs (Decidable (∃_i _j,_∧_∧_))
instance instDecidableFourWordCross (w u : Fin 6 → Fin 3) : Decidable (FourWordCross w u) := inferInstanceAs (Decidable (∀_j,_→_∧_))
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma sixty_six : (6 : ℕ) • (sixty : Angles)=0 := by
  rw [← AddCircle.coe_nsmul]
  convert AddCircle.coe_period (p := 2*Real.pi) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  simp only [nsmul_eq_mul,sixty]
  ring
def sixAngle (j : Fin 6) : Angles := j.val • (sixty : Angles)
lemma sixAngle_step (j : Fin 6) : sixAngle (j+1)=sixAngle j+(sixty : Angles) := by
  fin_cases j <;> norm_num [sixAngle,Fin.val_add,succ_nsmul]
  simpa only [succ_nsmul,zero_nsmul,zero_add] using sixty_six.symm
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
def angleEssential (s : Angles → Bool) (b : Bool) : Set Angles :=
  {t | ∃U : Set Angles,IsOpen U ∧ t∈U ∧ ∀ᵐu∂angularMeasure,u∈U → s u=b}
def angleBoundary (s : Angles → Bool) : Set Angles := (⋃b,angleEssential s b)ᶜ
lemma sixAngle_add (i j : Fin 6) : sixAngle (i+j)=sixAngle i+sixAngle j := by
  induction j using Fin.induction with
  | zero => simp [sixAngle]
  | succ j hj =>
    have he : j.succ=(j.castSucc : Fin 6)+1 := by
      apply Fin.ext
      simp only [Fin.val_succ,Fin.val_add,Fin.val_castSucc,Fin.val_one]
      exact (Nat.mod_eq_of_lt (by omega)).symm
    rw [he,←add_assoc,sixAngle_step,sixAngle_step,hj]
    abel
def sixAngleHom : Fin 6 →+ Angles where
  toFun := sixAngle
  map_zero' := rfl
  map_add' := sixAngle_add
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Exclusion
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace EuclideanFiveColor
instance instDecidableSideCompatible (s : Fin 5 → Bool) (p : Finset (Fin 5)) : Decidable (SideCompatible s p) :=
  inferInstanceAs (Decidable (_∧_∧_))
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
def angularSign (v : Fin 5 → ℂ) (t : Angles) (i : Fin 5) : Bool := decide (0<⟪direction t,v i⟫)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_FourContinuity
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsProbabilityMeasure μ]
def indL2 (A : Set Y) (hA : MeasurableSet A) : RealL2 μ :=
  indicatorConstLp 2 hA (measure_ne_top μ A) 1
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def fourStateL2 (x : ℂ) (s : Fin 3) : RealL2 angularMeasure :=
  indL2 {t | fourState c hc x t=s} (measurableSet_eq_fun (fourState_measurable c hc x) measurable_const)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def fourStateDistance (x y : ℂ) (s : Fin 3) : ℝ :=
  ∫t,‖{t | fourState c hc x t=s}.indicator (fun _ => (1:ℝ)) t-
    {t | fourState c hc y t=s}.indicator (fun _ => (1:ℝ)) t‖ ∂angularMeasure
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def fourRealState (x : ℂ) (s : Fin 3) : Set ℝ := {t | fourState c hc x (t : Angles)=s}
def fourSupport (x : ℂ) (s : Fin 3) : Set ℝ := (volume.restrict (fourRealState c hc x s)).support
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_FourTransport
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor

def sumTransport {a b : ℝ} (h : Real.sin (b-a)≠0) (H : RealPlane) (q : RealPlane) :=
  circleInverse h (circleSum 1 q-H)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def fourNonSingleton (x : ℂ) : Set ℝ := fourSupport c hc x 1∪fourSupport c hc x 2
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
def transportVelocity (H : RealPlane) (a b : ℝ) : ℝ :=
  -(H.1*Real.cos b+H.2*Real.sin b)/Real.sin (b-a)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Accumulation
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def fiveState (x : ℂ) (t : Angles) : Fin 5 := fiveCanonical (palette c hc x t)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Representations
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
instance instTopologicalSpaceRot : TopologicalSpace Rot := ⊥
instance instDiscreteTopologyRot : DiscreteTopology Rot := ⟨rfl⟩
instance rotMeasurable {X : Type*} [MeasurableSpace X] [MulAction K X]
    [MeasurableConstSMul K X] : MeasurableConstVAdd Rot X where
  measurable_const_vadd g := measurable_const_smul (rotMul g)
instance rotInvariant {X : Type*} [MeasurableSpace X] [MulAction K X]
    (μ : Measure X) [SMulInvariantMeasure K X μ] : VAddInvariantMeasure Rot X μ where
  measure_preimage_vadd g s _hs := measure_preimage_smul μ (rotMul g) s
instance rotErgodic {X : Type*} [MeasurableSpace X] [MulAction K X]
    (μ : Measure X) [ErgodicSMul K X μ] : ErgodicVAdd Rot X μ where
  aeconst_of_forall_preimage_vadd_ae_eq hm he :=
    ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq hm (fun k => he (mulRot k))
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory
namespace PlaneFiveColor.LabelModel
open Spectral
variable (k : ℕ)
lemma closed_proper : IsClosed {ω : E → Fin k | Proper k ω} := by
  unfold Proper
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun (x:E) => isClosed_iInter fun (y:E) => isClosed_iInter fun _ => ?_
  have hc : Continuous (fun ω : E → Fin k => (ω x,ω y)) := (continuous_apply x).prodMk (continuous_apply y)
  exact (isClosed_discrete {p : Fin k × Fin k | p.1 ≠ p.2}).preimage hc
instance instCompactSpaceSpace : CompactSpace (Space k) := isCompact_iff_compactSpace.mp (closed_proper k).isCompact
lemma trans_continuous (a : E) : Continuous (trans k a) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (x+a)).comp continuous_subtype_val
lemma rotate_continuous (b : K) : Continuous (rotate k b) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (kCoeff b*x)).comp continuous_subtype_val
lemma trans_add (a b : E) (ω : Space k) : trans k a (trans k b ω) = trans k (a+b) ω := by apply Subtype.ext; funext x; simp [add_assoc]
@[simp] lemma rotate_one (ω : Space k) : rotate k 1 ω = ω := by
  apply Subtype.ext
  funext x
  have h1 : kCoeff 1 = 1 := rfl
  simp [h1]
lemma rotate_mul (a b : K) (ω : Space k) : rotate k a (rotate k b ω) = rotate k (a*b) ω := by
  apply Subtype.ext
  funext x
  change ω.val (kCoeff b * (kCoeff a * x)) = ω.val (kCoeff (a*b)*x)
  have he : kCoeff (a*b) = kCoeff a * kCoeff b := by rfl
  rw [he]; ring_nf
lemma covariance (a : E) (b : K) (ω : Space k) : trans k a (rotate k b ω) = rotate k b (trans k (kCoeff b*a) ω) := by
  apply Subtype.ext
  funext x
  simp only [trans_apply,rotate_apply,mul_add]
def transHomeo (a : E) : Space k ≃ₜ Space k where
  toFun := trans k a
  invFun := trans k (-a)
  left_inv ω := by rw [trans_add,neg_add_cancel,trans_zero]
  right_inv ω := by rw [trans_add,add_neg_cancel,trans_zero]
  continuous_toFun := trans_continuous k a
  continuous_invFun := trans_continuous k (-a)
def rotateHomeo (b : K) : Space k ≃ₜ Space k where
  toFun := rotate k b
  invFun := rotate k b⁻¹
  left_inv ω := by rw [rotate_mul,inv_mul_cancel,rotate_one]
  right_inv ω := by rw [rotate_mul,mul_inv_cancel,rotate_one]
  continuous_toFun := rotate_continuous k b
  continuous_invFun := rotate_continuous k b⁻¹
abbrev Trans := Additive DiscreteE
def tr (a : Trans) : Space k → Space k := trans k (Multiplicative.toAdd (Additive.toMul a))
def ro (b : Rot) : Space k → Space k := rotate k (rotMul b)
def measure (ω : Space k) : Measure (Space k) := EuclideanFiveColor.StationaryMean.measure (tr k) (ro k) ω
instance instIsProbabilityMeasureSpaceMeasure (ω : Space k) : IsProbabilityMeasure (measure k ω) := inferInstanceAs (IsProbabilityMeasure (EuclideanFiveColor.StationaryMean.measure (tr k) (ro k) ω))
lemma trans_preserving (ω : Space k) (a : E) : MeasurePreserving (trans k a) (measure k ω) (measure k ω) := by
  apply EuclideanFiveColor.StationaryMean.preserving_of_average (tr k) (ro k) ω (transHomeo k a)
  intro f
  apply EuclideanFiveColor.StationaryMean.average_translation (tr k) (ro k) ω
    (fun a b x => trans_add k _ _ x) (fun b a => Additive.ofMul (Multiplicative.ofAdd (kCoeff (rotMul b)*Multiplicative.toAdd (Additive.toMul a))))
    (fun a b x => covariance k _ _ x) (Additive.ofMul (Multiplicative.ofAdd a)) f (trans_continuous k a)
lemma rotate_preserving (ω : Space k) (b : K) : MeasurePreserving (rotate k b) (measure k ω) (measure k ω) := by
  apply EuclideanFiveColor.StationaryMean.preserving_of_average (tr k) (ro k) ω (rotateHomeo k b)
  intro f
  exact EuclideanFiveColor.StationaryMean.average_rotation (tr k) (ro k) ω
    (fun a b x => rotate_mul k _ _ x) (mulRot b) f (rotate_continuous k b)
end PlaneFiveColor.LabelModel
end

noncomputable section
open MeasureTheory
namespace PlaneFiveColor.LabelModel
open Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors
variable (k : ℕ) (ω : Space k)
abbrev Hilbert := Lp ℂ 2 (measure k ω)
def translation (a : E) : unitary (Hilbert k ω →L[ℂ] Hilbert k ω) :=
  Koopman.unitary (measure k ω) (transHomeo k a).toMeasurableEquiv (trans_preserving k ω a)
def rotation (b : K) : unitary (Hilbert k ω →L[ℂ] Hilbert k ω) :=
  Koopman.unitary (measure k ω) (rotateHomeo k b).toMeasurableEquiv (rotate_preserving k ω b)
def representation : DiscreteE →* unitary (Hilbert k ω →L[ℂ] Hilbert k ω) where
  toFun a := translation k ω (Multiplicative.toAdd a)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change Lp.compMeasurePreserving (trans k 0) (trans_preserving k ω 0) v = v
    have he : trans k 0 = id := funext (trans_zero k)
    simp only [he,Lp.compMeasurePreserving_id_apply]
  map_mul' a b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change Lp.compMeasurePreserving (trans k (Multiplicative.toAdd a+Multiplicative.toAdd b)) _ v =
      Lp.compMeasurePreserving (trans k (Multiplicative.toAdd a)) _ (Lp.compMeasurePreserving (trans k (Multiplicative.toAdd b)) _ v)
    rw [← Lp.compMeasurePreserving_comp_apply]
    congr 2
    funext x
    exact (congrArg (fun c => trans k c x) (add_comm _ _)).trans (trans_add k _ _ x).symm
end PlaneFiveColor.LabelModel
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Energy
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable

variable {Y : Type*} [MeasurableSpace Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] (q : D → Y)
def projectedMass (z : E) : ℝ := ‖l2 (μ.map q) (conditional μ q (char z))‖^2
lemma projectedMass_nonneg (z : E) : 0 ≤ projectedMass μ q z := sq_nonneg _
lemma projected_char_bound (z : E) (y : Y) : ‖conditional μ q (char z) y‖ ≤ 1 :=
  expect_bound _ _ (fun d => le_of_eq (norm_char _ d)) y
variable (hq : Measurable q)
include hq in
lemma projectedMass_le_one (z : E) : projectedMass μ q z ≤ 1 := by
  let : IsProbabilityMeasure (μ.map q) :=
    (Measure.isProbabilityMeasure_map_iff hq.aemeasurable).mpr inferInstance
  have hn := l2_norm_le (μ.map q) (conditional μ q (char z)) (projected_char_bound μ q z)
  unfold projectedMass
  nlinarith [norm_nonneg (l2 (μ.map q) (conditional μ q (char z)))]
end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_RadialEnergy
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable

def sqrtF (a : F) : F := ⟨Real.sqrt a, mem_algebraicClosure_iff.mpr (by
  by_cases ha : 0 ≤ (a : ℝ)
  · apply IsAlgebraic.of_pow (n := 2) (by decide)
    rw [Real.sq_sqrt ha]
    exact mem_algebraicClosure_iff.mp a.property
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge ha)]
    exact isAlgebraic_zero)⟩

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]
def massReal (a : F) : ℝ := projectedMass μ q (ofF a)
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]
def radiusFamily (r : F) : Rot →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun g => massReal μ q (2*r*reF (kCoeff (rotMul g)))) continuous_of_discreteTopology 1
    (fun g => by
      rw [Real.norm_eq_abs]
      change |projectedMass μ q (ofF _)| ≤ 1
      rw [abs_of_nonneg (projectedMass_nonneg _ _ _)]
      exact projectedMass_le_one μ q hq _)
omit [StandardBorelSpace Y] [Nonempty Y] [ErgodicSMul K D μ]
  [MulAction K Y] [MeasurableConstSMul K Y]
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)] in
@[simp] lemma radiusFamily_apply (r : F) (g : Rot) :
    radiusFamily μ q hq r g = massReal μ q (2*r*reF (kCoeff (rotMul g))) := rfl
end PlaneFiveColor.Spectral
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_SpectralMeasure
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor EuclideanFiveColor.BoundedMeasurable
open EuclideanFiveColor.VectorMeasure EuclideanFiveColor.CommutingSpectral
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : DiscreteE →* unitary (H →L[ℂ] H)) (v : H)
def ordinaryIndicator : Func D :=
  ⟨(C:Set D).indicator (fun _ => (1:ℂ)),measurable_const.indicator measurableSet_C,
    1,fun d => by by_cases hd : d ∈ C <;> simp [Set.indicator_of_mem,Set.indicator_of_notMem,hd]⟩

def ordinaryVector : H := cyclicMap (calculus U) v (l2 (measure (calculus U) v) ordinaryIndicator)
end PlaneFiveColor.Spectral
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Ergodicity
attribute [-instance] _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable

def normF (z : E) : F := ⟨‖(z:ℂ)‖,mem_algebraicClosure_iff.mpr (by
  apply IsAlgebraic.of_pow (n := 2) (by decide)
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  have hr := mem_algebraicClosure_iff.mp (reF z).property
  have hi := mem_algebraicClosure_iff.mp (imF z).property
  exact (hr.mul hr).add (hi.mul hi))⟩
@[simp] lemma normF_coe (z : E) : ((normF z : F):ℝ) = ‖(z:ℂ)‖ := rfl
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open EuclideanFiveColor
namespace PlaneFiveColor.Spectral
instance instCountableRot : Countable Rot := inferInstanceAs (Countable K)
end PlaneFiveColor.Spectral
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_BorelTransfer
attribute [-instance] _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
namespace PlaneFiveColor.LabelModel
open Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors
variable (k : ℕ) (ω : Space k)
def colorValue (i : Fin k) (η : Space k) : ℂ := if η.val 0 = i then 1 else 0
lemma color_memLp (i : Fin k) : MemLp (colorValue k i) 2 (measure k ω) := by
  refine MemLp.of_bound ?_ 1 ?_
  · apply Measurable.aestronglyMeasurable
    apply Measurable.ite _ measurable_const measurable_const
    exact (measurableSet_singleton i).preimage (show Measurable (fun η : Space k => η.val 0) from
      ((continuous_apply (0 : E)).comp continuous_subtype_val).measurable)
  · exact .of_forall fun η => by dsimp [colorValue]; split_ifs <;> simp
abbrev colorVector (i : Fin k) : Hilbert k ω := (color_memLp k ω i).toLp (colorValue k i)
instance continuous_complete : CompleteSpace (space (A := E) (representation k ω)) :=
  (isClosed_space (A := E) (representation k ω)).completeSpace_coe
def projected (i : Fin k) : Hilbert k ω := (space (A := E) (representation k ω)).starProjection (colorVector k ω i)
end PlaneFiveColor.LabelModel
end

noncomputable section
open MeasureTheory Filter Topology
namespace PlaneFiveColor.LabelModel
open Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors
variable (k : ℕ) (ω : Space k)
def oneVector : Hilbert k ω := (memLp_const (1 : ℂ)).toLp (fun _ : Space k => (1 : ℂ))
end PlaneFiveColor.LabelModel
end

noncomputable section
open Filter Topology
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral
lemma dense_E : Dense (E : Set ℂ) := by
  intro z
  have hh : ∀ x y : ℝ, (x : ℂ)+(y : ℂ)*Complex.I ∈ closure (E : Set ℂ) := by
    intro x y
    refine (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).induction_on₂
      (p := fun x y : ℝ => (x : ℂ)+(y : ℂ)*Complex.I ∈ closure (E : Set ℂ)) ?_ ?_ x y
    · exact isClosed_closure.preimage ((Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul_const Complex.I))
    · intro q r
      apply subset_closure
      apply mem_algebraicClosure_iff.mpr
      have hq : IsAlgebraic ℚ ((q : ℝ) : ℂ) := by simpa using isAlgebraic_ratCast ℚ (A := ℂ) q
      have hr : IsAlgebraic ℚ ((r : ℝ) : ℂ) := by simpa using isAlgebraic_ratCast ℚ (A := ℂ) r
      exact hq.add (hr.mul (mem_algebraicClosure_iff.mp imagUnit.property))
  simpa only [Complex.re_add_im] using hh z.re z.im
end PlaneFiveColor.Spectral
end

noncomputable section
open Filter Topology
open scoped InnerProductSpace
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.ContinuousVectors
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : DiscreteE →* unitary (H →L[ℂ] H))
def orbitExtension (v : H) : ℂ → H := dense_E.extend (fun a : E => op U a v)
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace
namespace PlaneFiveColor.LabelModel
open Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors
variable (k : ℕ) (ω : Space k)
def fieldVector (i : Fin k) (x : ℂ) : Hilbert k ω := orbitExtension (representation k ω) (projected k ω i) x
end PlaneFiveColor.LabelModel
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_FiveSupport
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def fiveRealState (x : ℂ) (i : Fin 5) : Set ℝ := {t | fiveState c hc x (t : Angles)=i}
def fiveSupport (x : ℂ) (i : Fin 5) : Set ℝ := (volume.restrict (fiveRealState c hc x i)).support
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def fiveSupportList (x : ℂ) (a : ℝ) : Finset (Fin 5) := by
  classical
  exact Finset.univ.filter (fun i => a∈fiveSupport c hc x i)
@[simp] lemma mem_fiveSupportList (x : ℂ) (a : ℝ) (i : Fin 5) :
    i∈fiveSupportList c hc x a ↔ a∈fiveSupport c hc x i := by simp only [fiveSupportList,Finset.mem_filter,Finset.mem_univ,true_and]
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_GraphRealization
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology
universe u
namespace EuclideanFiveColor
lemma graphEdgePoint_apply {V : Type u} (i j k : V) (t : ℝ) :
    graphEdgePoint i j t k = (1-t)*(if k=i then 1 else 0)+t*(if k=j then 1 else 0) := rfl
lemma graphEdgePoint_swap {V : Type u} (i j : V) (t : ℝ) :
    graphEdgePoint i j t=graphEdgePoint j i (1-t) := by
  simp [graphEdgePoint,add_comm]
lemma continuous_graphEdgePoint {V : Type u} (i j : V) : Continuous (graphEdgePoint i j) := by
  exact ((continuous_const.sub continuous_id).smul continuous_const).add
    (continuous_id.smul continuous_const)
lemma graphVertex_mem {V : Type u} (G : SimpleGraph V) (i : V) : graphVertex i∈graphRealization G :=
  ⟨i,i,Or.inl rfl,0,by norm_num,by simp⟩
lemma graphEdgePoint_mem {V : Type u} {G : SimpleGraph V} {i j : V} (hij : i=j ∨ G.Adj i j)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : graphEdgePoint i j t∈graphRealization G :=
  ⟨i,j,hij,t,ht,rfl⟩
lemma graphRealization_mono {V : Type u} {G H : SimpleGraph V} (h : G≤H) :
    graphRealization G⊆graphRealization H := by
  rintro p ⟨i,j,hij,t,ht,rfl⟩
  exact ⟨i,j,hij.imp id (fun hh => h hh),t,ht,rfl⟩
lemma graphRealization_compact {V : Type u} [Finite V] (G : SimpleGraph V) :
    IsCompact (graphRealization G) := by
  have he : graphRealization G = ⋃ (i : V) (j : V) (_ : i=j ∨ G.Adj i j),
      graphEdgePoint i j '' Icc (0:ℝ) 1 := by
    ext p
    simp only [mem_iUnion,mem_image,graphRealization,mem_ofPred_eq]
    constructor
    · rintro ⟨i,j,hij,t,ht,rfl⟩; exact ⟨i,j,hij,t,ht,rfl⟩
    · rintro ⟨i,j,hij,t,ht,rfl⟩; exact ⟨i,j,hij,t,ht,rfl⟩
  rw [he]
  exact isCompact_iUnion fun i => isCompact_iUnion fun j => isCompact_iUnion fun _ =>
    isCompact_Icc.image (continuous_graphEdgePoint i j)
lemma graphRealization_closed {V : Type u} [Finite V] (G : SimpleGraph V) :
    IsClosed (graphRealization G) := (graphRealization_compact G).isClosed
instance graphSpace_compact {V : Type u} [Finite V] (G : SimpleGraph V) : CompactSpace (GraphSpace G) :=
  isCompact_iff_compactSpace.mp (graphRealization_compact G)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_DiskExtension
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology
universe u
namespace EuclideanFiveColor
/-- Linear transfer of a leaf coordinate along its unique incident edge. -/
def graphLeafMove {V : Type u} (v w : V) (t : ℝ) (p : V → ℝ) : V → ℝ :=
  p+(t*p v) • (graphVertex w-graphVertex v)
lemma continuous_graphLeafMove {V : Type u} (v w : V) :
    Continuous (fun tp : ℝ × (V → ℝ) => graphLeafMove v w tp.1 tp.2) := by
  apply continuous_pi
  intro i
  change Continuous (fun tp : ℝ × (V → ℝ) => tp.2 i + (tp.1 * tp.2 v) * (graphVertex w i-graphVertex v i))
  fun_prop
@[simp] lemma graphLeafMove_zero {V : Type u} (v w : V) (p : V → ℝ) : graphLeafMove v w 0 p=p := by
  simp [graphLeafMove]
lemma graphLeafMove_of_zero {V : Type u} (v w : V) (p : V → ℝ) (hp : p v=0) (t : ℝ) :
    graphLeafMove v w t p=p := by simp [graphLeafMove,hp]
lemma graphLeafMove_edge {V : Type u} {v w : V} (hvw : v≠w) (t s : ℝ) :
    graphLeafMove v w t (graphEdgePoint v w s)=graphEdgePoint v w (s+t*(1-s)) := by
  ext i
  by_cases hi : i=v
  · subst i; simp [graphLeafMove,graphEdgePoint,graphVertex,hvw]; ring
  · by_cases hj : i=w
    · subst i; simp [graphLeafMove,graphEdgePoint,graphVertex,hvw,Ne.symm hvw]
    · simp [graphLeafMove,graphEdgePoint,graphVertex,hi,hj,hvw]
lemma graphLeafMove_vertex {V : Type u} {v w : V} (hvw : v≠w) (t : ℝ) :
    graphLeafMove v w t (graphVertex v)=graphEdgePoint v w t := by
  simpa using graphLeafMove_edge hvw t 0
lemma graphLeafMove_mem {V : Type u} {G : SimpleGraph V} {v w : V}
    (hvw : G.Adj v w) (hleaf : ∀i,G.Adj v i → i=w)
    {p : V → ℝ} (hp : p∈graphRealization G) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    graphLeafMove v w t p∈graphRealization G := by
  obtain ⟨a,b,hab,s,hs,rfl⟩ := hp
  by_cases ha : a=v
  · subst a
    by_cases hb : b=v
    · subst b
      rw [graphEdgePoint_self,graphLeafMove_vertex hvw.ne]
      exact graphEdgePoint_mem (.inr hvw) ht
    · have : b=w := hleaf b (hab.resolve_left (Ne.symm hb))
      subst b
      rw [graphLeafMove_edge hvw.ne]
      apply graphEdgePoint_mem (.inr hvw)
      constructor
      · nlinarith [hs.1,hs.2,ht.1,ht.2]
      · nlinarith [hs.1,hs.2,ht.1,ht.2]
  · by_cases hb : b=v
    · subst b
      have haw : a=w := hleaf a ((hab.resolve_left ha).symm)
      subst a
      rw [graphEdgePoint_swap,graphLeafMove_edge hvw.ne]
      apply graphEdgePoint_mem (.inr hvw)
      constructor <;> nlinarith [hs.1,hs.2,ht.1,ht.2]
    · rw [graphLeafMove_of_zero v w _ (by simp [graphEdgePoint,graphVertex,Ne.symm ha,Ne.symm hb])]
      exact graphEdgePoint_mem hab hs
lemma graphLeafMove_one_at {V : Type u} {v w : V} (hvw : v≠w) (p : V → ℝ) :
    graphLeafMove v w 1 p v=0 := by
  simp [graphLeafMove,graphVertex,hvw]

lemma graphDrop_vertex {V : Type u} {v a : V} (ha : a≠v) :
    graphDrop v (graphVertex a)=graphVertex (⟨a,ha⟩ : {i : V // i≠v}) := by
  ext i; simp [graphDrop,graphVertex,Subtype.ext_iff]
lemma graphDrop_edge {V : Type u} {v a b : V} (ha : a≠v) (hb : b≠v) (t : ℝ) :
    graphDrop v (graphEdgePoint a b t)=graphEdgePoint (⟨a,ha⟩ : {i : V // i≠v}) ⟨b,hb⟩ t := by
  ext i; simp [graphDrop,graphEdgePoint,graphVertex,Subtype.ext_iff]
lemma graphLift_edge {V : Type u} (v : V) (a b : {i : V // i≠v}) (t : ℝ) :
    graphLift v (graphEdgePoint a b t)=graphEdgePoint a.val b.val t := by
  ext i
  by_cases hi : i=v
  · subst i; simp [graphLift,graphEdgePoint,graphVertex,Ne.symm a.property,Ne.symm b.property]
  · simp [graphLift,graphEdgePoint,graphVertex,hi,Subtype.ext_iff]
lemma graphLift_mem {V : Type u} {G : SimpleGraph V} (v : V) {p : {i : V // i≠v} → ℝ}
    (hp : p∈graphRealization (G.induce {i | i≠v})) : graphLift v p∈graphRealization G := by
  obtain ⟨a,b,hab,t,ht,rfl⟩ := hp
  rw [graphLift_edge]
  exact graphEdgePoint_mem (hab.imp (congrArg Subtype.val) id) ht
lemma graphDrop_mem {V : Type u} {G : SimpleGraph V} (v : V) {p : V → ℝ}
    (hp : p∈graphRealization G) (hz : p v=0) :
    graphDrop v p∈graphRealization (G.induce {i | i≠v}) := by
  obtain ⟨a,b,hab,t,ht,rfl⟩ := hp
  by_cases ha : a=v
  · subst a
    by_cases hb : b=v
    · subst b
      simp [graphEdgePoint,graphVertex] at hz
    · have he : t=1 := by
        have : 1-t=0 := by simpa [graphEdgePoint,graphVertex,Ne.symm hb] using hz
        linarith
      subst t
      rw [graphEdgePoint_one,graphDrop_vertex hb]
      exact graphVertex_mem _ _
  · by_cases hb : b=v
    · subst b
      have he : t=0 := by simpa [graphEdgePoint,graphVertex,Ne.symm ha] using hz
      subst t
      rw [graphEdgePoint_zero,graphDrop_vertex ha]
      exact graphVertex_mem _ _
    · rw [graphDrop_edge ha hb]
      exact graphEdgePoint_mem (hab.imp (fun h => Subtype.ext h) id) ht
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor

def graphLeafRetraction {V : Type u} {G : SimpleGraph V} {v w : V}
    (hvw : G.Adj v w) (hleaf : ∀i,G.Adj v i → i=w) :
    C(GraphSpace G, GraphSpace (G.induce {i | i≠v})) where
  toFun p := ⟨graphDrop v (graphLeafMove v w 1 p.val),
    graphDrop_mem v (graphLeafMove_mem hvw hleaf p.property (by norm_num))
      (graphLeafMove_one_at hvw.ne p.val)⟩
  continuous_toFun := (continuous_graphDrop v |>.comp
    ((continuous_graphLeafMove v w).comp (continuous_const.prodMk continuous_subtype_val))).subtype_mk _

def graphLeafInclusion {V : Type u} (G : SimpleGraph V) (v : V) :
    C(GraphSpace (G.induce {i | i≠v}), GraphSpace G) where
  toFun p := ⟨graphLift v p.val,graphLift_mem v p.property⟩
  continuous_toFun := ((continuous_graphLift v).comp continuous_subtype_val).subtype_mk _

def graphLeafHomotopy {V : Type u} {G : SimpleGraph V} {v w : V}
    (hvw : G.Adj v w) (hleaf : ∀i,G.Adj v i → i=w) :
    (ContinuousMap.id (GraphSpace G)).Homotopy
      ((graphLeafInclusion G v).comp (graphLeafRetraction hvw hleaf)) where
  toFun tp := ⟨graphLeafMove v w tp.1.val tp.2.val,
    graphLeafMove_mem hvw hleaf tp.2.property tp.1.property⟩
  continuous_toFun := ((continuous_graphLeafMove v w).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left p := by apply Subtype.ext; exact graphLeafMove_zero v w p.val
  map_one_left p := by
    apply Subtype.ext
    exact (graphLift_drop v _ (graphLeafMove_one_at hvw.ne p.val)).symm

end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_GraphCuts
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
lemma graphEdgePoint_index {V : Type u} {i j k : V} {t : ℝ}
    (h : graphEdgePoint i j t k ≠ 0) : k=i ∨ k=j := by
  by_contra hh
  simp only [not_or] at hh
  exact h (by simp [graphEdgePoint_apply,hh.1,hh.2])
lemma graphRealization_positive_adj {V : Type u} {G : SimpleGraph V} {p : V → ℝ}
    (hp : p∈graphRealization G) {i j : V} (hne : i≠j) (hi : 0<p i) (hj : 0<p j) : G.Adj i j := by
  obtain ⟨a,b,hab,t,ht,rfl⟩ := hp
  have ha := graphEdgePoint_index (ne_of_gt hi)
  have hb := graphEdgePoint_index (ne_of_gt hj)
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
  · exact (hne rfl).elim
  · exact hab.resolve_left hne
  · exact (hab.resolve_left hne.symm).symm
  · exact (hne rfl).elim
lemma graphRealization_pair_le {V : Type u} {G : SimpleGraph V} {p : V → ℝ}
    (hp : p∈graphRealization G) {i j : V} (hne : i≠j) : p i+p j≤1 := by
  obtain ⟨a,b,hab,t,ht,rfl⟩ := hp
  simp only [graphEdgePoint_apply]
  split_ifs <;> subst_vars <;> first | contradiction | nlinarith [ht.1,ht.2]

lemma graphRealization_subset_cut {V : Type u} (T : SimpleGraph V) :
    graphRealization T⊆graphCutRealization T := by
  intro p hp
  refine ⟨graphRealization_mono le_top hp,?_⟩
  intro i j hne hn he
  apply hn
  apply graphRealization_positive_adj hp hne
  · rw [he]; norm_num [graphEdgePoint_apply,hne,hne.symm]
  · rw [he]; norm_num [graphEdgePoint_apply,hne,hne.symm]
lemma graphCut_dominant {V : Type u} {T : SimpleGraph V} {p : V → ℝ}
    (hp : p∈graphCutRealization T) (hn : p∉graphRealization T) : ∃i,1/2<p i := by
  obtain ⟨i,j,hij,t,ht,he⟩ := hp.1
  have hne : i≠j := by
    intro h; apply hn; exact ⟨i,j,Or.inl h,t,ht,he⟩
  have hadj : ¬T.Adj i j := by
    intro h; apply hn; exact ⟨i,j,Or.inr h,t,ht,he⟩
  have htm : t≠1/2 := by intro h; exact hp.2 i j hne hadj (he.trans (by rw [h]))
  rcases lt_or_gt_of_ne htm with hl|hr
  · refine ⟨i,?_⟩; rw [he]; simp [graphEdgePoint_apply,hne]; linarith
  · refine ⟨j,?_⟩; rw [he]; simpa [graphEdgePoint_apply,hne.symm] using hr
lemma graphCut_dominant_unique {V : Type u} {T : SimpleGraph V} {p : V → ℝ}
    (hp : p∈graphCutRealization T) {i j : V} (hi : 1/2<p i) (hj : 1/2<p j) : i=j := by
  by_contra hne
  have hh := graphRealization_pair_le hp.1 hne
  linarith

def graphCutRetract {V : Type u} (T : SimpleGraph V) (p : GraphCutSpace T) : V → ℝ :=
  if h : p.val∈graphRealization T then p.val else graphVertex (graphCut_dominant p.property h).choose
lemma graphCutRetract_tree {V : Type u} {T : SimpleGraph V} (p : GraphCutSpace T)
    (hp : p.val∈graphRealization T) : graphCutRetract T p=p.val := by
  simp [graphCutRetract,hp]
lemma graphCutRetract_dominant {V : Type u} {T : SimpleGraph V} (p : GraphCutSpace T)
    (hp : p.val∉graphRealization T) {i : V} (hi : 1/2<p.val i) : graphCutRetract T p=graphVertex i := by
  rw [graphCutRetract,dite_eq_right hp]
  congr 1
  exact graphCut_dominant_unique p.property (graphCut_dominant p.property hp).choose_spec hi
lemma graphCutRetract_mem {V : Type u} (T : SimpleGraph V) (p : GraphCutSpace T) :
    graphCutRetract T p∈graphRealization T := by
  unfold graphCutRetract
  split
  · assumption
  · exact graphVertex_mem _ _
/-- The closed half of a deleted edge, viewed inside the cut graph. -/
def graphCutStub {V : Type u} (T : SimpleGraph V) (i j : V) : Set (GraphCutSpace T) :=
  {p | i≠j ∧ ¬T.Adj i j ∧ p.val∈graphEdgePoint i j '' Icc (0:ℝ) (1/2)}
lemma graphCutStub_retract {V : Type u} {T : SimpleGraph V} {i j : V}
    {p : GraphCutSpace T} (hp : p∈graphCutStub T i j) : graphCutRetract T p=graphVertex i := by
  obtain ⟨hne,hadj,t,ht,he⟩ := hp
  have he' := he.symm
  have htm : t<1/2 := lt_of_le_of_ne ht.2 (by
    intro h; exact p.property.2 i j hne hadj (he'.trans (by rw [h])))
  by_cases hT : p.val∈graphRealization T
  · rw [graphCutRetract_tree p hT]
    have ht0 : t=0 := by
      by_contra hh
      have hp1 : 0<p.val i := by rw [he']; simp [graphEdgePoint_apply,hne]; linarith
      have hp2 : 0<p.val j := by rw [he']; simp [graphEdgePoint_apply,hne.symm]; exact lt_of_le_of_ne ht.1 (Ne.symm hh)
      exact hadj (graphRealization_positive_adj hT hne hp1 hp2)
    rw [he',ht0,graphEdgePoint_zero]
  · apply graphCutRetract_dominant p hT
    rw [he']; simp [graphEdgePoint_apply,hne]; linarith
lemma graphCut_cover {V : Type u} {T : SimpleGraph V} (p : GraphCutSpace T) :
    p.val∈graphRealization T ∨ ∃i j,p∈graphCutStub T i j := by
  by_cases h : p.val∈graphRealization T
  · exact Or.inl h
  right
  obtain ⟨i,j,hij,t,ht,he⟩ := p.property.1
  have hne : i≠j := by intro hh; exact h ⟨i,j,Or.inl hh,t,ht,he⟩
  have hadj : ¬T.Adj i j := by intro hh; exact h ⟨i,j,Or.inr hh,t,ht,he⟩
  by_cases ht' : t≤1/2
  · exact ⟨i,j,hne,hadj,t,⟨ht.1,ht'⟩,he.symm⟩
  · refine ⟨j,i,hne.symm,fun hh => hadj hh.symm,1-t,⟨by linarith [ht.2],by linarith⟩,?_⟩
    exact (graphEdgePoint_swap i j t).symm.trans he.symm
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
lemma graphCutStub_closed {V : Type u} {T : SimpleGraph V} (i j : V) :
    IsClosed (graphCutStub T i j) := by
  change IsClosed ({p : GraphCutSpace T | i≠j} ∩
    ({p : GraphCutSpace T | ¬T.Adj i j} ∩ Subtype.val ⁻¹' (graphEdgePoint i j '' Icc (0:ℝ) (1/2))))
  exact isClosed_const.inter (isClosed_const.inter ((isCompact_Icc.image (continuous_graphEdgePoint i j)).isClosed.preimage
    continuous_subtype_val))
lemma continuous_graphCutRetract {V : Type u} [Finite V] (T : SimpleGraph V) :
    Continuous (graphCutRetract T) := by
  let S : Option (V × V) → Set (GraphCutSpace T) := fun a => match a with
    | none => Subtype.val ⁻¹' graphRealization T
    | some (i,j) => graphCutStub T i j
  have hcov : ⋃a,S a=univ := by
    apply iUnion_eq_univ_iff.mpr
    intro p
    rcases graphCut_cover p with hp|⟨i,j,hp⟩
    · exact ⟨none,hp⟩
    · exact ⟨some (i,j),hp⟩
  apply (locallyFinite_of_finite S).continuous hcov
  · intro a
    cases a with
    | none => exact (graphRealization_closed T).preimage continuous_subtype_val
    | some a => exact graphCutStub_closed a.1 a.2
  · intro a
    cases a with
    | none => exact continuous_subtype_val.continuousOn.congr (fun p hp => graphCutRetract_tree p hp)
    | some a => exact continuous_const.continuousOn.congr (fun p hp => graphCutStub_retract hp)

lemma graphMidpoint_coord_le {V : Type u} {i j : V} (hne : i≠j) (k : V) :
    graphEdgePoint i j (1/2) k ≤ 1/2 := by
  simp only [graphEdgePoint_apply]
  split_ifs <;> subst_vars <;> first | contradiction | norm_num
lemma graph_dominant_mem_cut {V : Type u} {T : SimpleGraph V} {p : V → ℝ}
    (hp : p∈graphRealization (⊤ : SimpleGraph V)) {i : V} (hi : 1/2<p i) :
    p∈graphCutRealization T := by
  refine ⟨hp,?_⟩
  intro j k hjk _ he
  have hh := graphMidpoint_coord_le hjk i
  rw [←he] at hh
  linarith
lemma graphEdgePoint_lerp_vertex {V : Type u} (i j : V) (t s : ℝ) :
    (1-s) • graphEdgePoint i j t+s • graphVertex i=graphEdgePoint i j ((1-s)*t) := by
  ext k
  simp only [graphEdgePoint,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring
lemma graphCut_lerp_mem {V : Type u} (T : SimpleGraph V) (p : GraphCutSpace T)
    {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    (1-s) • p.val+s • graphCutRetract T p∈graphCutRealization T := by
  rcases graphCut_cover p with hp|⟨i,j,hp⟩
  · rw [graphCutRetract_tree p hp,←add_smul]
    simp
  · have hr := graphCutStub_retract hp
    obtain ⟨hne,hadj,t,ht,he⟩ := hp
    have htm : t<1/2 := lt_of_le_of_ne ht.2 (by
      intro h; exact p.property.2 i j hne hadj (he.symm.trans (by rw [h])))
    rw [hr,←he,graphEdgePoint_lerp_vertex]
    have hu0 : 0≤(1-s)*t := mul_nonneg (by linarith [hs.2]) ht.1
    have hu1 : (1-s)*t≤t := mul_le_of_le_one_left ht.1 (by linarith [hs.1])
    have hu : (1-s)*t<1/2 := lt_of_le_of_lt hu1 htm
    apply graph_dominant_mem_cut (graphEdgePoint_mem (Or.inr (show (⊤ : SimpleGraph V).Adj i j from hne)) ⟨hu0,by linarith⟩) (i := i)
    simp [graphEdgePoint_apply,hne]
    linarith

def graphCutRetraction {V : Type u} [Finite V] (T : SimpleGraph V) :
    C(GraphCutSpace T,GraphSpace T) where
  toFun p := ⟨graphCutRetract T p,graphCutRetract_mem T p⟩
  continuous_toFun := (continuous_graphCutRetract T).subtype_mk _
def graphCutInclusion {V : Type u} (T : SimpleGraph V) : C(GraphSpace T,GraphCutSpace T) where
  toFun p := ⟨p.val,graphRealization_subset_cut T p.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _
def graphCutHomotopy {V : Type u} [Finite V] (T : SimpleGraph V) :
    (ContinuousMap.id (GraphCutSpace T)).Homotopy
      ((graphCutInclusion T).comp (graphCutRetraction T)) where
  toFun sp := ⟨(1-sp.1.val) • sp.2.val+sp.1.val • graphCutRetract T sp.2,
    graphCut_lerp_mem T sp.2 sp.1.property⟩
  continuous_toFun := (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp continuous_snd)).add
    ((continuous_subtype_val.comp continuous_fst).smul
      ((continuous_graphCutRetract T).comp continuous_snd))).subtype_mk _
  map_zero_left p := by apply Subtype.ext; simp
  map_one_left p := by apply Subtype.ext; simp [graphCutInclusion,graphCutRetraction]
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_HoleApproximation
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical ENNReal
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- Exception annuli for exact unit distances from the small closed disks. -/
def diskAnnulus (d : MarkedDisk) : Set ℂ :=
  Metric.closedBall d.center (1+d.radius) \ Metric.ball d.center (1-d.radius)
def holeAnnuli (S : Finset MarkedDisk) : Set ℂ := ⋃d∈S,diskAnnulus d
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_GraphPatches
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u v
namespace EuclideanFiveColor
/-- Edges whose midpoint fibers contain a compact continuum joining the two boundaries. -/
def crossingGraph {X : Type u} {V : Type v} [TopologicalSpace X]
    (f : X → V → ℝ) (A B : Set X) : SimpleGraph V where
  Adj i j := i≠j ∧ FiberCrosses f A B (graphEdgePoint i j (1/2))
  symm := ⟨by
    intro i j h
    refine ⟨h.1.symm,?_⟩
    have he : graphEdgePoint j i (1/2)=graphEdgePoint i j (1/2) := by
      convert graphEdgePoint_swap j i (1/2) using 1; norm_num
    rw [he]; exact h.2⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
def annulusInner (x : ℂ) (r R : ℝ) : Set (planeAnnulus x r R) := {z | dist z.val x=r}
def annulusOuter (x : ℂ) (r R : ℝ) : Set (planeAnnulus x r R) := {z | dist z.val x=R}
lemma sphere_mem_annulus {x z : ℂ} {r R : ℝ} (hrR : r≤R) (hz : z∈Metric.sphere x R) :
    z∈planeAnnulus x r R := by
  apply mem_planeAnnulus.mpr
  have hz' : dist z x=R := hz
  rw [hz']
  exact ⟨le_rfl,hrR⟩
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
def centerDisks (L : Finset ℂ) (R : ℝ) : Finset MarkedDisk := L.image fun x => ⟨x,R,false⟩
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Interfaces
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
def fourInterfaceSign (v : Fin 4 → ℂ) (t : Angles) (i : Fin 4) : Bool :=
  decide (0<⟪direction t,v i⟫)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor

variable {c : ℂ → Fin 5} (hc : Measurable c)
def interfaceStateSet (x : ℂ) (s : Fin 3) : Set Angles := {t | fourState c hc x t=s}
def interfaceStateSupport (x : ℂ) (s : Fin 3) : Set Angles :=
  (angularMeasure.restrict (interfaceStateSet hc x s)).support
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {c : ℂ → Fin 5} (hc : Measurable c)
def fourInterfaceWord (x : ℂ) (t : Angles) (j : Fin 6) : Fin 3 :=
  fourState c hc x (t+sixAngle j)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Sectors
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
def triangleState (c : ℂ → Fin 5) (hc : Measurable c) (x : ℂ) (t : Angles) : Bool := by
  classical
  exact if t∈paletteSet c hc x 3 then false else true
end EuclideanFiveColor
end

end OAI
end


