-- Prove2me | Definitions.Def_OAIQ239Tc022
-- name    : OAIQ239Tc022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:11:17.103388+00:00
-- url     : https://prove2.me/theorems/50feea2e-e72a-4f00-ad23-507db4e5e10f
-- title:
--   Definitions bundle OAIQ239Tc022 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 86 declarations of OpenAI's Lean: 39 definitions, 5 inductive types or structures and 42 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.Hermitian.smoothUnitDefect`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.sqrtSource`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.unitTransverseCut`, `OAI.TamingCompatibility.GeometricHilbert.HodgeCommutatorCover`, `OAI.TamingCompatibility.GeometricHilbert.HodgeCommutatorCover.weight`, `OAI.TamingCompatibility.GeometricHilbert.HodgeCommutatorCover.weightedSquare`, `OAI.TamingCompatibility.GeometricHilbert.HodgeCommutatorPatch`, `OAI.TamingCompatibility.GeometricHilbert.HodgeCommutatorPatch.source`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.basisForm`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.coordinateSupport`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.evaluation`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.evaluationApply`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.evaluationTerm`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.evaluationVector`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.innerKernel`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.regularize`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.wedgeKernel`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.weight`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.weightFunction`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingPatch`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingPatch.source`, `OAI.TamingCompatibility.GeometricHilbert.LocalHodgeSmoothing`, `OAI.TamingCompatibility.GeometricHilbert.LocalHodgeSmoothing.evaluation`, `OAI.TamingCompatibility.GeometricHilbert.LocalHodgeSmoothing.realEvaluation`, `OAI.TamingCompatibility.GeometricHilbert.LocalWeight.coordinateFunction`, `OAI.TamingCompatibility.GeometricHilbert.LocalWeight.coordinateSupport`, `OAI.TamingCompatibility.GeometricHilbert.LocalWeight.halfDensity`, `OAI.TamingCompatibility.GeometricHilbert.hodgeEnergyToScalarJet`, `OAI.TamingCompatibility.GeometricHilbert.hodgeLocalizedRegularization`, `OAI.TamingCompatibility.GeometricHilbert.hodgePowerCommutator`, `OAI.TamingCompatibility.GeometricHilbert.hodgeRawDistribution`, `OAI.TamingCompatibility.GeometricHilbert.hodgeRegularizedGraph`, `OAI.TamingCompatibility.GeometricHilbert.hodgeResolvent`, `OAI.TamingCompatibility.GeometricHilbert.hodgeScalarDistribution`, `OAI.TamingCompatibility.GeometricHilbert.hodgeScalarToJet`, `OAI.TamingCompatibility.GeometricHilbert.hodgeSmoothShift`, `OAI.TamingCompatibility.GeometricHilbert.hodgeTest`, `OAI.TamingCompatibility.GeometricHilbert.hodgeWeakSolution`, `OAI.TamingCompatibility.GeometricHilbert.preAntiProjection` and 4 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Concentration_RadialDefectCombination`, `TamingCompatibility_DifferentialForms_HermitianCorrectedLower`, `TamingCompatibility_DifferentialForms_UnitTransverseCut`, `TamingCompatibility_Functional_GeometricCompact`, `TamingCompatibility_HeatFlow_HodgeResolvent`, `TamingCompatibility_Hodge_HodgeChartScalar`, `TamingCompatibility_Hodge_HodgeCommutatorCover`, `TamingCompatibility_Hodge_HodgeFrameTest`, `TamingCompatibility_Hodge_HodgeGlobalEvaluation`, `TamingCompatibility_Hodge_HodgeLocalCodifferential`, `TamingCompatibility_Hodge_HodgeLocalEvaluation`, `TamingCompatibility_Hodge_HodgeLocalKernel`, `TamingCompatibility_Hodge_HodgeLocalSmooth`, `TamingCompatibility_Hodge_HodgeRawRegular`, `TamingCompatibility_Hodge_HodgeRegularization`, `TamingCompatibility_Hodge_HodgeScalarJet`, `TamingCompatibility_Hodge_HodgeScalarRaw`, `TamingCompatibility_Hodge_HodgeSmoothCommutation`, `TamingCompatibility_Hodge_HodgeSmoothCommutator`, `TamingCompatibility_Hodge_HodgeSmoothLaplacian`, `TamingCompatibility_Hodge_HodgeSmoothingCover`, `TamingCompatibility_Hodge_HodgeWeightNorm`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc017`, `OAIQ239Tc018`, `OAIQ239Tc019` and `OAIQ239Tc020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc025`, `OAIQ239Tc026` and `OAIQ239Tc027`; the statements `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_angularNear_point`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_positive_cross_lower`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_mass_lower`, `OAI.TamingCompatibility.GeometricHilbert.exists_closed_lift_hodge_bound`, `OAI.TamingCompatibility.GeometricHilbert.hodge_regularized_positive_current_cross`, `OAI.TamingCompatibility.GeometricHilbert.separating_current_wedge_upper` and `OAI.TamingCompatibility.separating_probability_atlas_defect`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingFiberForm_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leading_time_primitive` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualFiberForm_smooth`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc017
import Definitions.Def_OAIQ239Tc018
import Definitions.Def_OAIQ239Tc019
import Definitions.Def_OAIQ239Tc020

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_GeometricCompact
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma smoothToChart_metric_bound : ∃ C : ℝ, ∀ a : PreL2 A J α hs ht true,
    ‖smoothL2 A J α hs ht true a‖ ≤ C * ‖smoothToChart A J α hs ht a‖ := by
  obtain ⟨C,hC,hb⟩ := metric_norm_le_chart A J α hs ht D hD
  refine ⟨Real.sqrt C,fun a => ?_⟩
  rw [(smoothL2 A J α hs ht true).norm_map]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hC.le]
  exact hb a

include hD in
lemma chartToMetric_smooth (a : PreL2 A J α hs ht true) :
    chartToMetric A J α hs ht (smoothToChart A J α hs ht a) = smoothL2 A J α hs ht true a :=
  LinearMap.extendOfNorm_eq (smoothToChart_dense A J α hs ht)
    (smoothToChart_metric_bound A J α hs ht D hD) a

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianCorrectedLower
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)
  {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

def sqrtSource {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain) : antiPre A J α hs ht :=
  smoothAntiProjection A J α hs ht (smoothDdc J
    (scalarChartLift_smooth p
      (HermitianRadial.translatedCutoffSqrt_smooth
        (hermitianCenterExtension J p D hφ hc hφD) R hsp b)
      (HermitianRadial.translatedCutoffSqrt_compact _ hR s b)
      (((HermitianRadial.translatedCutoffSqrt_support _ hR s b).trans hball).trans D.domain_subset)))
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_RadialDefectCombination
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel 

def smoothUnitDefect (p : X) (b : Space) (r s : ℝ) :
    MetricUnit (hermitianMetric J α hs ht) → ℝ :=
  (unitChartDomain J α hs ht p (Metric.closedBall b r)).indicator
    (fun u => 2*unitRadialDefect J α hs ht p b u/(s^2+(unitRadialRadius J α hs ht p b u)^2)^2)

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitTransverseCut
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel 

def unitTransverseCut (p : X) (b : Space) (K : Set Space) :
    MetricUnit (hermitianMetric J α hs ht) → Space :=
  (unitChartDomain J α hs ht p K).indicator (unitTransverse J α hs ht p b)

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeChartScalar
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldLocalization ManifoldHodge
open Set MetricForms AntiInvariantFrame GeometricChart
open FormMetric (pairLeft pairRight)
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [CompactSpace X] in
lemma scalar_zero_off (p : A.centers) (a : TwoForm X) (j : Fin 6)
    {x : Space} (hx : x ∉ coordinateSupport A p) : scalar A J α ht D p a j x = 0 := by
  unfold scalar
  by_cases he : x ∈ (D p).domain
  · rw [indicator_of_mem he,localizedFunction_zero_off A p a hx]
    rfl
  · exact indicator_of_notMem he _

omit [T2Space X] in
lemma scalar_tsupport_subset (p : A.centers) (a : TwoForm X) (j : Fin 6) :
    tsupport (scalar A J α ht D p a j) ⊆ coordinateSupport A p := by
  apply closure_minimal _ (coordinateSupport_compact A p).isClosed
  intro x hx
  by_contra hn
  exact hx (scalar_zero_off A J α ht D p a j hn)

include hD in
omit [T2Space X] in
lemma scalar_smooth_compact (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) (j : Fin 6) :
    ContDiff ℝ ∞ (scalar A J α ht D p a j) ∧ HasCompactSupport (scalar A J α ht D p a j) := by
  apply smooth_indicator_of_compact (D p).domain_open (coordinateSupport_compact A p)
    (coordinateSupport_domain A J α ht D hD p)
  · exact FormSmooth.contDiffOn_apply_two
      (localizedFunction_smooth_compact A p a ha).1.contDiffOn
      ((D p).frame_smooth (pairLeft j)) ((D p).frame_smooth (pairRight j))
  · intro x _ hx
    rw [localizedFunction_zero_off A p a hx]
    rfl

def scalarSchwartz (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) (j : Fin 6) :
    𝓢(Space,ℝ) :=
  (scalar_smooth_compact A J α ht D hD p a ha j).2.toSchwartzMap
    (scalar_smooth_compact A J α ht D hD p a ha j).1

omit [T2Space X] in
lemma scalarSchwartz_support (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) (j : Fin 6) :
    tsupport (scalarSchwartz A J α ht D hD p a ha j) ⊆
      Metric.closedBall (extChartAt Model p.val p.val) (D p).radius :=
  (scalar_tsupport_subset A J α ht D p a j).trans (coordinateSupport_small A J α ht D hD p)

include hD in
omit [T2Space X] [CompactSpace X] in
lemma scalar_expansion (p : A.centers) (a : TwoForm X) (x : Space) :
    localizedFunction A p a x = ∑ j : Fin 6, scalar A J α ht D p a j x •
      HodgeFrame.basisForm (coordinateMetric J α ht p.val x) (fun i => (D p).frame i x) j := by
  by_cases hx : x ∈ coordinateSupport A p
  · have hxU := coordinateSupport_domain A J α ht D hD p hx
    have he (j : Fin 6) : scalar A J α ht D p a j x =
        HodgeFrame.coordinates (fun i => (D p).frame i x) (localizedFunction A p a x) j := by
      simp only [scalar, indicator_of_mem hxU, HodgeFrame.coordinates_apply]
    simp only [he, ← HodgeFrame.reconstruct_apply]
    exact (HodgeFrame.reconstruct_coordinates (coordinateMetric J α ht p.val x)
      (by simp [Space]) (fun i => (D p).frame i x) ((D p).frame_gram x hxU) _).symm
  · simp only [localizedFunction_zero_off A p a hx, scalar_zero_off A J α ht D p a _ hx,
      zero_smul, Finset.sum_const_zero]
end TamingCompatibility.HodgeChart

end
end

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume GeometricChart
open Set _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
omit [CompactSpace X] in
lemma localizedPairing_scalars (p : A.centers) (a : TwoForm X) (z : Space) :
    MetricForms.pairing (coordinateMetric J α ht p.val z)
      (localizedFunction A p a z) (localizedFunction A p a z) =
      ‖WithLp.toLp 2 (fun j : Fin 6 => scalar A J α ht D p a j z)‖^2 := by
  by_cases hz : z ∈ coordinateSupport A p
  · have hzU := coordinateSupport_domain A J α ht D hD p hz
    have he : WithLp.toLp 2 (fun j : Fin 6 => scalar A J α ht D p a j z) =
        HodgeFrame.coordinates (fun i => (D p).frame i z) (localizedFunction A p a z) := by
      ext j
      simp only [scalar,indicator_of_mem hzU,HodgeFrame.coordinates_apply]
    rw [he,← real_inner_self_eq_norm_sq]
    exact (HodgeFrame.coordinates_pairing (coordinateMetric J α ht p.val z)
      (by simp [Space]) (fun i => (D p).frame i z) ((D p).frame_gram z hzU) _ _).symm
  · rw [localizedFunction_zero_off A p a hz]
    simp only [scalar_zero_off A J α ht D p a _ hz]
    change MetricForms.pairing _ 0 0 = ‖(0 : EuclideanSpace ℝ (Fin 6))‖^2
    simp only [MetricForms.pairing_self_eq_zero _ _ |>.mpr rfl,norm_zero,ne_eq,
      OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]

include hs hD in
lemma scalar_norm_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, ∀ z,
      ‖WithLp.toLp 2 (fun j : Fin 6 => scalar A J α ht D p a j z)‖^2 ≤
        C * (chartDensity J α p.val z * MetricForms.pairing (coordinateMetric J α ht p.val z)
          (localizedFunction A p a z) (localizedFunction A p a z)) := by
  obtain ⟨C,hC,hbound⟩ := density_lower_on_support A J α hs ht D hD p
  refine ⟨C,hC,?_⟩
  intro a z
  rw [localizedPairing_scalars A J α ht D hD p a]
  by_cases hz : z ∈ coordinateSupport A p
  · have hm := mul_le_mul_of_nonneg_right (hbound z hz)
      (sq_nonneg ‖WithLp.toLp 2 (fun j : Fin 6 => scalar A J α ht D p a j z)‖)
    nlinarith
  · simp only [scalar_zero_off A J α ht D p a _ hz]
    change ‖(0 : EuclideanSpace ℝ (Fin 6))‖^2 ≤ C*(chartDensity J α p.val z*‖(0 : EuclideanSpace ℝ (Fin 6))‖^2)
    simp

variable [MeasurableSpace X] [BorelSpace X]
include hs hD in
lemma integral_scalar_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, Smooth a →
      (∫ z, ‖WithLp.toLp 2 (fun j : Fin 6 => scalar A J α ht D p a j z)‖^2) ≤
        C * ∫ x, GeometricAdjoint.pairing J α ht (cutoffForm A p a)
          (cutoffForm A p a) x ∂geometricVolume A J α := by
  obtain ⟨C,hC,hbound⟩ := scalar_norm_bound A J α hs ht D hD p
  refine ⟨C,hC,?_⟩
  intro a ha
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => sq_nonneg _))
    ((localizedPairing_integrable A J α ht hs p (Or.inr rfl) ha).const_mul C)
    (Filter.Eventually.of_forall (hbound a))
  rw [integral_const_mul,integral_localizedPairing A J α ht hs p (Or.inr rfl) ha] at h
  simpa only [pairing_cutoff A J α ht p a] using h
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLocalCodifferential
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume GeometricChart
open Set _root_.MeasureTheory ContinuousAlternatingMap
open scoped Manifold ContDiff SchwartzMap Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def system (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) : Space → HodgeNormalSymbol.Q :=
  HodgeGeometricCoefficients.operator (coordinateMetric J α ht p.val) (coordinateJ J p.val)
    (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p.val).symm) (D p).frame
    (scalarSchwartz A J α ht D hD p a ha)

lemma field_eq (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) :
    HodgeGeometricCoefficients.field (coordinateMetric J α ht p.val) (D p).frame
      (scalarSchwartz A J α ht D hD p a ha) = localizedFunction A p a := by
  funext x
  exact (scalar_expansion A J α ht D hD p a x).symm

lemma starredField_local (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) {z : Space}
    (hz : z ∈ (extChartAt Model p.val).target) :
    HodgeGeometricCoefficients.starredField (coordinateMetric J α ht p.val) (coordinateJ J p.val)
      (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p.val).symm) (D p).frame
      (scalarSchwartz A J α ht D hD p a ha) z =
      ManifoldForms.pullback (starTwo J α ht (cutoffForm A p a)) (extChartAt Model p.val).symm z := by
  rw [HodgeGeometricCoefficients.starredField_eq,field_eq,
    localizedFunction_eq_cutoff A p a hz,pullback_starTwo J α ht _ p.val hz]

lemma system_zero_off (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) {z : Space}
    (hz : z ∉ coordinateSupport A p) : system A J α ht D hD p a ha z = 0 := by
  have hn (j : Fin 6) : z ∉ tsupport (scalarSchwartz A J α ht D hD p a ha j) :=
    fun h => hz (scalar_tsupport_subset A J α ht D p a j h)
  unfold system HodgeGeometricCoefficients.operator HodgeGeometricCoefficients.field
    HodgeGeometricCoefficients.starredField
  rw [HodgeGeometricCoefficients.extDeriv_sum_zero hn,HodgeGeometricCoefficients.extDeriv_sum_zero hn]
  simp only [MetricHodge.starThree_zero,_root_.map_zero,add_zero]

variable (hs : IsSmooth α)
include hs hD in
lemma system_energy (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) {z : Space}
    (hz : z ∈ coordinateSupport A p) :
    chartDensity J α p.val z * ‖system A J α ht D hD p a ha z‖^2 =
      coordinateIntegrand J α p.val (GeometricAdjoint.pairing J α ht
        (codifferential J α ht (cutoffForm A p a)) (codifferential J α ht (cutoffForm A p a))) z +
      coordinateIntegrand J α p.val (GeometricAdjoint.pairing J α ht
        (codifferential J α ht (cutoffForm A p (starTwo J α ht a)))
        (codifferential J α ht (cutoffForm A p (starTwo J α ht a)))) z := by
  have hzU := coordinateSupport_domain A J α ht D hD p hz
  have hzT := (D p).domain_subset hzU
  have hfield : localizedFunction A p a =ᶠ[𝓝 z]
      ManifoldForms.pullback (cutoffForm A p a) (extChartAt Model p.val).symm := by
    filter_upwards [(isOpen_extChartAt_target p.val).mem_nhds hzT] with y hy
    exact localizedFunction_eq_cutoff A p a hy
  have hstar : HodgeGeometricCoefficients.starredField (coordinateMetric J α ht p.val)
      (coordinateJ J p.val) (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p.val).symm)
      (D p).frame (scalarSchwartz A J α ht D hD p a ha) =ᶠ[𝓝 z]
      ManifoldForms.pullback (starTwo J α ht (cutoffForm A p a)) (extChartAt Model p.val).symm := by
    filter_upwards [(isOpen_extChartAt_target p.val).mem_nhds hzT] with y hy
    exact starredField_local A J α ht D hD p a ha hy
  have he₁ := pullback_codifferential J α hs ht (cutoffForm_smooth A p ha) p.val hzT
  have he₂ := pullback_codifferential_star J α hs ht (cutoffForm_smooth A p ha) p.val hzT
  have hcut : starTwo J α ht (cutoffForm A p a) = cutoffForm A p (starTwo J α ht a) :=
    hodgeStar_fun_smul J α ht (A.partition p) a
  rw [hcut] at he₂
  unfold system HodgeGeometricCoefficients.operator
  rw [field_eq,hstar.extDeriv_eq,hfield.extDeriv_eq,
    HodgeNormalOperator.output_norm _ _ ((D p).frame_gram z hzU)]
  rw [← neg_neg (MetricHodge.starThree _ _ (extDeriv _ z)),← he₁,
    MetricForms.pairing_neg_self]
  rw [← neg_neg (MetricHodge.starThree _ _ (extDeriv _ z)),← he₂,
    MetricForms.pairing_neg_self]
  rw [pairing_chart J α ht p.val (Or.inl rfl) _ _ hzT,
    pairing_chart J α ht p.val (Or.inl rfl) _ _ hzT]
  unfold coordinateIntegrand
  rw [indicator_of_mem hzT,indicator_of_mem hzT,mul_add]

end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameTest
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge HodgeFrame HodgeGeometricCoefficients GeometricChart
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
  (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)

omit [T2Space X] in
lemma manifoldTest_zero_off (q : Space → HodgeNormalSymbol.W) {x : X}
    (hx : x ∉ (extChartAt Model p).symm '' tsupport q) : manifoldTest J α ht p D q x = 0 := by
  apply chartLift_zero_off
  rintro ⟨z,hz,rfl⟩
  exact hx ⟨z,coordinateTest_support J α ht p D q hz,rfl⟩

end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScalarJet
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section

namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldLocalization Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
omit [CompactSpace X] in
lemma scalar_add (p : A.centers) (a b : TwoForm X) (j : Fin 6) :
    scalar A J α ht D p (a+b) j = scalar A J α ht D p a j + scalar A J α ht D p b j := by
  ext x
  unfold scalar
  by_cases hx : x ∈ (D p).domain
  · simp only [indicator_of_mem hx,Pi.add_apply,localizedFunction_add,ContinuousAlternatingMap.add_apply]
  · simp only [indicator_of_notMem hx,Pi.add_apply,add_zero]
omit [CompactSpace X] in
lemma scalar_smul (p : A.centers) (c : ℝ) (a : TwoForm X) (j : Fin 6) :
    scalar A J α ht D p (c • a) j = c • scalar A J α ht D p a j := by
  ext x
  unfold scalar
  by_cases hx : x ∈ (D p).domain
  · simp only [indicator_of_mem hx,Pi.smul_apply,localizedFunction_smul,ContinuousAlternatingMap.smul_apply]
  · simp only [indicator_of_notMem hx,Pi.smul_apply,smul_zero]
def scalarLinear (p : A.centers) (j : Fin 6) : smoothForms X 2 →ₗ[ℝ] 𝓢(Space,ℝ) where
  toFun a := scalarSchwartz A J α ht D hD p a.val a.property j
  map_add' a b := by
    ext x
    exact congrFun (scalar_add A J α ht D p a.val b.val j) x
  map_smul' c a := by
    ext x
    exact congrFun (scalar_smul A J α ht D p c a.val j) x

def scalarVectorLinear (p : A.centers) : smoothForms X 2 →ₗ[ℝ] 𝓢(Space,HodgeScalar.F) :=
  ∑ j : Fin 6, (SchwartzMap.postcompCLM (HodgeScalar.inject j)).toLinearMap ∘ₗ scalarLinear A J α ht D hD p j
end TamingCompatibility.HodgeChart

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart _root_.MeasureTheory
open EuclideanSobolevOperators TemperedDistribution
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

def hodgeScalarToJet (p : A.centers) : PreL2 A J α hs ht true →ₗ[ℝ] HodgeScalar.Jet :=
  HodgeScalar.jet.toLinearMap ∘ₗ scalarVectorLinear A J α ht (fun q => (D q).toData) hD p

def hodgeEnergyToScalarJet (p : A.centers) : hodgeEnergy A J α hs ht →L[ℝ] HodgeScalar.Jet :=
  (hodgeScalarToJet A J α hs ht D hD p).extendOfNorm (hodgeSmooth A J α hs ht)

def hodgeScalarDistribution (p : A.centers) : hodgeEnergy A J α hs ht →L[ℝ] 𝓢'(Space,HodgeScalar.F) :=
  HodgeScalar.jetDistribution none ∘L hodgeEnergyToScalarJet A J α hs ht D hD p

def hodgeRawDistribution (p : A.centers) (τ : 𝓢(Space,ℝ)) :
    hodgeEnergy A J α hs ht →L[ℝ] 𝓢'(Space,HodgeScalar.F) :=
  (smulLeftCLM HodgeScalar.F (SchwartzMap.postcompCLM Complex.ofRealCLM τ)).restrictScalars ℝ ∘L
    hodgeScalarDistribution A J α hs ht D hD p
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScalarRaw
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)
def hodgeTest (p : A.centers) (q : 𝓢(Space,HodgeNormalSymbol.W))
    (hc : HasCompactSupport (q : Space → _)) (hqD : tsupport q ⊆ (D p).domain) : PreL2 A J α hs ht true :=
  ⟨manifoldTest J α ht p.val (D p).toData q,
    manifoldTest_smooth J α hs ht p.val (D p).toData (q.smooth ⊤) hc hqD⟩

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeResolvent
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Filter Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeEnergy_coercive (r : ℝ) (hr : 0 < r) : IsCoercive
    (Variational.energy (V := hodgeEnergy A J α hs ht) (H := L2 A J α hs ht true) (Z := HodgeDerivativePair A J α hs ht) (hodgeInclusion A J α hs ht) (hodgeScaledDerivative A J α hs ht r)) := by
  refine ⟨min 1 (r^2),lt_min zero_lt_one (sq_pos_of_pos hr),fun u => ?_⟩
  rw [Variational.energy_apply,hodgeScaledDerivative_apply,
    real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  have hh := WithLp.prod_norm_sq_eq_of_L2 u.val
  change min 1 (r^2)*‖u.val‖*‖u.val‖ ≤ ‖u.val.fst‖^2 + r*(r*‖u.val.snd‖^2)
  have h1 := mul_le_mul_of_nonneg_right (min_le_left 1 (r^2)) (sq_nonneg ‖u.val.fst‖)
  have h2 := mul_le_mul_of_nonneg_right (min_le_right 1 (r^2)) (sq_nonneg ‖u.val.snd‖)
  calc
    min 1 (r^2)*‖u.val‖*‖u.val‖ = min 1 (r^2)*‖u.val‖^2 := by ring
    _ = min 1 (r^2)*(‖u.val.fst‖^2+‖u.val.snd‖^2) := by rw [hh]
    _ ≤ ‖u.val.fst‖^2+r*(r*‖u.val.snd‖^2) := by nlinarith only [h1,h2]

def hodgeResolvent (r : ℝ) : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  if hr : 0 < r then
    Variational.resolvent (V := hodgeEnergy A J α hs ht) (H := L2 A J α hs ht true) (Z := HodgeDerivativePair A J α hs ht) (hodgeInclusion A J α hs ht) (hodgeScaledDerivative A J α hs ht r)
      (hodgeEnergy_coercive A J α hs ht r hr)
  else 1

def hodgeWeakSolution (r : ℝ) (hr : 0 < r) : L2 A J α hs ht true →L[ℝ] hodgeEnergy A J α hs ht :=
  Variational.weakSolution (V := hodgeEnergy A J α hs ht) (H := L2 A J α hs ht true) (Z := HodgeDerivativePair A J α hs ht) (hodgeInclusion A J α hs ht) (hodgeScaledDerivative A J α hs ht r)
    (hodgeEnergy_coercive A J α hs ht r hr)

lemma hodgeResolvent_eq (r : ℝ) (hr : 0 < r) : hodgeResolvent A J α hs ht r =
    (hodgeInclusion A J α hs ht).comp (hodgeWeakSolution A J α hs ht r hr) := by
  simp only [hodgeResolvent,dite_eq_left hr,Variational.resolvent,hodgeWeakSolution]

lemma hodgeResolvent_symmetric (r : ℝ) : (hodgeResolvent A J α hs ht r).toLinearMap.IsSymmetric := by
  unfold hodgeResolvent
  split_ifs with hr
  · exact Variational.resolvent_symmetric _ _ _
  · intro f g; rfl

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeRawRegular
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

def hodgeRegularizedGraph (r : ℝ) (hr : 0 < r) :
    L2 A J α hs ht true →L[ℝ] hodgeEnergy A J α hs ht :=
  (hodgeWeakSolution A J α hs ht r hr).comp (hodgeResolvent A J α hs ht r ^ 2)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLocalEvaluation
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

def hodgeLocalizedRegularization (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (r : ℝ) (hr : 0 < r) : L2 A J α hs ht true →L[ℝ] 𝓢'(Space,C 6) :=
  ((smulLeftCLM (C 6) χ).restrictScalars ℝ).comp
    ((hodgeRawDistribution A J α hs ht D hD p τ).comp (hodgeRegularizedGraph A J α hs ht r hr))

structure LocalHodgeSmoothing (p : A.centers) (q : Space) (r : ℝ) (hr : 0 < r) where
  reciprocal : 𝓢(Space,ℝ)
  cutoff : 𝓢(Space,ℂ)
  neighborhood : Set Space
  neighborhood_open : IsOpen neighborhood
  center_mem : q ∈ neighborhood
  neighborhood_subset : neighborhood ⊆ (D p).domain
  reciprocal_eq : ∀ z ∈ neighborhood, reciprocal z * coordinateWeight A p z = 1
  cutoff_eq : ∀ z ∈ neighborhood, cutoff z = 1
  lift : L2 A J α hs ht true →L[ℝ] H Space (C 6) 5
  lift_spec : ∀ f, toDistribution Space (C 6) 5 (lift f) =
    hodgeLocalizedRegularization A J α hs ht D hD p reciprocal cutoff r hr f

namespace LocalHodgeSmoothing
variable {A J α hs ht D hD} {p : A.centers} {q : Space} {r : ℝ} {hr : 0 < r}
variable (L : LocalHodgeSmoothing A J α hs ht D hD p q r hr)

def evaluation (z : Space) : L2 A J α hs ht true →L[ℝ] C 6 :=
  ((sobolevEval 5 (by norm_num [Space]) z).restrictScalars ℝ).comp L.lift

omit [T2Space X] in
lemma evaluation_continuous : Continuous L.evaluation := by
  have h := sobolevEval_continuous (E := Space) (F := C 6) 5 (by norm_num [Space])
  exact ((ContinuousLinearMap.restrictScalarsL ℂ (H Space (C 6) 5) (C 6) ℝ ℝ).continuous.comp h).clm_comp continuous_const

end LocalHodgeSmoothing
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLocalKernel
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
namespace LocalHodgeSmoothing
variable {p : A.centers} {q : Space} {r : ℝ} {hr : 0 < r}
variable (L : LocalHodgeSmoothing A J α hs ht D hD p q r hr)

def realEvaluation (z : Space) : L2 A J α hs ht true →L[ℝ] HodgeNormalSymbol.W :=
  (retract 6).comp (L.evaluation z)

omit [T2Space X] in
lemma realEvaluation_continuous : Continuous L.realEvaluation :=
  continuous_const.clm_comp L.evaluation_continuous

end LocalHodgeSmoothing
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothingCover
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

structure HodgeSmoothingPatch (r : ℝ) (hr : 0 < r) where
  chart : A.centers
  center : Space
  smoothing : LocalHodgeSmoothing A J α hs ht D hD chart center r hr

namespace HodgeSmoothingPatch
variable {A J α hs ht D hD} {r : ℝ} {hr : 0 < r}
variable (P : HodgeSmoothingPatch A J α hs ht D hD r hr)
def source : Set X := (extChartAt Model P.chart.val).source ∩
  (extChartAt Model P.chart.val) ⁻¹' P.smoothing.neighborhood
omit [T2Space X] in
lemma source_open : IsOpen P.source :=
  (continuousOn_extChartAt P.chart.val).isOpen_inter_preimage
    (isOpen_extChartAt_source P.chart.val) P.smoothing.neighborhood_open
omit [T2Space X] in
lemma source_subset : P.source ⊆ (extChartAt Model P.chart.val).source := inter_subset_left
end HodgeSmoothingPatch

structure HodgeSmoothingCover (r : ℝ) (hr : 0 < r) where
  centers : Finset X
  patch : centers → HodgeSmoothingPatch A J α hs ht D hD r hr
  partition : SmoothPartitionOfUnity centers Model X
  subordinate : partition.IsSubordinate (fun i => (patch i).source)

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

def coordinateSupport (i : C.centers) : Set Space :=
  (extChartAt Model (C.patch i).chart.val) '' tsupport (C.partition i)

lemma coordinateSupport_compact (i : C.centers) : IsCompact (C.coordinateSupport i) := by
  apply (isClosed_tsupport _).isCompact.image_of_continuousOn
  exact (continuousOn_extChartAt _).mono ((C.subordinate i).trans (C.patch i).source_subset)

lemma coordinateSupport_neighborhood (i : C.centers) :
    C.coordinateSupport i ⊆ (C.patch i).smoothing.neighborhood := by
  rintro z ⟨x,hx,rfl⟩
  exact (C.subordinate i hx).2

lemma coordinateSupport_target (i : C.centers) :
    C.coordinateSupport i ⊆ (extChartAt Model (C.patch i).chart.val).target :=
  (C.coordinateSupport_neighborhood i).trans
    ((C.patch i).smoothing.neighborhood_subset.trans (D (C.patch i).chart).toData.domain_subset)

def weightFunction (i : C.centers) : Space → ℝ :=
  (extChartAt Model (C.patch i).chart.val).target.indicator
    (fun z => C.partition i ((extChartAt Model (C.patch i).chart.val).symm z))

lemma weightFunction_smooth_compact (i : C.centers) :
    ContDiff ℝ ∞ (C.weightFunction i) ∧ HasCompactSupport (C.weightFunction i) := by
  apply smooth_indicator_of_compact (isOpen_extChartAt_target _)
    (C.coordinateSupport_compact i) (C.coordinateSupport_target i)
  · exact (C.partition i).contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt_symm _) |>.contDiffOn
  · intro z hz hn
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hn ⟨_,h,(extChartAt Model (C.patch i).chart.val).right_inv hz⟩

lemma weightFunction_support (i : C.centers) : tsupport (C.weightFunction i) ⊆ C.coordinateSupport i := by
  apply closure_minimal _ (C.coordinateSupport_compact i).isClosed
  intro z hz
  by_cases ht : z ∈ (extChartAt Model (C.patch i).chart.val).target
  · refine ⟨(extChartAt Model (C.patch i).chart.val).symm z,?_,
      (extChartAt Model (C.patch i).chart.val).right_inv ht⟩
    apply subset_closure
    simpa only [Function.mem_support,weightFunction,indicator_of_mem ht] using hz
  · exact False.elim (hz (indicator_of_notMem ht _))

def weight (i : C.centers) : 𝓢(Space,ℝ) :=
  (C.weightFunction_smooth_compact i).2.toSchwartzMap (C.weightFunction_smooth_compact i).1

lemma weight_support (i : C.centers) : tsupport (C.weight i) ⊆ (C.patch i).smoothing.neighborhood :=
  (C.weightFunction_support i).trans (C.coordinateSupport_neighborhood i)

lemma weight_compact (i : C.centers) : HasCompactSupport (C.weight i : Space → ℝ) :=
  (C.weightFunction_smooth_compact i).2

variable [T2Space X]

def basisForm (i : C.centers) (j : Fin 6) : PreL2 A J α hs ht true :=
  hodgeTest A J α hs ht D (C.patch i).chart (componentTest j (C.weight i))
    (full_componentTest_compact j (C.weight i) (C.weight_compact i))
    ((full_componentTest_support j (C.weight i)).trans
      ((C.weight_support i).trans (C.patch i).smoothing.neighborhood_subset))

lemma basisForm_zero (i : C.centers) (j : Fin 6) {x : X}
    (hx : x ∉ tsupport (C.partition i)) : (C.basisForm i j).val x = 0 := by
  apply manifoldTest_zero_off
  rintro ⟨z,hz,rfl⟩
  have hs : z ∈ C.coordinateSupport i :=
    C.weightFunction_support i (full_componentTest_support j (C.weight i) hz)
  obtain ⟨y,hy,rfl⟩ := hs
  exact hx (by rwa [(extChartAt Model (C.patch i).chart.val).left_inv
    ((C.subordinate i hy).1)])
end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Bundle Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def evaluationTerm (i : C.centers) (j : Fin 6) (u : MetricUnit g) :
    L2 A J α hs ht true →L[ℝ] ℝ :=
  unitEvaluation J g (C.basisForm i j).val (C.basisForm i j).property u •
    (EuclideanSpace.proj j).comp ((C.patch i).smoothing.realEvaluation
      (extChartAt Model (C.patch i).chart.val u.val.proj))

lemma evaluationTerm_continuous (i : C.centers) (j : Fin 6) :
    Continuous (C.evaluationTerm g i j) := by
  have hb : Continuous (fun u : MetricUnit g => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u.val.proj ∈ tsupport (C.partition i)
  · have hchart : ContinuousAt (fun v : MetricUnit g => extChartAt Model (C.patch i).chart.val v.val.proj) u :=
      ((continuousOn_extChartAt _ _ (C.subordinate i hu).1).continuousAt
        ((isOpen_extChartAt_source _).mem_nhds (C.subordinate i hu).1)).comp (f := fun v : MetricUnit g => v.val.proj) hb.continuousAt
    exact ((unitEvaluation J g (C.basisForm i j).val (C.basisForm i j).property).continuous.continuousAt).smul
      (continuousAt_const.clm_comp ((C.patch i).smoothing.realEvaluation_continuous.continuousAt.comp hchart))
  · apply (continuousAt_const (y := (0 : L2 A J α hs ht true →L[ℝ] ℝ))).congr_of_eventuallyEq
    have hn : ∀ᶠ v : MetricUnit g in 𝓝 u, v.val.proj ∉ tsupport (C.partition i) :=
      hb.continuousAt.eventually ((isClosed_tsupport (C.partition i)).isOpen_compl.mem_nhds hu)
    filter_upwards [hn] with v hv
    unfold evaluationTerm
    have hz : unitEvaluation J g (C.basisForm i j).val (C.basisForm i j).property v = 0 := by
      change eval (C.basisForm i j).val v.val.proj v.val.2 (J.endomorphism v.val.proj v.val.2) = 0
      change (C.basisForm i j).val v.val.proj ![v.val.2,J.endomorphism v.val.proj v.val.2] = 0
      rw [C.basisForm_zero i j hv]
      rfl
    rw [hz,zero_smul]

def evaluation (u : MetricUnit g) : L2 A J α hs ht true →L[ℝ] ℝ :=
  ∑ i : C.centers, ∑ j : Fin 6, C.evaluationTerm g i j u

lemma evaluation_continuous : Continuous (C.evaluation g) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact C.evaluationTerm_continuous g i j

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeRegularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization
open Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def evaluationVector (u : MetricUnit g) : L2 A J α hs ht true :=
  (C.evaluation g u).adjoint 1

def regularize (μ : Measure (MetricUnit g)) : L2 A J α hs ht true :=
  ∫ u, C.evaluationVector g u ∂μ

def innerKernel (u v : MetricUnit g) : ℝ :=
  ⟪C.evaluationVector g u,C.evaluationVector g v⟫

def wedgeKernel (u v : MetricUnit g) : ℝ :=
  ⟪C.evaluationVector g u,l2Star A J α hs ht (C.evaluationVector g v)⟫

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLocalSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma smoothL2_preD (a : PreL2 A J α hs ht false) :
    smoothL2 A J α hs ht true (hodgePreD A J α hs ht a) = testDerivative A J α hs ht a := rfl

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def hodgeSmoothShift (r : ℝ) : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true :=
  LinearMap.id + r^2 • hodgeLaplacian A J α hs ht

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def preAntiProjection : PreL2 A J α hs ht true →L[ℝ] PreL2 A J α hs ht true :=
  (1/2:ℝ) • (ContinuousLinearMap.id ℝ _ - (preJAction A J α hs ht).toContinuousLinearMap)

def hodgePowerCommutator (k : ℕ) : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true :=
  ((hodgeLaplacian A J α hs ht)^k).comp (preAntiProjection A J α hs ht).toLinearMap -
    (preAntiProjection A J α hs ht).toLinearMap.comp ((hodgeLaplacian A J α hs ht)^k)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeWeightNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

namespace LocalWeight
variable (p : A.centers) (U : Set Space) (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
  (η : X → ℝ) (hη : ContMDiff Model 𝓘(ℝ,ℝ) ∞ η)
  (hηU : tsupport η ⊆ (extChartAt Model p.val).source ∩ (extChartAt Model p.val) ⁻¹' U)

def coordinateFunction : Space → ℝ :=
  (extChartAt Model p.val).target.indicator (fun z => η ((extChartAt Model p.val).symm z))

def coordinateSupport : Set Space := (extChartAt Model p.val) '' tsupport η

include hηU in
omit [MeasurableSpace X] [BorelSpace X] in
lemma coordinateSupport_compact : IsCompact (coordinateSupport A p η) := by
  apply (isClosed_tsupport η).isCompact.image_of_continuousOn
  exact (continuousOn_extChartAt p.val).mono (fun _ hx => (hηU hx).1)

include hηU in
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma coordinateSupport_subset : coordinateSupport A p η ⊆ U := by
  rintro z ⟨x,hx,rfl⟩
  exact (hηU hx).2

include hηU in
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma coordinateSupport_target : coordinateSupport A p η ⊆ (extChartAt Model p.val).target := by
  rintro z ⟨x,hx,rfl⟩
  exact (extChartAt Model p.val).map_source (hηU hx).1

include hη hηU in
omit [MeasurableSpace X] [BorelSpace X] in
lemma coordinateFunction_smooth_compact :
    ContDiff ℝ ∞ (coordinateFunction A p η) ∧ HasCompactSupport (coordinateFunction A p η) := by
  apply smooth_indicator_of_compact (isOpen_extChartAt_target p.val)
    (coordinateSupport_compact A p U η hηU) (coordinateSupport_target A p U η hηU)
  · exact (hη.comp_contMDiffOn (contMDiffOn_extChartAt_symm p.val)).contDiffOn
  · intro z hz hn
    apply image_eq_zero_of_notMem_tsupport
    intro hh
    exact hn ⟨_,hh,(extChartAt Model p.val).right_inv hz⟩

include hηU in
omit [MeasurableSpace X] [BorelSpace X] in
lemma coordinateFunction_support : tsupport (coordinateFunction A p η) ⊆ U := by
  apply (closure_minimal ?_ (coordinateSupport_compact A p U η hηU).isClosed).trans
    (coordinateSupport_subset A p U η hηU)
  intro z hz
  by_cases ht : z ∈ (extChartAt Model p.val).target
  · refine ⟨(extChartAt Model p.val).symm z,?_,(extChartAt Model p.val).right_inv ht⟩
    apply subset_closure
    simpa only [Function.mem_support,coordinateFunction,indicator_of_mem ht] using hz
  · exact False.elim (hz (indicator_of_notMem ht _))

include hs hUD in
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma density_sqrt_smooth : ContDiffOn ℝ ∞ (fun z => Real.sqrt (chartDensity J α p.val z)) U :=
  ((chartDensity_smooth J α hs ht p.val).mono (hUD.trans (D p).domain_subset)).sqrt
    (fun _z hz => ne_of_gt (chartDensity_pos J α ht p.val ((D p).domain_subset (hUD hz))))

def halfDensity : 𝓢(Space,ℝ) :=
  SchwartzCutoff.schwartz hU (density_sqrt_smooth A J α hs ht D p U hUD)
    (coordinateFunction_smooth_compact A p U η hη hηU).1
    (coordinateFunction_smooth_compact A p U η hη hηU).2
    (coordinateFunction_support A p U η hηU)

end LocalWeight
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCommutatorCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

structure HodgeCommutatorPatch (k : ℕ) where
  chart : A.centers
  reciprocal : 𝓢(Space,ℝ)
  neighborhood : Set Space
  neighborhood_open : IsOpen neighborhood
  neighborhood_subset : neighborhood ⊆ (D chart).domain
  reciprocal_spec : ∀ z ∈ neighborhood, reciprocal z * coordinateWeight A chart z = 1
  estimate : ∀ χ : 𝓢(Space,ℂ), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ neighborhood →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∃ T : L2 A J α hs ht true →L[ℝ] H Space (C 6) 0,
        (∀ f : PreL2 A J α hs ht true,
          toDistribution Space (C 6) 0
            (T (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) f))) =
            smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD chart reciprocal
              (hodgeSmooth A J α hs ht (hodgePowerCommutator A J α hs ht (k+1) f)))) ∧
        ∀ v, ‖T v‖ ≤ B * (r⁻¹)^(2*k+1) * ‖v‖

namespace HodgeCommutatorPatch
variable {A J α hs ht D hD} {k : ℕ}
variable (P : HodgeCommutatorPatch A J α hs ht D hD k)
def source : Set X := (extChartAt Model P.chart.val).source ∩
  (extChartAt Model P.chart.val) ⁻¹' P.neighborhood
omit [T2Space X] in
lemma source_open : IsOpen P.source :=
  (continuousOn_extChartAt P.chart.val).isOpen_inter_preimage
    (isOpen_extChartAt_source P.chart.val) P.neighborhood_open
end HodgeCommutatorPatch

structure HodgeCommutatorCover (k : ℕ) where
  centers : Finset X
  patch : centers → HodgeCommutatorPatch A J α hs ht D hD k
  partition : SmoothPartitionOfUnity centers Model X
  subordinate : partition.IsSubordinate (fun i => (patch i).source)

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
namespace HodgeCommutatorCover
variable {k : ℕ} (C : HodgeCommutatorCover A J α hs ht D hD k)

def weight (i : C.centers) : 𝓢(Space,ℝ) :=
  LocalWeight.halfDensity A J α hs ht D (C.patch i).chart (C.patch i).neighborhood
    (C.patch i).neighborhood_open (C.patch i).neighborhood_subset
    (C.partition i) (C.partition i).contMDiff (C.subordinate i)

def weightedSquare (i : C.centers) (a : PreL2 A J α hs ht true) : ℝ :=
  ∫ x, (C.partition i x)^2 * GeometricAdjoint.pairing J α ht a.val a.val x
    ∂geometricVolume A J α

end HodgeCommutatorCover

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothCommutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def evaluationApply : L2 A J α hs ht true →L[ℝ] C(MetricUnit g,ℝ) :=
by
  let hex := (isCompact_univ : IsCompact (Set.univ : Set (MetricUnit g))).exists_bound_of_continuousOn
    (f := C.evaluation g) (C.evaluation_continuous g).continuousOn
  let K := hex.choose
  have hK := hex.choose_spec
  exact LinearMap.mkContinuous
    { toFun := fun f => ⟨fun u => C.evaluation g u f,
        (C.evaluation_continuous g).clm_apply continuous_const⟩
      map_add' := fun f h => by ext u; exact map_add (C.evaluation g u) f h
      map_smul' := fun c f => by ext u; exact map_smul (C.evaluation g u) c f }
    (max K 0) (fun f => by
      apply (ContinuousMap.norm_le _ (mul_nonneg (le_max_right _ _) (norm_nonneg _))).mpr
      intro u
      exact ((C.evaluation g u).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right ((hK u (mem_univ u)).trans (le_max_left _ _))
          (norm_nonneg f)))

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


