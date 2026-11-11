-- Prove2me | Definitions.Def_OAIQ239Tc014
-- name    : OAIQ239Tc014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:25:52.64504+00:00
-- url     : https://prove2.me/theorems/92f0ebd0-a179-451d-8aa5-e413d69d76e8
-- title:
--   Definitions bundle OAIQ239Tc014 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 105 declarations of OpenAI's Lean: 47 definitions, 4 instances and 54 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricAdjoint.pairing`, `OAI.TamingCompatibility.GeometricChart.antiDdcVector`, `OAI.TamingCompatibility.GeometricChart.coordinateWeight`, `OAI.TamingCompatibility.GeometricChart.deltaA`, `OAI.TamingCompatibility.GeometricChart.deltaComplexA`, `OAI.TamingCompatibility.GeometricChart.instNormedAddCommGroupContinuousLinearMapRealIdFormSpace`, `OAI.TamingCompatibility.GeometricChart.instNormedSpaceRealContinuousLinearMapIdFormSpace`, `OAI.TamingCompatibility.GeometricChart.radialSourceVector`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.affineMetric`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gaugedFirst`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gaugedZero`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.metricJet`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalFirst`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMetric`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalPrincipal`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalZero`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledB`, `OAI.TamingCompatibility.GeometricHilbert.HodgeDerivativePair`, `OAI.TamingCompatibility.GeometricHilbert.HodgeGraphSpace`, `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.antiMultiply`, `OAI.TamingCompatibility.GeometricHilbert.antiPre`, `OAI.TamingCompatibility.GeometricHilbert.hodgeDelta`, `OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy`, `OAI.TamingCompatibility.GeometricHilbert.hodgeGraph`, `OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion`, `OAI.TamingCompatibility.GeometricHilbert.hodgeSmooth`, `OAI.TamingCompatibility.GeometricHilbert.l2Core`, `OAI.TamingCompatibility.GeometricHilbert.l2Pairing`, `OAI.TamingCompatibility.GeometricHilbert.l2Star`, `OAI.TamingCompatibility.GeometricHilbert.oneCore` and 7 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_ChartMetric`, `TamingCompatibility_Charts_ChartMetricBounds`, `TamingCompatibility_Charts_CoordinateIntegrand`, `TamingCompatibility_Charts_GeometricCutoff`, `TamingCompatibility_DifferentialForms_AntiEnergy`, `TamingCompatibility_DifferentialForms_AntiSmoothMultiply`, `TamingCompatibility_DifferentialForms_ClosedLiftData`, `TamingCompatibility_DifferentialForms_ComplexEquiv`, `TamingCompatibility_DifferentialForms_ConstantGeometricEnergy`, `TamingCompatibility_DifferentialForms_Dpos`, `TamingCompatibility_DifferentialForms_FunSmul`, `TamingCompatibility_DifferentialForms_GeometricFrameTest`, `TamingCompatibility_DifferentialForms_MetricL2Core`, `TamingCompatibility_DifferentialForms_PairingSmooth`, `TamingCompatibility_DifferentialForms_RadialGeometricCoefficient`, `TamingCompatibility_DifferentialForms_RadialScalarOff`, `TamingCompatibility_DifferentialForms_RawJetEstimate`, `TamingCompatibility_DifferentialForms_RawTest`, `TamingCompatibility_DifferentialForms_TestLinear`, `TamingCompatibility_DifferentialForms_Wedge`, `TamingCompatibility_Functional_MetricL2Completion`, `TamingCompatibility_Functional_NormalMap`, `TamingCompatibility_Hodge_HodgeCompactExtension`, `TamingCompatibility_Hodge_HodgeFiniteFrameResolution`, `TamingCompatibility_Hodge_HodgeFrameTest`, `TamingCompatibility_Hodge_HodgeNormalDistribution`, `TamingCompatibility_Hodge_HodgeStarNormalGauge`, `TamingCompatibility_Hodge_HodgeWedgeEnergy`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc010` and `OAIQ239Tc011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc017`, `OAIQ239Tc018`, `OAIQ239Tc019` and `OAIQ239Tc020`; the statements `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.centeredDisplacement_hasFDerivAt` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMetric_dpos_zero`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc010
import Definitions.Def_OAIQ239Tc011

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartMetric
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility.ManifoldVolume
open _root_.MeasureTheory Set Bundle
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

lemma chartDensity_smooth (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (p : X) :
    ContDiffOn ℝ ∞ (chartDensity J α p) (extChartAt Model p).target := by
  apply MetricDensity.contDiffOn_gram_density
  · exact (hs.invariantPart J).metricCoords J p
  · intro z hz
    exact chartMetric_symm J α p hz
  · intro z hz
    exact chartMetric_pos J α htame p hz

variable [T2Space X] [CompactSpace X]
variable (A : ManifoldLocalization.FiniteCharts X)

omit [T2Space X] in
lemma chartWeight_smooth_compact (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (p : A.centers) :
    ContDiff ℝ ∞ (chartWeight A J α p) ∧ HasCompactSupport (chartWeight A J α p) := by
  apply ManifoldLocalization.smooth_indicator_of_compact (isOpen_extChartAt_target p.val)
    (ManifoldLocalization.coordinateSupport_compact A p)
    (ManifoldLocalization.coordinateSupport_subset A p)
  · have hρ : ContDiffOn ℝ ∞
        (fun z => A.partition p ((extChartAt Model p.val).symm z))
        (extChartAt Model p.val).target := by
      exact (A.partition p).contMDiff.comp_contMDiffOn
        (contMDiffOn_extChartAt_symm p.val) |>.contDiffOn
    exact hρ.mul (chartDensity_smooth J α hs htame p.val)
  · intro z hz hK
    have hn : (extChartAt Model p.val).symm z ∉ tsupport (A.partition p) := by
      intro h
      exact hK ⟨(extChartAt Model p.val).symm z,h,(extChartAt Model p.val).right_inv hz⟩
    rw [image_eq_zero_of_notMem_tsupport hn, zero_mul]

variable [MeasurableSpace X] [BorelSpace X]

omit [T2Space X] [BorelSpace X] in
lemma chartMeasure_finite (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (p : A.centers) :
    IsFiniteMeasure (chartMeasure A J α p) := by
  have hw := chartWeight_smooth_compact A J α hs htame p
  have hi : Integrable (chartWeight A J α p) volume :=
    hw.1.continuous.integrable_of_hasCompactSupport hw.2
  have hf := (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (chartWeight_nonneg A J α p))).mp hi.hasFiniteIntegral
  have := isFiniteMeasure_withDensity hf.ne
  exact inferInstanceAs (IsFiniteMeasure (Measure.map (chartInverse p.val)
    (volume.withDensity (fun z => ENNReal.ofReal (chartWeight A J α p z)))))

omit [T2Space X] [BorelSpace X] in
lemma geometricVolume_finite (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) :
    IsFiniteMeasure (geometricVolume A J α) := by
  have (p : A.centers) := chartMeasure_finite A J α hs htame p
  unfold geometricVolume
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

omit [T2Space X] in
lemma integral_chartMeasure (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (p : A.centers)
    (f : X → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂chartMeasure A J α p) =
      ∫ z, chartWeight A J α p z * f ((extChartAt Model p.val).symm z) := by
  rw [chartMeasure, integral_map (chartInverse_measurable p.val).aemeasurable
    hf.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun z => ENNReal.ofReal (chartWeight A J α p z)) from
      ENNReal.measurable_ofReal.comp
        (chartWeight_smooth_compact A J α hs htame p).1.continuous.measurable)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  rw [ENNReal.toReal_ofReal (chartWeight_nonneg A J α p z), smul_eq_mul]
  by_cases hz : z ∈ (extChartAt Model p.val).target
  · simp only [chartInverse, ite_eq_left hz]
  · simp only [chartWeight, Set.indicator_of_notMem hz, zero_mul]

end TamingCompatibility.ManifoldVolume

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_CoordinateIntegrand
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility.ManifoldVolume
open _root_.MeasureTheory Set Bundle
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]

omit [T2Space X] in
lemma coordinateIntegrand_continuous_compact (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (p : X) (f : X → ℝ)
    (hf : Continuous f) (hfp : tsupport f ⊆ (extChartAt Model p).source) :
    Continuous (coordinateIntegrand J α p f) ∧
      HasCompactSupport (coordinateIntegrand J α p f) := by
  have hK : IsCompact ((extChartAt Model p) '' tsupport f) :=
    (isClosed_tsupport f).isCompact.image_of_continuousOn
      ((continuousOn_extChartAt p).mono hfp)
  apply continuous_indicator_compact (isOpen_extChartAt_target p) hK
  · rintro z ⟨x,hx,rfl⟩
    exact (extChartAt Model p).map_source (hfp hx)
  · exact (chartDensity_smooth J α hs htame p).continuousOn.mul
      (hf.comp_continuousOn (continuousOn_extChartAt_symm p))
  · intro z hz hn
    have hn' : (extChartAt Model p).symm z ∉ tsupport f := by
      intro h
      exact hn ⟨(extChartAt Model p).symm z,h,(extChartAt Model p).right_inv hz⟩
    rw [image_eq_zero_of_notMem_tsupport hn', mul_zero]

omit [T2Space X] in
lemma coordinateIntegrand_integrable (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (p : X) (f : X → ℝ)
    (hf : Continuous f) (hfp : tsupport f ⊆ (extChartAt Model p).source) :
    Integrable (coordinateIntegrand J α p f) := by
  have h := coordinateIntegrand_continuous_compact J α hs htame p f hf hfp
  exact h.1.integrable_of_hasCompactSupport h.2

variable (A : ManifoldLocalization.FiniteCharts X)
variable [MeasurableSpace X] [BorelSpace X]

omit [T2Space X] in
lemma integral_chartMeasure_coordinate (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (q : A.centers)
    (f : X → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂chartMeasure A J α q) =
      ∫ z, coordinateIntegrand J α q.val (fun x => A.partition q x * f x) z := by
  rw [integral_chartMeasure A J α hs htame q f hf]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : z ∈ (extChartAt Model q.val).target
  · simp only [chartWeight, coordinateIntegrand, indicator_of_mem hz]
    ring
  · simp only [chartWeight, coordinateIntegrand, indicator_of_notMem hz, zero_mul]

omit [T2Space X] in

theorem integral_geometricVolume_coordinate (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (p : X)
    (f : X → ℝ) (hf : Continuous f) (hfp : tsupport f ⊆ (extChartAt Model p).source) :
    (∫ x, f x ∂geometricVolume A J α) =
      ∫ z in (extChartAt Model p).target,
        chartDensity J α p z * f ((extChartAt Model p).symm z) := by
  have hc (q : A.centers) : Continuous (fun x => A.partition q x * f x) :=
    (A.partition q).contMDiff.continuous.mul hf
  have hp (q : A.centers) : tsupport (fun x => A.partition q x * f x) ⊆
      (extChartAt Model p).source := (tsupport_mul_subset_right).trans hfp
  have hq (q : A.centers) : tsupport (fun x => A.partition q x * f x) ⊆
      (extChartAt Model q.val).source := (tsupport_mul_subset_left).trans (A.subordinate q)
  have hmi (q : A.centers) : Integrable f (chartMeasure A J α q) := by
    let := chartMeasure_finite A J α hs htame q
    exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  rw [geometricVolume, integral_finsetSum_measure (fun q _ => hmi q)]
  simp_rw [integral_chartMeasure_coordinate A J α hs htame _ f hf]
  have he (q : A.centers) := integral_coordinateIntegrand_eq J α q.val p
    (fun x => A.partition q x * f x) (hq q) (hp q)
  simp_rw [he]
  rw [← integral_finsetSum _ (fun q _ =>
    coordinateIntegrand_integrable J α hs htame p _ (hc q) (hp q))]
  rw [← integral_indicator (isOpen_extChartAt_target p).measurableSet]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : z ∈ (extChartAt Model p).target
  · simp only [coordinateIntegrand, indicator_of_mem hz]
    rw [← Finset.mul_sum, ← Finset.sum_mul, ManifoldLocalization.partition_sum, one_mul]
  · simp only [coordinateIntegrand, indicator_of_notMem hz, Finset.sum_const_zero]

end TamingCompatibility.ManifoldVolume

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FunSmul
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap

namespace TamingCompatibility.ManifoldStokes
open Bundle ContinuousAlternatingMap _root_.MeasureTheory Set
open ManifoldForms ManifoldTop ManifoldVolume
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : ManifoldLocalization.FiniteCharts X)

omit [T2Space X] in
lemma coefficient_integrable (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {β : ManifoldForms.Form X 4} (hβ : Smooth β) :
    Integrable (ManifoldTop.coefficient J α β) (geometricVolume A J α) := by
  let _ := geometricVolume_finite A J α hs ht
  exact (coefficient_smooth J α hs ht hβ).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def integral (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J) :
    smoothForms X 4 →ₗ[ℝ] ℝ where
  toFun β := ∫ x, ManifoldTop.coefficient J α β.1 x ∂geometricVolume A J α
  map_add' β γ := by
    change (∫ x, ManifoldTop.coefficient J α (β.1 + γ.1) x ∂geometricVolume A J α) = _
    rw [coefficient_add]
    exact integral_add (coefficient_integrable A J α hs ht β.2) (coefficient_integrable A J α hs ht γ.2)
  map_smul' c β := by
    change (∫ x, ManifoldTop.coefficient J α (c • β.1) x ∂geometricVolume A J α) = _
    rw [coefficient_smul]
    exact integral_smul c _

omit [T2Space X] in
lemma integral_exteriorDerivative_cutoff (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) (f : X → ℝ)
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (hfp : tsupport f ⊆ (extChartAt Model p).source)
    (β : ManifoldForms.Form X 3) (hβ : Smooth β) :
    integral A J α hs ht ⟨exteriorDerivative (fun x => f x • β x),(hβ.fun_smul hf).exteriorDerivative⟩ = 0 := by
  let γ : ManifoldForms.Form X 3 := fun x => f x • β x
  have hγ : Smooth γ := hβ.fun_smul hf
  have hcoeff : tsupport (ManifoldTop.coefficient J α (exteriorDerivative γ)) ⊆ tsupport f := by
    apply closure_minimal _ (isClosed_tsupport f)
    intro x hx
    by_contra h
    apply hx
    change (exteriorDerivative γ x basis) / volumeForm J α x basis = 0
    rw [show exteriorDerivative γ x = 0 from exteriorDerivative_fun_smul_vanishes β h]
    change (0 : ℝ) / _ = 0
    exact zero_div _
  change (∫ x, ManifoldTop.coefficient J α (exteriorDerivative γ) x ∂geometricVolume A J α) = 0
  rw [integral_geometricVolume_coordinate A J α hs ht p _
    (coefficient_smooth J α hs ht hγ.exteriorDerivative).continuous (hcoeff.trans hfp)]
  let ν : Space → ℝ := fun z => ManifoldForms.pullback (volumeForm J α) (extChartAt Model p).symm z basis
  have hν : ContDiffOn ℝ ∞ ν (extChartAt Model p).target :=
    (ContinuousAlternatingMap.apply ℝ Space ℝ basis).contDiff.comp_contDiffOn
      (smooth_chart _ (volumeForm_smooth J α hs) p)
  let K : Set Space := (extChartAt Model p) '' tsupport f
  have hK : IsCompact K := (isClosed_tsupport f).isCompact.image_of_continuousOn
    ((continuousOn_extChartAt p).mono hfp)
  have hKU : K ⊆ (extChartAt Model p).target := by
    rintro z ⟨x,hx,rfl⟩
    exact (extChartAt Model p).map_source (hfp hx)
  calc
    _ = ∫ z in (extChartAt Model p).target, OrientationSign.sign (ν z) *
        extDeriv (ManifoldForms.pullback γ (extChartAt Model p).symm) z basis := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target p).measurableSet
      intro z hz
      dsimp only
      rw [density_coefficient J α ht (exteriorDerivative γ) p hz]
      rw [pullback_exteriorDerivative γ hγ (isOpen_extChartAt_target p)
        (contMDiffOn_extChartAt_symm p) hz,extDerivWithin_eq_of_mem (isOpen_extChartAt_target p) hz]
    _ = 0 := by
      apply SignedStokes.integral_extDeriv_on_open (isOpen_extChartAt_target p) hK hKU hν
        (fun z hz => coordinateVolume_ne_zero J α ht p hz) (smooth_chart γ hγ p)
      intro z hz hnK
      have hn : (extChartAt Model p).symm z ∉ tsupport f := by
        intro h
        exact hnK ⟨(extChartAt Model p).symm z,h,(extChartAt Model p).right_inv hz⟩
      change ((f ((extChartAt Model p).symm z) • β ((extChartAt Model p).symm z)).compContinuousLinearMap _) = 0
      rw [image_eq_zero_of_notMem_tsupport hn,zero_smul]
      ext v
      rfl

omit [T2Space X] in

theorem stokes (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (β : smoothForms X 3) : integral A J α hs ht (d β) = 0 := by
  classical
  let βp (p : A.centers) : smoothForms X 3 :=
    ⟨fun x => A.partition p x • β.1 x,β.2.fun_smul (A.partition p).contMDiff⟩
  have hsum : ∑ p : A.centers, βp p = β := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change (∑ p : A.centers, A.partition p x • β.1 x) = β.1 x
    rw [← Finset.sum_smul,ManifoldLocalization.partition_sum,one_smul]
  rw [← hsum,_root_.map_sum,_root_.map_sum]
  apply Finset.sum_eq_zero
  intro p _
  exact integral_exteriorDerivative_cutoff A J α hs ht p.val (A.partition p)
    (A.partition p).contMDiff (A.subordinate p) β.1 β.2

end TamingCompatibility.ManifoldStokes

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Wedge
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap

namespace TamingCompatibility.GeometricAdjoint
open Bundle ContinuousAlternatingMap _root_.MeasureTheory ManifoldForms ManifoldHodge ManifoldTop ManifoldVolume
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def pairing (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    {k : ℕ} (a b : ManifoldForms.Form X k) : X → ℝ :=
  fun x => MetricForms.pairing (E := Space) (pointMetric J α ht x) (a x) (b x)

lemma pairing_neg_right (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    {k : ℕ} (a b : ManifoldForms.Form X k) (x : X) : pairing J α ht a (-b) x = -pairing J α ht a b x := by
  let g := pointMetric J α ht x
  let a' : MetricForms.Form Space k := a x
  let b' : MetricForms.Form Space k := b x
  change FormMetric.pairing (MetricHodge.formEquiv g k a') (MetricHodge.formEquiv g k (-b')) =
    -FormMetric.pairing (MetricHodge.formEquiv g k a') (MetricHodge.formEquiv g k b')
  rw [_root_.map_neg,← neg_one_smul ℝ (MetricHodge.formEquiv g k b'),
    FormMetric.pairing_smul_right,neg_one_mul]

lemma coefficient_wedgeTwo_star (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a b : ManifoldForms.Form X 2) :
    ManifoldTop.coefficient J α (ManifoldForms.wedgeTwo a (starTwo J α ht b)) = pairing J α ht a b := by
  funext x
  let a' : MetricForms.Form Space 2 := a x
  let b' : MetricForms.Form Space 2 := b x
  let F : MetricForms.Form Space 2 := invariantPart J α x
  let g := pointMetric J α ht x
  have he := MetricWedgePairing.wedgeTwo_star (E := Space) (pointMetric J α ht x) (J.endomorphism x) (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
    (by simp [Space]) (invariantPart J α x)
    (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm) (a x) (b x)
  change TopForms.coefficient basis (ExteriorForms.volumeSquare F)
    (ExteriorForms.wedgeTwo a' (MetricHodge.starTwo g (J.endomorphism x) F b')) = MetricForms.pairing g a' b'
  exact (congrArg (TopForms.coefficient basis (ExteriorForms.volumeSquare F)) he).trans
    (TopForms.coefficient_smul_left basis (ExteriorForms.volumeSquare F)
      (TopForms.eval_ne_zero basis _ (volumeForm_ne_zero J α ht x)) _)

lemma coefficient_wedgeOne_three (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a : ManifoldForms.Form X 1) (b : ManifoldForms.Form X 3) :
    ManifoldTop.coefficient J α (ManifoldForms.wedgeOne a b) = fun x => -pairing J α ht a (starThree J α ht b) x := by
  funext x
  let a' : MetricForms.Form Space 1 := a x
  let b' : MetricForms.Form Space 3 := b x
  let F : MetricForms.Form Space 2 := invariantPart J α x
  let g := pointMetric J α ht x
  have he := MetricWedgePairing.wedgeOne_three (E := Space) (pointMetric J α ht x) (J.endomorphism x) (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
    (by simp [Space]) (invariantPart J α x)
    (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm) (a x) (b x)
  change TopForms.coefficient basis (ExteriorForms.volumeSquare F)
    (ExteriorForms.wedgeOne (ExteriorForms.oneLinear a') b') = -MetricForms.pairing g a' (MetricHodge.starThree g F b')
  exact (congrArg (TopForms.coefficient basis (ExteriorForms.volumeSquare F)) he).trans
    (TopForms.coefficient_smul_left basis (ExteriorForms.volumeSquare F)
      (TopForms.eval_ne_zero basis _ (volumeForm_ne_zero J α ht x)) _)

lemma codifferential_smooth (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {b : TwoForm X} (hb : IsSmooth b) : Smooth (codifferential J α ht b) := by
  have he := (starThree_smooth J α hs ht (Smooth.exteriorDerivative (starTwo_smooth J α hs ht hb))).smul (-1)
  simpa only [codifferential,neg_one_smul] using he

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : ManifoldLocalization.FiniteCharts X)

theorem formal_adjoint (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {a : ManifoldForms.Form X 1} {b : TwoForm X}
    (ha : Smooth a) (hb : IsSmooth b) :
    (∫ x, pairing J α ht (exteriorDerivative a) b x ∂geometricVolume A J α) =
      ∫ x, pairing J α ht a (codifferential J α ht b) x ∂geometricVolume A J α := by
  let bstar := starTwo J α ht b
  have hbs : Smooth bstar := starTwo_smooth J α hs ht hb
  let γ : smoothForms X 3 := ⟨ManifoldForms.wedgeOne a bstar,ha.wedgeOne hbs⟩
  let η : smoothForms X 4 := ⟨ManifoldForms.wedgeTwo (exteriorDerivative a) bstar,ha.exteriorDerivative.wedgeTwo hbs⟩
  let ζ : smoothForms X 4 := ⟨ManifoldForms.wedgeOne a (exteriorDerivative bstar),ha.wedgeOne hbs.exteriorDerivative⟩
  have hd : d γ = η - ζ := Subtype.ext (exteriorDerivative_wedgeOne ha hbs)
  have hst := ManifoldStokes.stokes A J α hs ht γ
  rw [hd,_root_.map_sub] at hst
  have hη : ManifoldStokes.integral A J α hs ht η =
      ∫ x, pairing J α ht (exteriorDerivative a) b x ∂geometricVolume A J α := by
    change (∫ x, ManifoldTop.coefficient J α (ManifoldForms.wedgeTwo (exteriorDerivative a) (starTwo J α ht b)) x
      ∂geometricVolume A J α) = _
    rw [coefficient_wedgeTwo_star]
  have hζ : ManifoldStokes.integral A J α hs ht ζ =
      ∫ x, pairing J α ht a (codifferential J α ht b) x ∂geometricVolume A J α := by
    change (∫ x, ManifoldTop.coefficient J α (ManifoldForms.wedgeOne a (exteriorDerivative bstar)) x
      ∂geometricVolume A J α) = _
    rw [coefficient_wedgeOne_three]
    apply integral_congr_ae
    filter_upwards [] with x
    exact (pairing_neg_right J α ht a (starThree J α ht (exteriorDerivative bstar)) x).symm
  rw [hη,hζ] at hst
  exact sub_eq_zero.mp hst
end TamingCompatibility.GeometricAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ComplexEquiv
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap

namespace TamingCompatibility.GeometricAdjoint
open Bundle ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
lemma rdd_smooth (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) {a : TwoForm X} (ha : IsSmooth a) : IsSmooth (rdd J α ht a) :=
  IsSmooth.antiInvariantPart (Smooth.exteriorDerivative (codifferential_smooth J α hs ht ha)) J

end TamingCompatibility.GeometricAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PairingSmooth
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.GeometricAdjoint
open Bundle ManifoldForms ManifoldHodge ManifoldTop
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
lemma pairing_one_smooth (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {a b : ManifoldForms.Form X 1}
    (ha : Smooth a) (hb : Smooth b) : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (pairing J α ht a b) := by
  apply scalar_smooth_of_charts
  intro p
  apply (SmoothMetric.contDiffOn_pairing_one (coordinateMetric J α ht p) (coordinateJ J p)
    (by simp [Space]) (isOpen_extChartAt_target p) (coordinateMetric_smooth J α hs ht p)
    (coordinateJ_smooth J p) (fun z hz => coordinateJ_square J p hz)
    (fun z hz => coordinateMetric_hermitian J α ht p hz)
    (smooth_chart a ha p) (smooth_chart b hb p)).congr
  intro z hz
  let L : Space ≃L[ℝ] Space := inverseChartEquiv p z hz
  have hL : L.toContinuousLinearMap = mfderiv Model Model (extChartAt Model p).symm z :=
    inverseChartEquiv_coe p z hz
  have he := MetricForms.pairing_one_comp (E := Space) (D := Space) (coordinateMetric J α ht p z)
    (pointMetric J α ht ((extChartAt Model p).symm z)) L
    (coordinateMetric_pullback J α ht p hz) (by simp [Space]) (a ((extChartAt Model p).symm z)) (b ((extChartAt Model p).symm z))
  rw [hL] at he
  exact he.symm
lemma pairing_two_smooth (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {a b : ManifoldForms.Form X 2}
    (ha : Smooth a) (hb : Smooth b) : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (pairing J α ht a b) := by
  apply scalar_smooth_of_charts
  intro p
  apply (SmoothMetric.contDiffOn_pairing_two (coordinateMetric J α ht p) (coordinateJ J p)
    (by simp [Space]) (isOpen_extChartAt_target p) (coordinateMetric_smooth J α hs ht p)
    (coordinateJ_smooth J p) (fun z hz => coordinateJ_square J p hz)
    (fun z hz => coordinateMetric_hermitian J α ht p hz)
    (smooth_chart a ha p) (smooth_chart b hb p)).congr
  intro z hz
  let L : Space ≃L[ℝ] Space := inverseChartEquiv p z hz
  have hL : L.toContinuousLinearMap = mfderiv Model Model (extChartAt Model p).symm z :=
    inverseChartEquiv_coe p z hz
  have he := MetricForms.pairing_two_comp (E := Space) (D := Space) (coordinateMetric J α ht p z)
    (pointMetric J α ht ((extChartAt Model p).symm z)) L
    (coordinateMetric_pullback J α ht p hz) (by simp [Space]) (a ((extChartAt Model p).symm z)) (b ((extChartAt Model p).symm z))
  rw [hL] at he
  exact he.symm
end TamingCompatibility.GeometricAdjoint

namespace TamingCompatibility.ManifoldVolume
open Bundle _root_.MeasureTheory ManifoldLocalization
open scoped Topology Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X)

theorem geometricVolume_openPos (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) : (geometricVolume A J α).IsOpenPosMeasure := by
  classical
  constructor
  intro U hU hne
  obtain ⟨x,hxU⟩ := hne
  have hn : (∑ p : A.centers, A.partition p x) ≠ 0 := by
    rw [partition_sum A x]
    exact one_ne_zero
  obtain ⟨p,_,hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hp' : 0 < A.partition p x := lt_of_le_of_ne (A.partition.nonneg _ _) hp.symm
  let e := extChartAt Model p.val
  have hx : x ∈ e.source := A.subordinate p (subset_tsupport _ hp)
  have hz : e x ∈ e.target := e.map_source hx
  let w := chartWeight A J α p
  have hw : Continuous w := (chartWeight_smooth_compact A J α hs ht p).1.continuous
  have hwz : 0 < w (e x) := by
    change 0 < e.target.indicator (fun z => A.partition p (e.symm z) * chartDensity J α p.val z) (e x)
    rw [Set.indicator_of_mem hz,e.left_inv hx]
    exact mul_pos hp' (chartDensity_pos J α ht p.val hz)
  let V : Set Space := (e.target ∩ e.symm ⁻¹' U) ∩ {z | 0 < w z}
  have hV : IsOpen V :=
    ((continuousOn_extChartAt_symm p.val).isOpen_inter_preimage
      (isOpen_extChartAt_target p.val) hU).inter (isOpen_lt continuous_const hw)
  have hzV : e x ∈ V := ⟨⟨hz,by simpa only [Set.mem_preimage,e.left_inv hx] using hxU⟩,hwz⟩
  have hVm : 0 < volume V := hV.measure_pos volume ⟨e x,hzV⟩
  let f := fun z => ENNReal.ofReal (w z)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp hw.measurable
  have hVF : V ⊆ Function.support f ∩ chartInverse p.val ⁻¹' U := by
    intro z hz
    refine ⟨?_,?_⟩
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr hz.2)
    · change (if z ∈ e.target then e.symm z else p.val) ∈ U
      rw [ite_eq_left hz.1.1]
      exact hz.1.2
  have hpos : 0 < chartMeasure A J α p U := by
    rw [chartMeasure,Measure.map_apply (chartInverse_measurable p.val) hU.measurableSet,
      withDensity_apply _ ((chartInverse_measurable p.val) hU.measurableSet)]
    exact (setLIntegral_pos_iff hf).mpr (lt_of_lt_of_le hVm (measure_mono hVF))
  have hle : chartMeasure A J α p U ≤ geometricVolume A J α U := by
    rw [geometricVolume,Measure.finsetSum_apply]
    exact Finset.single_le_sum (fun q _ => show (0 : ENNReal) ≤ chartMeasure A J α q U from bot_le) (Finset.mem_univ p)
  exact ne_of_gt (lt_of_lt_of_le hpos hle)
end TamingCompatibility.ManifoldVolume

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricL2Core
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace TamingCompatibility.GeometricHilbert
open _root_.MeasureTheory ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization GeometricAdjoint
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def l2Pairing {k : ℕ} (a b : smoothForms X k) : ℝ :=
  ∫ x, pairing J α ht a.val b.val x ∂geometricVolume A J α

omit [CompactSpace X] [BorelSpace X] in
lemma l2_nonneg {k : ℕ} (a : smoothForms X k) : 0 ≤ l2Pairing A J α ht a a :=
  integral_nonneg (fun x => MetricForms.pairing_self_nonneg (pointMetric J α ht x) (a.val x))

omit [CompactSpace X] [BorelSpace X] in
lemma l2_symm {k : ℕ} (a b : smoothForms X k) :
    l2Pairing A J α ht a b = l2Pairing A J α ht b a := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => MetricForms.pairing_symm _ _ _)

@[instance_reducible] def l2Core (k : ℕ)
    (hcont : ∀ a b : smoothForms X k, Continuous (pairing J α ht a.val b.val)) :
    InnerProductSpace.Core ℝ (smoothForms X k) := by
  let := geometricVolume_finite A J α hs ht
  let := geometricVolume_openPos A J α hs ht
  have hint (a b : smoothForms X k) : Integrable (pairing J α ht a.val b.val)
      (geometricVolume A J α) :=
    (hcont a b).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine {
    inner := l2Pairing A J α ht
    conj_inner_symm := ?_
    re_inner_nonneg := fun a => l2_nonneg A J α ht a
    add_left := ?_
    smul_left := ?_
    definite := ?_ }
  · intro a b
    exact l2_symm A J α ht b a
  · intro a b c
    change (∫ x, pairing J α ht (a.val+b.val) c.val x ∂geometricVolume A J α) = _
    have he : pairing J α ht (a.val+b.val) c.val =
        pairing J α ht a.val c.val + pairing J α ht b.val c.val := by
      funext x
      exact MetricForms.pairing_add_left' _ _ _ _
    rw [he]
    exact integral_add (hint a c) (hint b c)
  · intro a b r
    change (∫ x, pairing J α ht (r • a.val) b.val x ∂geometricVolume A J α) =
      r * l2Pairing A J α ht a b
    have he : pairing J α ht (r • a.val) b.val =
        fun x => r * pairing J α ht a.val b.val x := by
      funext x
      exact MetricForms.pairing_smul_left _ _ _ _
    rw [he,integral_const_mul]
    rfl
  · intro a haz
    apply Subtype.ext
    funext x
    apply (MetricForms.pairing_self_eq_zero (pointMetric J α ht x) (a.val x)).mp
    have he : pairing J α ht a.val a.val = 0 :=
      Measure.eq_of_ae_eq ((integral_eq_zero_iff_of_nonneg
        (fun y => MetricForms.pairing_self_nonneg (pointMetric J α ht y) (a.val y))
        (hint a a)).mp haz) (hcont a a) continuous_zero
    exact congrFun he x

@[instance_reducible] def oneCore : InnerProductSpace.Core ℝ (smoothForms X 1) :=
  l2Core A J α hs ht 1 (fun a b =>
    (pairing_one_smooth J α hs ht a.property b.property).continuous)
@[instance_reducible] def twoCore : InnerProductSpace.Core ℝ (smoothForms X 2) :=
  l2Core A J α hs ht 2 (fun a b =>
    (pairing_two_smooth J α hs ht a.property b.property).continuous)

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_MetricL2Completion
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldLocalization
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def PreL2 (_A : FiniteCharts X) (_J : AlmostComplexStructure X) (_α : TwoForm X)
    (_hs : IsSmooth _α) (_ht : Tames _α _J) (k : Bool) : Type _ := ↥(smoothForms X (if k then 2 else 1))

instance preL2Add (k : Bool) : AddCommGroup (PreL2 A J α hs ht k) :=
  inferInstanceAs (AddCommGroup (smoothForms X (if k then 2 else 1)))
instance preL2Module (k : Bool) : Module ℝ (PreL2 A J α hs ht k) :=
  inferInstanceAs (Module ℝ (smoothForms X (if k then 2 else 1)))

@[instance_reducible] def preL2Core (k : Bool) :
    InnerProductSpace.Core ℝ (PreL2 A J α hs ht k) := by
  cases k
  · exact oneCore A J α hs ht
  · exact twoCore A J α hs ht

instance preL2Normed (k : Bool) : NormedAddCommGroup (PreL2 A J α hs ht k) :=
  letI := preL2Core A J α hs ht k
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
instance preL2Inner (k : Bool) : InnerProductSpace ℝ (PreL2 A J α hs ht k) :=
  InnerProductSpace.ofCore (preL2Core A J α hs ht k).toCore

lemma preL2_inner (k : Bool) (a b : PreL2 A J α hs ht k) :
    inner ℝ a b = l2Pairing A J α ht a b := by
  cases k <;> rfl

lemma preL2_norm_sq (k : Bool) (a : PreL2 A J α hs ht k) :
    ‖a‖^2 = l2Pairing A J α ht a a := by
  rw [← real_inner_self_eq_norm_sq,preL2_inner]

abbrev L2 (k : Bool) := UniformSpace.Completion (PreL2 A J α hs ht k)

def smoothL2 (k : Bool) : PreL2 A J α hs ht k →ₗᵢ[ℝ] L2 A J α hs ht k :=
  UniformSpace.Completion.toComplₗᵢ

lemma smoothL2_dense (k : Bool) : DenseRange (smoothL2 A J α hs ht k) :=
  UniformSpace.Completion.denseRange_coe

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_AntiEnergy
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
lemma antiInvariantPart_add (J : AlmostComplexStructure X) (a b : TwoForm X) :
    antiInvariantPart J (a+b) = antiInvariantPart J a + antiInvariantPart J b := by
  simp only [antiInvariantPart,jAction_add,add_sub_add_comm,smul_add]
lemma antiInvariantPart_smul (J : AlmostComplexStructure X) (c : ℝ) (a : TwoForm X) :
    antiInvariantPart J (c • a) = c • antiInvariantPart J a := by
  simp only [antiInvariantPart,jAction_smul]
  module

namespace ManifoldHodge
lemma starThree_add (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a b : ManifoldForms.Form X 3) : starThree J α ht (a+b) =
      starThree J α ht a + starThree J α ht b := by
  funext x
  change MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x) (invariantPart J α x)
      (a x+b x) = MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
      (invariantPart J α x) (a x) + MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
      (invariantPart J α x) (b x)
  exact MetricHodge.starThree_add _ _ _ _
lemma starThree_smul (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (c : ℝ) (a : ManifoldForms.Form X 3) : starThree J α ht (c • a) =
      c • starThree J α ht a := by
  funext x
  change MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x) (invariantPart J α x)
      (c • a x) = c • MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
      (invariantPart J α x) (a x)
  exact MetricHodge.starThree_smul _ _ _ _
end ManifoldHodge

namespace GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def antiPre : Submodule ℝ (PreL2 A J α hs ht true) where
  carrier := {a | antiInvariantPart J a.val = a.val}
  zero_mem' := by
    change antiInvariantPart J 0 = 0
    have he := antiInvariantPart_smul J 0 (0 : TwoForm X)
    simpa only [zero_smul] using he
  add_mem' := by
    intro a b ha hb
    change antiInvariantPart J (a.val+b.val) = a.val+b.val
    rw [antiInvariantPart_add,ha,hb]
  smul_mem' := by
    intro c a ha
    change antiInvariantPart J (c • a.val) = c • a.val
    rw [antiInvariantPart_smul,ha]

end GeometricHilbert
end TamingCompatibility

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ConstantGeometricEnergy
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap RealInnerProductSpace
namespace TamingCompatibility.MatrixEnergy
open EuclideanEnergy

lemma constantSystem_integrable (c : Fin 4 → Pair →L[ℝ] V) (A B : S) :
    Integrable (fun x => ‖constantSystem c A B x‖^2) := by
  have h := system_integrable (fun i _ => c i) (fun _ => 0) A B
    (δ := ∑ i, ‖c i‖) (C := 0) (fun _ => continuous_const) continuous_const
    (fun _ i => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    (fun _ => by simp)
  simpa only [system,zero_apply,add_zero,constantSystem] using h

end TamingCompatibility.MatrixEnergy

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_GeometricCutoff
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section

namespace TamingCompatibility
open Bundle ManifoldForms ManifoldHodge GeometricAdjoint
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma antiInvariant_fun_smul (J : AlmostComplexStructure X) {a : TwoForm X}
    (ha : antiInvariantPart J a = a) (f : X → ℝ) :
    antiInvariantPart J (fun x => f x • a x) = fun x => f x • a x := by
  funext x
  ext v
  have h := congrArg (fun b => b x v) ha
  change (1/2:ℝ) * (a x v - (a x).compContinuousLinearMap (J.endomorphism x) v) = a x v at h
  change (1/2:ℝ) * (f x * a x v - f x * (a x).compContinuousLinearMap (J.endomorphism x) v) = f x * a x v
  calc
    _ = f x * ((1/2:ℝ) * (a x v - (a x).compContinuousLinearMap (J.endomorphism x) v)) := by ring
    _ = _ := congrArg (f x * ·) h

end TamingCompatibility

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartMetricBounds
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldVolume ManifoldHodge
open Set MetricForms _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
local instance instFiniteDimensionalRealContinuousMultilinearMapFinSpace {k : ℕ} : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => Space) ℝ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective
local instance instFiniteDimensionalRealFormSpace {k : ℕ} : FiniteDimensional ℝ (MetricForms.Form Space k) :=
  FiniteDimensional.of_injective ContinuousAlternatingMap.toContinuousMultilinearMapLinear
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective
local instance instNormedAddCommGroupContinuousLinearMapRealIdFormSpace {k : ℕ} : NormedAddCommGroup (MetricForms.Form Space k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdFormSpace {k : ℕ} : NormedSpace ℝ (MetricForms.Form Space k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

include hs hD in

lemma coordinate_metric_bounds (p : A.centers) (k : ℕ)
    (hpair : ContinuousOn (fun x => pairingCLM (coordinateMetric J α ht p.val x) k) (D p).domain) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ coordinateSupport A p, ∀ v : MetricForms.Form Space k,
      ‖v‖^2 ≤ C * (chartDensity J α p.val x * pairing (coordinateMetric J α ht p.val x) v v) ∧
      chartDensity J α p.val x * pairing (coordinateMetric J α ht p.val x) v v ≤ C * ‖v‖^2 := by
  let Q := fun x => chartDensity J α p.val x • pairingCLM (coordinateMetric J α ht p.val x) k
  have hQ : ContinuousOn Q (coordinateSupport A p) :=
    ((chartDensity_smooth J α hs ht p.val).continuousOn.mono
      ((coordinateSupport_domain A J α ht D hD p).trans (D p).domain_subset)).smul
      (hpair.mono (coordinateSupport_domain A J α ht D hD p))
  obtain ⟨C,hC,hbound⟩ := CompactQuadratic.lower_bound (coordinateSupport_compact A p) Q hQ (by
    intro x hx v hv
    exact mul_pos (chartDensity_pos J α ht p.val ((coordinateSupport_domain A J α ht D hD p).trans
      (D p).domain_subset hx)) (lt_of_le_of_ne (pairing_self_nonneg _ _) (Ne.symm (by
        intro h; exact hv ((pairing_self_eq_zero _ _).mp h)))))
  obtain ⟨B,hB⟩ := (coordinateSupport_compact A p).exists_bound_of_continuousOn (f := Q) hQ
  refine ⟨max C (max 1 B),lt_of_lt_of_le hC (le_max_left _ _),?_⟩
  intro x hx v
  have hval : 0 ≤ Q x v v := mul_nonneg (chartDensity_pos J α ht p.val
    ((coordinateSupport_domain A J α ht D hD p).trans (D p).domain_subset hx)).le
    (pairing_self_nonneg _ _)
  constructor
  · exact (hbound x hx v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hval)
  · change Q x v v ≤ _
    calc Q x v v ≤ ‖Q x v v‖ := le_abs_self _
         _ ≤ ‖Q x v‖ * ‖v‖ := (Q x v).le_opNorm v
         _ ≤ (‖Q x‖ * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right ((Q x).le_opNorm v) (norm_nonneg _)
         _ ≤ (max C (max 1 B) * ‖v‖) * ‖v‖ := by
           gcongr
           exact (hB x hx).trans ((le_max_right 1 B).trans (le_max_right C (max 1 B)))
         _ = _ := by ring

include hs hD in
lemma coordinate_metric_one_bounds (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ coordinateSupport A p, ∀ v : MetricForms.Form Space 1,
      ‖v‖^2 ≤ C * (chartDensity J α p.val x * pairing (coordinateMetric J α ht p.val x) v v) ∧
      chartDensity J α p.val x * pairing (coordinateMetric J α ht p.val x) v v ≤ C * ‖v‖^2 :=
  coordinate_metric_bounds A J α hs ht D hD p 1
    (pairingCLM_one_smooth _ (by simp [Space]) (D p).frame (D p).frame_smooth (D p).frame_gram).continuousOn

include hs hD in
lemma coordinate_metric_two_bounds (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ coordinateSupport A p, ∀ v : MetricForms.Form Space 2,
      ‖v‖^2 ≤ C * (chartDensity J α p.val x * pairing (coordinateMetric J α ht p.val x) v v) ∧
      chartDensity J α p.val x * pairing (coordinateMetric J α ht p.val x) v v ≤ C * ‖v‖^2 :=
  coordinate_metric_bounds A J α hs ht D hD p 2
    (pairingCLM_two_smooth _ (by simp [Space]) (D p).frame (D p).frame_smooth (D p).frame_gram).continuousOn
end TamingCompatibility.GeometricChart

end
end

section

noncomputable section

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume LocalMatrixOperator
open Set _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)

lemma coordinateIntegrand_self_nonneg {k : ℕ} (p : X) (a : ManifoldForms.Form X k) (z : Space) :
    0 ≤ coordinateIntegrand J α p (GeometricAdjoint.pairing J α ht a a) z := by
  unfold coordinateIntegrand
  by_cases hz : z ∈ (extChartAt Model p).target
  · rw [indicator_of_mem hz]
    exact mul_nonneg (chartDensity_pos J α ht p hz).le (MetricForms.pairing_self_nonneg _ _)
  · rw [indicator_of_notMem hz]

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFrameTest
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
  (ht : Tames α J) (p : X) (D : Data J α ht p)

include hs in
omit [T2Space X] in
lemma coordinateTest_smooth {q : Space → EuclideanEnergy.Pair} (hq : ContDiff ℝ ∞ q)
    (hqD : tsupport q ⊆ D.domain) : ContDiff ℝ ∞ (coordinateTest J α ht p D q) :=
  frameTest_smooth D.domain_open
    (realPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth)
    (imagPart_smooth ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth) hq hqD

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawTest
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def coordinateWeight (p : A.centers) (z : Space) : ℝ :=
  A.partition p ((extChartAt Model p.val).symm z)

omit [CompactSpace X] in
lemma coordinateWeight_smooth (p : A.centers) :
    ContDiffOn ℝ ∞ (coordinateWeight A p) (extChartAt Model p.val).target :=
  (A.partition p).contMDiff.comp_contMDiffOn
    (contMDiffOn_extChartAt_symm p.val) |>.contDiffOn

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_AntiSmoothMultiply
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def antiMultiply (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (a : antiPre A J α hs ht) : antiPre A J α hs ht :=
  ⟨⟨(fun x => ρ x • a.val.val x),a.val.property.fun_smul hρ⟩,
    antiInvariant_fun_smul J a.property ρ⟩

@[simp] lemma antiMultiply_apply (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (a : antiPre A J α hs ht) (x : X) :
    (antiMultiply A J α hs ht ρ hρ a).val.val x = ρ x • a.val.val x := rfl

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_TestLinear
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge LocalMatrixOperator
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)
lemma coordinateTest_add (q r : Space → EuclideanEnergy.Pair) :
    coordinateTest J α ht p D (q+r) = coordinateTest J α ht p D q + coordinateTest J α ht p D r := by
  funext z
  simp only [coordinateTest,frameTest,Pi.add_apply,PiLp.add_apply,add_smul]
  module
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ClosedLiftData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

def deltaA (i : Fin 4) (z : Space) : EuclideanEnergy.Pair →L[ℝ] MetricForms.Form Space 1 :=
  -(frameRecover (coordinateMetric J α ht p z) (fun j => D.frame j z)).comp (normalA J α ht p D i z)

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
local instance instNormedAddCommGroupMetricTensorSpace : NormedAddCommGroup (NormalJets.MetricTensor (V := ManifoldForms.Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace : NormedSpace ℝ (NormalJets.MetricTensor (V := ManifoldForms.Space)) := ContinuousLinearMap.toNormedSpace
open ManifoldForms ManifoldHodge _root_.MeasureTheory Set Filter NormalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def frameMap (b : Fin 4 → Space) : Space →L[ℝ] Space :=
  ∑ i, (EuclideanSpace.proj i).smulRight (b i)

@[simp] lemma frameMap_apply (b : Fin 4 → Space) (v : Space) :
    frameMap b v = ∑ i, v i • b i := by
  simp [frameMap]

local instance instNormedAddCommGroupMetricDerivativeSpace_r3e2add_1 : NormedAddCommGroup (NormalJets.MetricDerivative (V := ManifoldForms.Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricDerivativeSpace_r3e2add_1 : NormedSpace ℝ (NormalJets.MetricDerivative (V := ManifoldForms.Space)) := ContinuousLinearMap.toNormedSpace
def affineMetric (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (pz : Space × Space) : MetricTensor (V := Space) :=
  (g (pz.1+B pz.1 pz.2)).bilinearComp (B pz.1) (B pz.1)

def metricJet (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (p : Space) : MetricDerivative (V := Space) :=
  UniformJets.dpos (affineMetric g B) (p,0)

def normalMetric (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (pz : Space × Space) : MetricTensor (V := Space) :=
  pullbackMetric (fun z => affineMetric g B (pz.1,z)) (metricJet g B pz.1) pz.2

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialGeometricCoefficient
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (p : X)

def antiDdcVector (u v : Space → Space) (z : Space) : Space :=
  (1/2:ℝ) • ((fderiv ℝ (coordinateJ J p) z (v z)) (u z) -
    (fderiv ℝ (coordinateJ J p) z (u z)) (v z) +
    (fderiv ℝ (coordinateJ J p) z (coordinateJ J p z (u z))) (coordinateJ J p z (v z)) -
    (fderiv ℝ (coordinateJ J p) z (coordinateJ J p z (v z))) (coordinateJ J p z (u z)))

lemma antiDdcVector_smooth {U : Set Space} (hU : IsOpen U)
    (hUt : U ⊆ (extChartAt Model p).target) {u v : Space → Space}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U) :
    ContDiffOn ℝ ∞ (antiDdcVector J p u v) U := by
  have hj := (coordinateJ_smooth J p).mono hUt
  have hd := hj.fderiv_of_isOpen hU (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact ContDiffOn.const_smul (1/2:ℝ) ((((hd.clm_apply hv).clm_apply hu).sub
    ((hd.clm_apply hu).clm_apply hv)).add
      ((hd.clm_apply (hj.clm_apply hu)).clm_apply (hj.clm_apply hv)) |>.sub
      ((hd.clm_apply (hj.clm_apply hv)).clm_apply (hj.clm_apply hu)))

variable {α : TwoForm X} {ht : Tames α J} (D : Data J α ht p)

def radialSourceVector (j : Fin 2) : Space → Space :=
  antiDdcVector J p (D.frame 0) (D.frame (if j = 0 then 2 else 3))

end TamingCompatibility.GeometricChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawJetEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator GeometricAdjoint Set Filter ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

def deltaComplexA (i : Fin 4) (z : Space) : C 2 →L[ℝ] MetricForms.Form Space 1 :=
  (deltaA J α ht p D i z).comp (retract 2)

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialScalarOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge LocalMatrixOperator
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : Data J α ht p)
lemma coordinateTest_smul (c : ℝ) (q : Space → EuclideanEnergy.Pair) :
    coordinateTest J α ht p D (c • q) = c • coordinateTest J α ht p D q := by
  funext z
  simp only [coordinateTest,frameTest,Pi.smul_apply,PiLp.smul_apply,smul_eq_mul]
  module
end TamingCompatibility.GeometricChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeWedgeEnergy
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricAdjoint _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

local instance instNormedAddCommGroupTangentSpaceRealSpaceModel_r3e2add_1 (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
  inferInstanceAs (NormedAddCommGroup Space)
local instance instNormedSpaceRealTangentSpaceSpaceModel_r3e2add_1 (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
local instance instFiniteDimensionalRealTangentSpaceSpaceModel_r3e2add_1 (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
  inferInstanceAs (FiniteDimensional ℝ Space)
lemma hodgeStar_add (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a b : TwoForm X) : starTwo J α ht (a+b) = starTwo J α ht a + starTwo J α ht b := by
  funext x
  ext v
  simp only [ManifoldHodge.starTwo,MetricHodge.starTwo,Pi.add_apply,
    MetricForms.pairing_add_left',ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sub_apply,ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,smul_eq_mul]
  ring

lemma hodgeStar_smul (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (c : ℝ) (a : TwoForm X) : starTwo J α ht (c • a) = c • starTwo J α ht a := by
  funext x
  ext v
  simp only [ManifoldHodge.starTwo,MetricHodge.starTwo,Pi.smul_apply,
    MetricForms.pairing_smul_left,ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,smul_eq_mul]
  ring

lemma hodgeStar_pairing (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a b : TwoForm X) (x : X) :
    pairing J α ht (starTwo J α ht a) b x = pairing J α ht a (starTwo J α ht b) x := by
  exact MetricHodge.starTwo_self_adjoint (pointMetric J α ht x) (J.endomorphism x : Space →L[ℝ] Space) (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
    (by change Module.finrank ℝ Space = 4; simp [Space]) (invariantPart J α x)
    (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm) (a x) (b x)

namespace GeometricHilbert
variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

local instance instNormedAddCommGroupTangentSpaceRealSpaceModel_r3e2add_2 (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
  inferInstanceAs (NormedAddCommGroup Space)
local instance instNormedSpaceRealTangentSpaceSpaceModel_r3e2add_2 (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
local instance instFiniteDimensionalRealTangentSpaceSpaceModel_r3e2add_2 (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
  inferInstanceAs (FiniteDimensional ℝ Space)
def preStar : PreL2 A J α hs ht true →ₗᵢ[ℝ] PreL2 A J α hs ht true where
  toFun a := ⟨starTwo J α ht a.val,starTwo_smooth J α hs ht a.property⟩
  map_add' a b := Subtype.ext (hodgeStar_add J α ht a.val b.val)
  map_smul' c a := Subtype.ext (hodgeStar_smul J α ht c a.val)
  norm_map' a := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [preL2_norm_sq,preL2_norm_sq]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      change pairing J α ht (starTwo J α ht a.val) (starTwo J α ht a.val) x = _
      rw [hodgeStar_pairing,starTwo_square])

def l2Star : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  ((smoothL2 A J α hs ht true).toContinuousLinearMap.comp
    (preStar A J α hs ht).toContinuousLinearMap).extend
      (smoothL2 A J α hs ht true).toContinuousLinearMap

@[simp] lemma l2Star_smooth (a : PreL2 A J α hs ht true) :
    l2Star A J α hs ht (smoothL2 A J α hs ht true a) =
      smoothL2 A J α hs ht true (preStar A J α hs ht a) := by
  exact ContinuousLinearMap.extend_eq _ (smoothL2_dense A J α hs ht true)
    (smoothL2 A J α hs ht true).isometry.isUniformInducing a

end GeometricHilbert
end TamingCompatibility

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameTest
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
open ManifoldForms ManifoldHodge HodgeFrame HodgeGeometricCoefficients GeometricChart
open Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
  (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)

def normalA (i : Fin 4) (z : Space) : HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q :=
  HodgeGeometricCoefficients.principal D.frame i z
def normalB (z : Space) : HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q :=
  HodgeGeometricCoefficients.lower (coordinateMetric J α ht p) (coordinateJ J p)
    (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm) D.frame z
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalMap
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

local instance instNormedAddCommGroupMetricTensorSpace_2_r3e2add_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_2_r3e2add_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
def normalMap (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q z : Space) : Space :=
  q + B q (coordinateJet (metricJet g B q) z)
def normalDifferential (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q z : Space) : Space →L[ℝ] Space :=
  (B q).comp (normalJacobian (metricJet g B q) z)

@[simp] lemma normalMap_zero (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) : normalMap g B q 0 = q := by
  simp [normalMap]
@[simp] lemma normalDifferential_zero (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) : normalDifferential g B q 0 = B q := by
  simp [normalDifferential]

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def pulledA (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p)
    (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (q : Space) (i : Fin 4) (z : Space) : W →L[ℝ] Q :=
  pullCoefficient (fun k => HodgeChart.normalA J α ht p D k (normalMap g B q z))
    (normalDifferential g B q z).inverse i

def pulledB (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p)
    (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (q z : Space) : W →L[ℝ] Q := HodgeChart.normalB J α ht p D (normalMap g B q z)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactExtension
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

local instance instNormedAddCommGroupMetricTensorSpace_4_r3e2add_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_4_r3e2add_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
def normalDensity (x : Space × Space) : ℝ := volumeDensity (normalMetric g B x)
def normalPrincipal (i j : Fin 4) (x : Space × Space) : ℝ := principal (normalMetric g B x) i j

def normalFirst (j : Fin 4) (x : Space × Space) : W →L[ℝ] W :=
  firstMatrix EuclideanEnergy.e (pulledA J α ht p D g B x.1)
    (pulledB J α ht p D g B x.1) (fun z => normalDensity g B (x.1,z)) j x.2

def normalZero (x : Space × Space) : W →L[ℝ] W :=
  zeroMatrix EuclideanEnergy.e (pulledA J α ht p D g B x.1)
    (pulledB J α ht p D g B x.1) (fun z => normalDensity g B (x.1,z)) x.2

def normalGauge (x : Space × Space) : W →L[ℝ] W :=
  gauge (halfJet (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4))
    (fun j => normalFirst J α ht p D g B j (x.1,0))) x.2

def gaugedFirst (j : Fin 4) (x : Space × Space) : W →L[ℝ] W :=
  gaugeFirst EuclideanEnergy.e (fun i j z => normalPrincipal g B i j (x.1,z))
    (fun j z => normalFirst J α ht p D g B j (x.1,z))
    (fun z => normalGauge J α ht p D g B (x.1,z)) j x.2

def gaugedZero (x : Space × Space) : W →L[ℝ] W :=
  gaugeZero EuclideanEnergy.e (fun i j z => normalPrincipal g B i j (x.1,z))
    (fun j z => normalFirst J α ht p D g B j (x.1,z))
    (fun z => normalZero J α ht p D g B (x.1,z))
    (fun z => normalGauge J α ht p D g B (x.1,z)) x.2

attribute [local irreducible] normalFirst

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeStarNormalGauge
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol HodgeStarGeometry FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

local instance hodgeStarNormalGaugeAngularMetricNormedAddCommGroup_r3e2add_1 :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeStarNormalGaugeAngularMetricNormedSpace_r3e2add_1 :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
@[simp] lemma normalGauge_zero (q : Space) : normalGauge J α ht p D g B (q,0) = 1 := by
  simp [normalGauge]

attribute [local irreducible] normalGauge normalFirst

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalDistribution
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply
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

def hodgeDelta : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht false where
  toFun a := ⟨codifferential J α ht a.val,GeometricAdjoint.codifferential_smooth J α hs ht a.property⟩
  map_add' a b := by
    apply Subtype.ext
    change codifferential J α ht (a.val+b.val) =
      codifferential J α ht a.val + codifferential J α ht b.val
    rw [codifferential,hodgeStar_add,
      exteriorDerivative_add (starTwo_smooth J α hs ht a.property) (starTwo_smooth J α hs ht b.property),
      starThree_add,neg_add]
    rfl
  map_smul' c a := by
    apply Subtype.ext
    change codifferential J α ht (c • a.val) = c • codifferential J α ht a.val
    rw [codifferential,hodgeStar_smul,exteriorDerivative_smul,starThree_smul]
    exact (smul_neg c _).symm

abbrev HodgeDerivativePair := WithLp 2 (L2 A J α hs ht false × L2 A J α hs ht false)
abbrev HodgeGraphSpace := WithLp 2 (L2 A J α hs ht true × HodgeDerivativePair A J α hs ht)

def hodgeGraph : PreL2 A J α hs ht true →ₗ[ℝ] HodgeGraphSpace A J α hs ht :=
  (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp <|
    (smoothL2 A J α hs ht true).toLinearMap.prod
      ((WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp <|
        ((smoothL2 A J α hs ht false).toLinearMap.comp (hodgeDelta A J α hs ht)).prod
          ((smoothL2 A J α hs ht false).toLinearMap.comp
            ((hodgeDelta A J α hs ht).comp (preStar A J α hs ht).toLinearMap)))

def hodgeEnergy : Submodule ℝ (HodgeGraphSpace A J α hs ht) :=
  (LinearMap.range (hodgeGraph A J α hs ht)).topologicalClosure

def hodgeInclusion : hodgeEnergy A J α hs ht →L[ℝ] L2 A J α hs ht true :=
  (WithLp.fstL 2 ℝ _ _) ∘L (hodgeEnergy A J α hs ht).subtypeL

def hodgeSmooth : PreL2 A J α hs ht true →ₗ[ℝ] hodgeEnergy A J α hs ht :=
  (hodgeGraph A J α hs ht).codRestrict _ (fun a => subset_closure ⟨a,rfl⟩)

@[simp] lemma hodgeInclusion_smooth (a : PreL2 A J α hs ht true) :
    hodgeInclusion A J α hs ht (hodgeSmooth A J α hs ht a) = smoothL2 A J α hs ht true a := rfl

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFiniteFrameResolution
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricAdjoint
open ManifoldForms ManifoldHodge
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
lemma pairing_two_chart (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (a b : TwoForm X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    MetricForms.pairing (coordinateMetric J α ht p z)
      (ManifoldForms.pullback a (extChartAt Model p).symm z)
      (ManifoldForms.pullback b (extChartAt Model p).symm z) =
      pairing J α ht a b ((extChartAt Model p).symm z) := by
  have he := MetricForms.pairing_two_comp (E := Space) (D := Space) (coordinateMetric J α ht p z)
    (pointMetric J α ht ((extChartAt Model p).symm z)) (inverseChartEquiv p z hz)
    (coordinateMetric_pullback J α ht p hz) (by simp [Space])
    (a ((extChartAt Model p).symm z)) (b ((extChartAt Model p).symm z))
  erw [inverseChartEquiv_coe] at he
  exact he
end TamingCompatibility.GeometricAdjoint

end
end

end

end OAI
end


