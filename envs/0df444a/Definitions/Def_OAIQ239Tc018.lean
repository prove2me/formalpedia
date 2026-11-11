-- Prove2me | Definitions.Def_OAIQ239Tc018
-- name    : OAIQ239Tc018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:40:33.859127+00:00
-- url     : https://prove2.me/theorems/5e2da19b-83ae-4307-a102-5531d920d304
-- title:
--   Definitions bundle OAIQ239Tc018 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 132 declarations of OpenAI's Lean: 84 definitions and 48 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.compactTimeIntegralMetricTensorNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.compactTimeIntegralMetricTensorNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.compactTimeIntegralPatchMetricTensorNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.compactTimeIntegralPatchMetricTensorNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.firstMatrixJointMetricTensorNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.firstMatrixJointMetricTensorNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.geometricMetricSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.geometricNormalChart`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixGaussianMetricNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixGaussianMetricNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixInitialMetricTensorNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixInitialMetricTensorNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixInitialSliceMetricTensorNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixInitialSliceMetricTensorNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeStarNormalGaugeAngularMetricNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeStarNormalGaugeAngularMetricNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeStarNormalGaugeCommuteMetricNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeStarNormalGaugeCommuteMetricNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricDerivativeSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_1`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_2`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_3`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_4`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_5`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_6`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricDerivativeSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_1`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_2`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_3`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_4`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_5`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_6`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingCoordinate`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingPatch`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalInverseMetricTensorNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalInverseMetricTensorNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDomainMetricTensorNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDomainMetricTensorNormedSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixLocalWeakMetricTensorNormedAddCommGroup` and 44 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_RadialUnitCoordinates`, `TamingCompatibility_Concentration_HodgeCompactResidual`, `TamingCompatibility_Concentration_HodgeResidualFamily`, `TamingCompatibility_Concentration_HodgeResidualPush`, `TamingCompatibility_Currents_NormalDensityJacobian`, `TamingCompatibility_Currents_PlaneFirstVariation`, `TamingCompatibility_Currents_PlaneMeasure`, `TamingCompatibility_Currents_PlaneTest`, `TamingCompatibility_DifferentialForms_Dpos`, `TamingCompatibility_DifferentialForms_Dpos2`, `TamingCompatibility_DifferentialForms_EuclideanUnitPlanes`, `TamingCompatibility_DifferentialForms_FirstMatrixJoint`, `TamingCompatibility_DifferentialForms_PlaneConvolution`, `TamingCompatibility_DifferentialForms_PlaneTransverseGraph`, `TamingCompatibility_DifferentialForms_PositiveTestMass`, `TamingCompatibility_DifferentialForms_RadialGeometricAssembly`, `TamingCompatibility_DifferentialForms_UnitTransverseCut`, `TamingCompatibility_Functional_GeometricQuadraticMass`, `TamingCompatibility_Functional_NormalMap`, `TamingCompatibility_HeatFlow_HodgeResolvent`, `TamingCompatibility_Hodge_HodgeChartScalar`, `TamingCompatibility_Hodge_HodgeCompactExtension`, `TamingCompatibility_Hodge_HodgeCompactTimeIntegral`, `TamingCompatibility_Hodge_HodgeFiniteFrameResolution`, `TamingCompatibility_Hodge_HodgeFrameTest`, `TamingCompatibility_Hodge_HodgeGeometricDistance`, `TamingCompatibility_Hodge_HodgeGlobalSmooth`, `TamingCompatibility_Hodge_HodgeLocalSmooth`, `TamingCompatibility_Hodge_HodgeNormalDistribution`, `TamingCompatibility_Hodge_HodgeNormalInverse`, `TamingCompatibility_Hodge_HodgeParametrixDomain`, `TamingCompatibility_Hodge_HodgeParametrixGaussian`, `TamingCompatibility_Hodge_HodgeParametrixInitial`, `TamingCompatibility_Hodge_HodgeParametrixLocalWeak`, `TamingCompatibility_Hodge_HodgeParametrixPatch`, `TamingCompatibility_Hodge_HodgeParametrixWeakEquation`, `TamingCompatibility_Hodge_HodgePatchAllCenters`, `TamingCompatibility_Hodge_HodgeStarNormalGauge`, `TamingCompatibility_Hodge_SmoothCorrection`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc014` and `OAIQ239Tc015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc021`, `OAIQ239Tc022`, `OAIQ239Tc023` and `OAIQ239Tc024`; the statements `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData.jets`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gaugedFirst_center`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_unitary`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normal_density_principal_jets`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_joint`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_scalar_at`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_weighted_principal` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledB_joint`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.centeredDisplacement_hasFDerivAt`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gaugedFirst_center`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_unitary`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMetric_dpos_zero`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normal_density_principal_jets`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_joint`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_weighted_principal` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledB_joint`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc014
import Definitions.Def_OAIQ239Tc015

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_SmoothCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def smoothAntiProjection : smoothForms X 2 →ₗ[ℝ] antiPre A J α hs ht where
  toFun β := ⟨⟨antiInvariantPart J β.val, IsSmooth.antiInvariantPart β.property J⟩,
    antiInvariantPart_idempotent J β.val⟩
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    exact antiInvariantPart_add J a.val b.val
  map_smul' c a := by
    apply Subtype.ext
    apply Subtype.ext
    exact antiInvariantPart_smul J c a.val

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialGeometricAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def smoothDdc (J : AlmostComplexStructure X) {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) : smoothForms X 2 :=
  ⟨exteriorDerivative (complexDifferential J f), (ddc_smooth_closed J hf).1⟩

end TamingCompatibility.ManifoldForms

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PositiveTestMass
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
open Bundle Set _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
attribute [local instance] unitMeasurable unitBorel

omit [IsManifold Model ∞ X] [T2Space X] in
lemma inverse_chart_compact_image (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    IsCompact ((extChartAt Model p).symm '' K) :=
  hK.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hKT)
end TamingCompatibility

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_RadialUnitCoordinates
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
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)

def unitChartDomain (p : X) (K : Set Space) : Set (MetricUnit (hermitianMetric J α hs ht)) :=
  {u | u.val.proj ∈ (extChartAt Model p).symm '' K}

def unitChartBase (p : X) (u : MetricUnit (hermitianMetric J α hs ht)) : Space :=
  extChartAt Model p u.val.proj

def unitChartVector (p : X) (u : MetricUnit (hermitianMetric J α hs ht)) : Space :=
  ((trivializationAt Space (TangentSpace Model) p) u.val).2

omit [CompactSpace X] in
lemma unitChartDomain_closed (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    _root_.IsClosed (unitChartDomain J α hs ht p K) :=
  (inverse_chart_compact_image p hK hKT).isClosed.preimage
    ((FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val)

omit [CompactSpace X] [T2Space X] in
lemma unitChart_mem (p : X) {K : Set Space} (hKT : K ⊆ (extChartAt Model p).target)
    {u : MetricUnit (hermitianMetric J α hs ht)} (hu : u ∈ unitChartDomain J α hs ht p K) :
    u.val.proj ∈ (extChartAt Model p).source ∧ unitChartBase J α hs ht p u ∈ K := by
  obtain ⟨z,hz,he⟩ := hu
  refine ⟨he ▸ (extChartAt Model p).map_target (hKT hz),?_⟩
  change extChartAt Model p u.val.proj ∈ K
  rw [← he,(extChartAt Model p).right_inv (hKT hz)]
  exact hz

omit [CompactSpace X] [T2Space X] in
lemma unitChartBase_continuousOn (p : X) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitChartBase J α hs ht p) (unitChartDomain J α hs ht p K) := by
  apply (continuousOn_extChartAt p).comp
    (((FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp
      continuous_subtype_val).continuousOn)
  exact fun u hu => (unitChart_mem J α hs ht p hKT hu).1

omit [CompactSpace X] [T2Space X] in
lemma unitChartVector_continuousOn (p : X) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitChartVector J α hs ht p) (unitChartDomain J α hs ht p K) := by
  intro u hu
  have hb : u.val.proj ∈ (trivializationAt Space (TangentSpace Model) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet,extChartAt_source] using
      (unitChart_mem J α hs ht p hKT hu).1
  exact (((trivializationAt Space (TangentSpace Model) p).continuousAt
    ((trivializationAt Space (TangentSpace Model) p).mem_source.mpr hb)).comp
      continuous_subtype_val.continuousAt).snd.continuousWithinAt

def unitRadialDefect (p : X) (b : Space) (u : MetricUnit (hermitianMetric J α hs ht)) : ℝ :=
  hermitianDefect (coordinateJ J p b) (unitChartBase J α hs ht p u-b)
    (unitChartVector J α hs ht p u)

def unitRadialRadius (p : X) (b : Space) (u : MetricUnit (hermitianMetric J α hs ht)) : ℝ :=
  ‖hermitianGraph (coordinateJ J p b) (unitChartBase J α hs ht p u-b)‖

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace
local instance instNormedAddCommGroupMetricDerivativeSpace : NormedAddCommGroup (NormalJets.MetricDerivative (V := ManifoldForms.Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricDerivativeSpace : NormedSpace ℝ (NormalJets.MetricDerivative (V := ManifoldForms.Space)) := ContinuousLinearMap.toNormedSpace
open ManifoldForms ManifoldHodge _root_.MeasureTheory Set Filter NormalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma frameMap_smooth {U : Set Space} (b : Fin 4 → Space → Space)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) :
    ContDiffOn ℝ ∞ (fun z => frameMap (fun i => b i z)) U := by
  apply ContDiffOn.sum
  intro i _
  exact contDiffOn_const.smulRight (hb i)

lemma exists_metric_frame_extension (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    {q : Space} (hq : q ∈ D.domain) :
    ∃ (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
      (U : Set Space), ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ B ∧
      IsOpen U ∧ q ∈ U ∧ U ⊆ D.domain ∧
      (∀ x ∈ U, g x = (coordinateMetric J α ht p x).bilinear) ∧
      (∀ x ∈ U, B x = frameMap (fun i => D.frame i x)) ∧
      (∀ x v w, g x v w = g x w v) := by
  obtain ⟨φ,hφ,hφD,U,hU,hqU,hUD,hφone⟩ := SchwartzCutoff.exists_one_near D.domain_open hq
  let g := SchwartzCutoff.schwartz D.domain_open
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) (φ.smooth ⊤) hφ hφD
  let B := SchwartzCutoff.schwartz D.domain_open
    (frameMap_smooth D.frame D.frame_smooth) (φ.smooth ⊤) hφ hφD
  refine ⟨g,B,U,g.smooth ⊤,B.smooth ⊤,hU,hqU,hUD,?_,?_,?_⟩
  · intro x hx
    simp [g,SchwartzCutoff.schwartz_apply,hφone x hx]
  · intro x hx
    simp [B,SchwartzCutoff.schwartz_apply,hφone x hx]
  · intro x v w
    simp only [g,SchwartzCutoff.schwartz_apply,_root_.smul_apply,smul_eq_mul]
    rw [(coordinateMetric J α ht p x).symm]

lemma affineMetric_contDiff (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (affineMetric g B) := by
  apply contDiff_clm_apply_iff.mpr
  intro v
  apply contDiff_clm_apply_iff.mpr
  intro w
  have hBc : ContDiff ℝ ∞ (fun pz : Space × Space => B pz.1) := hB.comp contDiff_fst
  exact ((hg.comp (contDiff_fst.add (hBc.clm_apply contDiff_snd))).clm_apply
    (hBc.clm_apply contDiff_const)).clm_apply (hBc.clm_apply contDiff_const)

lemma metricJet_contDiff (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (metricJet g B) :=
  (UniformJets.dpos_contDiff _ (affineMetric_contDiff g B hg hB)).comp
    (contDiff_id.prodMk contDiff_const)

lemma normalMetric_contDiff (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (normalMetric g B) := by
  have hG : ContDiff ℝ ∞ (metricJet g B) := metricJet_contDiff g B hg hB
  have hJ : ContDiff ℝ ∞ (fun pz : Space × Space =>
      normalJacobian (metricJet g B pz.1) pz.2) :=
    contDiff_const.sub (((christoffel_contDiff.comp hG).comp contDiff_fst).clm_apply contDiff_snd)
  have hM : ContDiff ℝ ∞ (fun pz : Space × Space =>
      affineMetric g B (pz.1, coordinateJet (metricJet g B pz.1) pz.2)) :=
    (affineMetric_contDiff g B hg hB).comp
      (contDiff_fst.prodMk (jointJet_contDiff _ hG))
  apply contDiff_clm_apply_iff.mpr
  intro v
  apply contDiff_clm_apply_iff.mpr
  intro w
  change ContDiff ℝ ∞ (fun pz : Space × Space =>
    affineMetric g B (pz.1, coordinateJet (metricJet g B pz.1) pz.2)
      (normalJacobian (metricJet g B pz.1) pz.2 v)
      (normalJacobian (metricJet g B pz.1) pz.2 w))
  exact (hM.clm_apply (hJ.clm_apply contDiff_const)).clm_apply (hJ.clm_apply contDiff_const)

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeChartScalar
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

def scalar (p : A.centers) (a : TwoForm X) (j : Fin 6) : Space → ℝ :=
  (D p).domain.indicator (fun x => localizedFunction A p a x ![(D p).frame (pairLeft j) x,(D p).frame (pairRight j) x])

end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameTest
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

def coordinateTest (q : Space → HodgeNormalSymbol.W) (z : Space) : MetricForms.Form Space 2 :=
  reconstruct (coordinateMetric J α ht p z) (fun i => D.frame i z) (q z)
omit [T2Space X] in
lemma coordinateTest_zero {q : Space → HodgeNormalSymbol.W} {z : Space} (hz : q z = 0) :
    coordinateTest J α ht p D q z = 0 := by
  simp only [coordinateTest,hz,map_zero]
omit [T2Space X] in
lemma coordinateTest_support (q : Space → HodgeNormalSymbol.W) :
    tsupport (coordinateTest J α ht p D q) ⊆ tsupport q := by
  apply closure_mono
  intro z hz
  by_contra hn
  apply hz
  exact coordinateTest_zero J α ht p D (by simpa only [Function.mem_support, not_not] using hn)
include hs in
omit [T2Space X] in
lemma coordinateTest_smooth {q : Space → HodgeNormalSymbol.W} (hq : ContDiff ℝ ∞ q)
    (hqD : tsupport q ⊆ D.domain) : ContDiff ℝ ∞ (coordinateTest J α ht p D q) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport q
  · have hψ := HodgeFrame.basisForm_smooth
      ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth
    change ContDiffAt ℝ ∞ (fun y => ∑ j, q y j • basisForm (coordinateMetric J α ht p y)
      (fun i => D.frame i y) j) z
    apply ContDiffAt.sum
    intro j _
    exact (((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hq).contDiffAt).smul
      ((hψ j z (hqD hz)).contDiffAt (D.domain_open.mem_nhds (hqD hz)))
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport q).isOpen_compl.mem_nhds hz] with y hy
    exact coordinateTest_zero J α ht p D (image_eq_zero_of_notMem_tsupport hy)
omit [T2Space X] in
lemma coordinateTest_compact {q : Space → HodgeNormalSymbol.W} (hc : HasCompactSupport q) :
    HasCompactSupport (coordinateTest J α ht p D q) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (coordinateTest_support J α ht p D q)

def manifoldTest (q : Space → HodgeNormalSymbol.W) : TwoForm X :=
  chartLift p (coordinateTest J α ht p D q)
include hs in
lemma manifoldTest_smooth {q : Space → HodgeNormalSymbol.W} (hq : ContDiff ℝ ∞ q)
    (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain) :
    IsSmooth (manifoldTest J α ht p D q) :=
  chartLift_smooth p (coordinateTest_smooth J α hs ht p D hq hqD)
    (coordinateTest_compact J α ht p D hc)
    ((coordinateTest_support J α ht p D q).trans (hqD.trans D.domain_subset))
omit [T2Space X] in
lemma pullback_manifoldTest (q : Space → HodgeNormalSymbol.W)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (manifoldTest J α ht p D q) (extChartAt Model p).symm z =
      coordinateTest J α ht p D q z := pullback_chartLift p _ hz

def rawVector (a : TwoForm X) (z : Space) : HodgeNormalSymbol.W :=
  coordinates (fun i => D.frame i z) (ManifoldForms.pullback a (extChartAt Model p).symm z)
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_NormalDensityJacobian
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupMetricTensorSpace_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalMap
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
local instance instNormedAddCommGroupMetricTensorSpace_2 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_2 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos2
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupMetricTensorSpace_3 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_3 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

lemma normalMap_joint (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (fun x : Space × Space => normalMap g B x.1 x.2) :=
  contDiff_fst.add ((hB.comp contDiff_fst).clm_apply
    (jointJet_contDiff (metricJet g B) (metricJet_contDiff g B hg hB)))

lemma normalDifferential_joint (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (fun x : Space × Space => normalDifferential g B x.1 x.2) := by
  have hJ : ContDiff ℝ ∞ (fun x : Space × Space => normalJacobian (metricJet g B x.1) x.2) :=
    contDiff_const.sub (((christoffel_contDiff.comp (metricJet_contDiff g B hg hB)).comp
      contDiff_fst).clm_apply contDiff_snd)
  exact (hB.comp contDiff_fst).clm_comp hJ

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def regularSet (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p) (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) : Set (Space × Space) :=
  {x | normalMap g B x.1 x.2 ∈ D.domain ∧ (normalDifferential g B x.1 x.2).IsInvertible}

lemma regularSet_open (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p) (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    IsOpen (regularSet J α ht p D g B) := by
  exact (D.domain_open.preimage (normalMap_joint g B hg hB).continuous).inter
    ((ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := Space) (F := Space)).preimage
      (normalDifferential_joint g B hg hB).continuous)

lemma regularSet_center (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p) (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (q : Space) (hq : q ∈ D.domain) (hBq : (B q).IsInvertible) :
    (q,0) ∈ regularSet J α ht p D g B := by
  exact ⟨by simpa using hq,by simpa using hBq⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FirstMatrixJoint
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance firstMatrixJointMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance firstMatrixJointMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactExtension
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
local instance instNormedAddCommGroupMetricTensorSpace_4 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_4 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

attribute [local irreducible] normalFirst

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeCompactResidual
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
local instance instNormedAddCommGroupMetricTensorSpace_5 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_5 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

attribute [local irreducible] normalFirst

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupMetricTensorSpace_6 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_6 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalPrincipal normalGauge gaugedFirst gaugedZero

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalInverse
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance normalInverseMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance normalInverseMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
  (q : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q = Bq)

def geometricNormalChart : OpenPartialHomeomorph (Space × Space) (Space × Space) :=
  centeredChart B (metricJet g B) hB (metricJet_contDiff g B hg hB) q Bq hBq

lemma geometricNormalChart_apply (x : Space × Space) :
    geometricNormalChart g B hg hB q Bq hBq x = (x.1,normalMap g B x.1 x.2) := rfl

lemma geometricNormalChart_smooth :
    ContDiff ℝ ∞ (geometricNormalChart g B hg hB q Bq hBq : Space × Space → Space × Space) :=
  centeredMap_contDiff B (metricJet g B) hB (metricJet_contDiff g B hg hB)

lemma geometricNormalChart_center :
    (q,q) ∈ inverseRegularDomain (geometricNormalChart g B hg hB q Bq hBq) := by
  refine ⟨centeredChart_mem_target B (metricJet g B) hB (metricJet_contDiff g B hg hB) q Bq hBq,?_⟩
  change (fderiv ℝ (centeredMap B (metricJet g B))
    ((centeredChart B (metricJet g B) hB (metricJet_contDiff g B hg hB) q Bq hBq).symm (q,q))).IsInvertible
  rw [centeredChart_symm_center]
  have hd := centeredMap_hasStrictFDerivAt B (metricJet g B) hB (metricJet_contDiff g B hg hB) q Bq hBq
  rw [hd.hasFDerivAt.fderiv]
  exact ⟨centeredDerivative Bq,rfl⟩

lemma geometricNormalChart_symm_fst {x : Space × Space}
    (hx : x ∈ (geometricNormalChart g B hg hB q Bq hBq).target) :
    ((geometricNormalChart g B hg hB q Bq hBq).symm x).1 = x.1 := by
  have he := (geometricNormalChart g B hg hB q Bq hBq).right_inv hx
  change ((geometricNormalChart g B hg hB q Bq hBq).symm x).1 = x.1
  simpa only [geometricNormalChart_apply] using congrArg Prod.fst he

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixDomain
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance parametrixDomainMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance parametrixDomainMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixPatch
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance parametrixPatchMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance parametrixPatchMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] normalGauge normalFirst

def leadingCoordinate (ψ χ : Space → ℝ) (t : ℝ) (x : Space × Space) : W →L[ℝ] W :=
  (ψ x.1 * χ x.2 * FlatHeat.heat t x.2) • normalGauge J α ht p D g B x

def leadingPatch (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (t : ℝ) : Space × Space → W →L[ℝ] W :=
  KernelExtension.push (geometricNormalChart g B hg hB q₀ Bq hBq)
    (leadingCoordinate J α ht p D g B ψ χ t)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixGaussian
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set _root_.MeasureTheory
open HodgeNormalSymbol FirstJetGauge OrthogonalJets UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance hodgeParametrixGaussianMetricNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeParametrixGaussianMetricNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

attribute [local irreducible] normalGauge normalFirst

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeResidualFamily
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
local instance residualFamilyMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance residualFamilyMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalGauge normalPrincipal gaugedFirst gaugedZero

def residualCoordinate (ψ χ : Space → ℝ) (t : ℝ) (x : Space × Space) : W →L[ℝ] W :=
  ψ x.1 • ((normalGauge J α ht p D g B x) ∘L
    NormalHeatResidual.residual
      (fun z => CutoffFamilies.principal (normalPrincipal g B) χ (x.1,z))
      (fun z => CutoffFamilies.first (normalPrincipal g B) (gaugedFirst J α ht p D g B) χ (x.1,z))
      (fun z => CutoffFamilies.zero (normalPrincipal g B) (gaugedFirst J α ht p D g B)
        (gaugedZero J α ht p D g B) χ (x.1,z)) t x.2)

def residualPatch (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (t : ℝ) : Space × Space → W →L[ℝ] W :=
  KernelExtension.push (geometricNormalChart g B hg hB q₀ Bq hBq)
    (residualCoordinate J α ht p D g B ψ χ t)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeResidualPush
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
local instance residualPushMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance residualPushMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_EuclideanUnitPlanes
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)

omit [CompactSpace X] [T2Space X] in
lemma unitChartVector_ne_zero (p : X) (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p).source) : unitChartVector J α hs ht p u ≠ 0 := by
  let t := trivializationAt Space (TangentSpace Model) p
  have hb : u.val.proj ∈ t.baseSet := by
    simpa only [t,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hu
  have hv : t.symmL ℝ u.val.proj (unitChartVector J α hs ht p u) = u.val.2 := by
    change t.symmL ℝ u.val.proj ((t u.val).2) = _
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ t hb]
    exact t.symmL_continuousLinearMapAt hb _
  intro h
  rw [h,map_zero] at hv
  have hh := u.property
  rw [← hv] at hh
  simp at hh

def unitChartJVector (p : X) (u : MetricUnit (hermitianMetric J α hs ht)) : Space :=
  coordinateJ J p (unitChartBase J α hs ht p u) (unitChartVector J α hs ht p u)

def unitChartFirst (p : X) (u : MetricUnit (hermitianMetric J α hs ht)) : Space :=
  first (unitChartVector J α hs ht p u)

def unitChartSecond (p : X) (u : MetricUnit (hermitianMetric J α hs ht)) : Space :=
  second (unitChartVector J α hs ht p u) (unitChartJVector J α hs ht p u)

def unitChartArea (p : X) (u : MetricUnit (hermitianMetric J α hs ht)) : ℝ :=
  area (unitChartVector J α hs ht p u) (unitChartJVector J α hs ht p u)

omit [CompactSpace X] [T2Space X] in
lemma unitChartPlane (p : X) (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p).source) :
    ‖unitChartFirst J α hs ht p u‖ = 1 ∧ ‖unitChartSecond J α hs ht p u‖ = 1 ∧
      ⟪unitChartFirst J α hs ht p u,unitChartSecond J α hs ht p u⟫ = 0 ∧
      0 < unitChartArea J α hs ht p u := by
  have ha := unitChartVector_ne_zero J α hs ht p u hu
  have hab : normalPart (unitChartVector J α hs ht p u) (unitChartJVector J α hs ht p u) ≠ 0 :=
    normalPart_complex_ne_zero _ (coordinateJ_square J p ((extChartAt Model p).map_source hu)) ha
  exact ⟨norm_first ha,norm_second hab,first_second_orthogonal ha _,area_pos ha hab⟩

omit [CompactSpace X] [T2Space X] in
lemma unitChartJVector_continuousOn (p : X) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitChartJVector J α hs ht p) (unitChartDomain J α hs ht p K) := by
  exact ((coordinateJ_smooth J p).continuousOn.comp
    (unitChartBase_continuousOn J α hs ht p hKT)
    (fun u hu => hKT (unitChart_mem J α hs ht p hKT hu).2)).clm_apply
      (unitChartVector_continuousOn J α hs ht p hKT)

omit [CompactSpace X] [T2Space X] in
lemma unitChartArea_continuousOn (p : X) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitChartArea J α hs ht p) (unitChartDomain J α hs ht p K) := by
  intro u hu
  apply ContinuousAt.comp_continuousWithinAt
    (f := fun v => (unitChartVector J α hs ht p v,unitChartJVector J α hs ht p v))
    (area_continuousAt (b := unitChartJVector J α hs ht p u)
      (unitChartVector_ne_zero J α hs ht p u (unitChart_mem J α hs ht p hKT hu).1))
  exact ((unitChartVector_continuousOn J α hs ht p hKT) u hu).prodMk
    ((unitChartJVector_continuousOn J α hs ht p hKT) u hu)

lemma unitChartArea_bounds (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ m C : ℝ, 0 < m ∧ 0 < C ∧ ∀ u ∈ unitChartDomain J α hs ht p K,
      m ≤ unitChartArea J α hs ht p u ∧ unitChartArea J α hs ht p u ≤ C := by
  have hS := (unitChartDomain_closed J α hs ht p hK hKT).isCompact
  have hc := unitChartArea_continuousOn J α hs ht p hKT
  have hp : ∀ u ∈ unitChartDomain J α hs ht p K, 0 < unitChartArea J α hs ht p u :=
    fun u hu => (unitChartPlane J α hs ht p u (unitChart_mem J α hs ht p hKT hu).1).2.2.2
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn hc
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn (hc.inv₀ (fun u hu => ne_of_gt (hp u hu)))
  refine ⟨(max M 1)⁻¹,max C 1,by positivity,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro u hu
  have hpos := hp u hu
  have hm := hM u hu
  have hc' := hC u hu
  change ‖(unitChartArea J α hs ht p u)⁻¹‖ ≤ M at hm
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos)] at hm
  rw [Real.norm_eq_abs,abs_of_pos hpos] at hc'
  refine ⟨?_,hc'.trans (le_max_left _ _)⟩
  exact (inv_le_comm₀ hpos (lt_of_lt_of_le zero_lt_one (le_max_right M 1))).mp
    (hm.trans (le_max_left _ _))
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_PlaneMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel 

def planeAreaCut (p : X) (K : Set Space) : MetricUnit (hermitianMetric J α hs ht) → ℝ :=
  (unitChartDomain J α hs ht p K).indicator (unitChartArea J α hs ht p)

def planeBaseCut (p : X) (K : Set Space) : MetricUnit (hermitianMetric J α hs ht) → Space :=
  (unitChartDomain J α hs ht p K).indicator (unitChartBase J α hs ht p)

omit [CompactSpace X] in
lemma planeAreaCut_measurable (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) : Measurable (planeAreaCut J α hs ht p K) := by
  classical
  exact (unitChartArea_continuousOn J α hs ht p hKT).measurable_piecewise continuousOn_const
    (unitChartDomain_closed J α hs ht p hK hKT).measurableSet

omit [CompactSpace X] [T2Space X] in
lemma planeAreaCut_nonneg (p : X) (K : Set Space) (u : MetricUnit (hermitianMetric J α hs ht)) :
    0 ≤ planeAreaCut J α hs ht p K u := by
  apply indicator_nonneg _ u
  intro v _
  exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

lemma planeAreaCut_integrable (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    Integrable (planeAreaCut J α hs ht p K) μ := by
  obtain ⟨m,C,_,hC,hbound⟩ := unitChartArea_bounds J α hs ht p hK hKT
  apply (integrable_const C).mono' (planeAreaCut_measurable J α hs ht p hK hKT).aestronglyMeasurable
  apply ae_of_all
  intro u
  rw [Real.norm_eq_abs,abs_of_nonneg (planeAreaCut_nonneg J α hs ht p K u)]
  by_cases hu : u ∈ unitChartDomain J α hs ht p K
  · exact (indicator_of_mem hu _).le.trans (hbound u hu).2
  · rw [planeAreaCut,indicator_of_notMem hu]
    exact hC.le

def planeMeasure (p : X) (K : Set Space)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) : Measure Space :=
  (μ.withDensity (fun u => ENNReal.ofReal (planeAreaCut J α hs ht p K u))).map
    (planeBaseCut J α hs ht p K)

lemma planeMeasure_finite (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    IsFiniteMeasure (planeMeasure J α hs ht p K μ) := by
  have hi := planeAreaCut_integrable J α hs ht p hK hKT μ
  have hp := planeAreaCut_nonneg J α hs ht p K
  have hh : ∫⁻ u, ENNReal.ofReal (planeAreaCut J α hs ht p K u) ∂μ ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hp)]
    exact ENNReal.ofReal_ne_top
  let := isFiniteMeasure_withDensity hh
  exact inferInstanceAs (IsFiniteMeasure (Measure.map _ (μ.withDensity _)))

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_PlaneTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel 

def planeCurrentTest (p : X) (h : Space → ℝ) (v : Space)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (hT : tsupport h ⊆ (extChartAt Model p).target) : smoothForms X 2 :=
  ⟨exteriorDerivative (chartLift p (testOne h v)),
    (chartLift_smooth p (testOne_smooth hh v) (testOne_compact hc v)
      ((testOne_support h v).trans hT)).exteriorDerivative⟩

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PlaneTransverseGraph
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

def unitTransverse (p : X) (b : Space) (u : MetricUnit (hermitianMetric J α hs ht)) : Space :=
  transverse (unitChartFirst J α hs ht p u) (unitChartSecond J α hs ht p u)
    (unitChartBase J α hs ht p u-b)

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PlaneConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel 

def planeConvolution (p : X) (K : Set Space)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (k : Space → ℝ) (b : Space) : ℝ :=
  ∫ y, k (b-y) ∂planeMeasure J α hs ht p K μ

lemma planeConvolution_smooth (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (k : Space → ℝ) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    ContDiff ℝ ∞ (planeConvolution J α hs ht p K μ k) := by
  let := planeMeasure_finite J α hs ht p hK hKT μ
  exact finite_convolution_smooth _ k hk hc

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_PlaneFirstVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel 

lemma reflected_smooth (k : Space → ℝ) (hk : ContDiff ℝ ∞ k) (b : Space) :
    ContDiff ℝ ∞ (fun y => k (b-y)) := hk.comp (contDiff_const.sub contDiff_id)

lemma reflected_compact (k : Space → ℝ) (hc : HasCompactSupport k) (b : Space) :
    HasCompactSupport (fun y => k (b-y)) := hc.comp_homeomorph (Homeomorph.subLeft b)

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitTransverseCut
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

def unitDistanceCut (p : X) (b : Space) (K : Set Space) :
    MetricUnit (hermitianMetric J α hs ht) → ℝ :=
  (unitChartDomain J α hs ht p K).indicator (fun u => ‖unitChartBase J α hs ht p u-b‖)

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_GeometricQuadraticMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility
open Bundle Manifold ManifoldForms ManifoldVolume GeometricHilbert Set _root_.MeasureTheory
open scoped Bundle Manifold ContDiff ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] unitMeasurable unitBorel 

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X] in

def hermitianEDist (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) : X → X → ℝ≥0∞ :=
  letI : RiemannianBundle (TangentSpace Model : X → Type) :=
    ⟨(hermitianMetric J α hs ht).toRiemannianMetric⟩
  riemannianEDist Model

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalDistribution
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

def hodgeWeakDerivative : hodgeEnergy A J α hs ht →L[ℝ] HodgeDerivativePair A J α hs ht :=
  (WithLp.sndL 2 ℝ _ _) ∘L (hodgeEnergy A J α hs ht).subtypeL

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
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero
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

def hodgeScaledDerivative (r : ℝ) : hodgeEnergy A J α hs ht →L[ℝ] HodgeDerivativePair A J α hs ht :=
  r • hodgeWeakDerivative A J α hs ht

@[simp] lemma hodgeScaledDerivative_apply (r : ℝ) (u : hodgeEnergy A J α hs ht) :
    hodgeScaledDerivative A J α hs ht r u = r • hodgeWeakDerivative A J α hs ht u := rfl

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeStarNormalGauge
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open HodgeNormalSymbol HodgeStarGeometry FirstJetGauge OrthogonalJets Filter Set OperatorCalculus
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance hodgeStarNormalGaugeCommuteMetricNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeStarNormalGaugeCommuteMetricNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol HodgeStarGeometry FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance hodgeStarNormalGaugeAngularMetricNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeStarNormalGaugeAngularMetricNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

attribute [local irreducible] normalGauge normalFirst

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixInitial
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set _root_.MeasureTheory
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance hodgeParametrixInitialMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeParametrixInitialMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

attribute [local irreducible] normalGauge normalFirst

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set _root_.MeasureTheory
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance hodgeParametrixInitialSliceMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeParametrixInitialSliceMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactTimeIntegral
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance compactTimeIntegralMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance compactTimeIntegralMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance compactTimeIntegralPatchMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance compactTimeIntegralPatchMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixLocalWeak
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance parametrixLocalWeakMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance parametrixLocalWeakMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalPrincipal normalGauge gaugedFirst gaugedZero

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixWeakEquation
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance parametrixWeakEquationMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance parametrixWeakEquationMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalPrincipal normalGauge gaugedFirst gaugedZero

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance parametrixDataMetricTensorNormedAddCommGroup_r7a7433_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance parametrixDataMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePatchAllCenters
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.ManifoldLocalization
open Set ManifoldForms
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X)

def squareMass (x : X) : ℝ := ∑ p : A.centers, (A.partition p x)^2

lemma squareMass_pos (x : X) : 0 < squareMass A x := by
  classical
  have he : ∃ p : A.centers, A.partition p x ≠ 0 := by
    by_contra h
    push Not at h
    have hh := partition_sum A x
    simp only [h,Finset.sum_const_zero] at hh
    norm_num at hh
  obtain ⟨p,hp⟩ := he
  exact (sq_pos_of_ne_zero hp).trans_le
    (Finset.single_le_sum (fun q _ => sq_nonneg (A.partition q x)) (Finset.mem_univ p))

lemma squareMass_smooth : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (squareMass A) := by
  exact ContMDiff.sum (fun p _ => (A.partition p).contMDiff.pow 2)

lemma squareMass_inv_smooth : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (fun x => (squareMass A x)⁻¹) :=
  (squareMass_smooth A).inv₀ (fun x => ne_of_gt (squareMass_pos A x))

end TamingCompatibility.ManifoldLocalization

namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open HodgeNormalSymbol (W)
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma pairing_basisForm (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (a : MetricForms.Form E 2) (j : Fin 6) :
    pairing g a (basisForm g b j) = coordinates b a j := by
  rw [← coordinates_pairing g hdim b hb]
  simp only [PiLp.inner_apply,coordinates_basisForm g b hb,RCLike.inner_apply,conj_trivial]
  simp

lemma basisForm_resolution (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (a : MetricForms.Form E 2) :
    ∑ j : Fin 6, pairing g a (basisForm g b j) • basisForm g b j = a := by
  simp_rw [pairing_basisForm g hdim b hb]
  exact (reconstruct_apply g b (coordinates b a)).symm.trans (reconstruct_coordinates g hdim b hb a)

end TamingCompatibility.HodgeFrame

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFiniteFrameResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms HodgeNormalSymbol
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma reconstruct_basisFun (g : Metric E) (b : Fin 4 → E) (j : Fin 6) :
    reconstruct g b (EuclideanSpace.basisFun (Fin 6) ℝ j) = basisForm g b j := by
  rw [reconstruct_apply]
  simp
end TamingCompatibility.HodgeFrame

end
end

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
lemma Smooth.sum {ι : Type*} (s : Finset ι) {k : ℕ} (a : ι → Form X k)
    (ha : ∀ i ∈ s, Smooth (a i)) : Smooth (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Smooth.zero (X := X) (k := k))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (ha i (Finset.mem_insert_self i s)).add (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))
end TamingCompatibility.ManifoldForms

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricDistance
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle Manifold ManifoldForms Set _root_.MeasureTheory
open scoped Bundle Manifold ContDiff ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X]

@[reducible] def geometricMetricSpace (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) : MetricSpace X := by
  let g := hermitianMetric J α hs ht
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type) :=
    ⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩
  let : EMetricSpace X := .ofRiemannianMetric Model X
  apply EMetricSpace.toMetricSpace
  intro x y
  have hb : Metric.eball x ⊤ = univ :=
    (show IsClopen (Metric.eball x ⊤) from
      ⟨Metric.isClosed_eball_top,Metric.isOpen_eball⟩).eq_univ ⟨x,by simp⟩
  have hy : y ∈ Metric.eball x ⊤ := by rw [hb]; trivial
  exact (by simpa only [Metric.mem_eball,edist_comm] using hy : edist x y < ⊤).ne

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

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

def hodgePreD : PreL2 A J α hs ht false →ₗ[ℝ] PreL2 A J α hs ht true where
  toFun a := ⟨exteriorDerivative a.val,a.property.exteriorDerivative⟩
  map_add' a b := Subtype.ext (exteriorDerivative_add a.property b.property)
  map_smul' c a := Subtype.ext (exteriorDerivative_smul c a.val)

def hodgeLaplacian : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true :=
  (hodgePreD A J α hs ht).comp (hodgeDelta A J α hs ht) +
    (preStar A J α hs ht).toLinearMap.comp ((hodgePreD A J α hs ht).comp
      ((hodgeDelta A J α hs ht).comp (preStar A J α hs ht).toLinearMap))

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalSmooth
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero
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
local instance instNormedAddCommGroupTangentSpaceRealSpaceModel_2 (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
  inferInstanceAs (NormedAddCommGroup Space)
local instance instNormedSpaceRealTangentSpaceSpaceModel_2_r7a7433_1 (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
local instance instFiniteDimensionalRealTangentSpaceSpaceModel_2 (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
  inferInstanceAs (FiniteDimensional ℝ Space)

lemma jAction_pairing (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a b : TwoForm X) (x : X) :
    pairing J α ht (TamingCompatibility.jAction J a) (TamingCompatibility.jAction J b) x =
      pairing J α ht a b x := by
  let L : TangentSpace Model x ≃L[ℝ] TangentSpace Model x :=
    (LinearEquiv.ofBijective (J.endomorphism x).toLinearMap
      ⟨J.injective x,J.surjective x⟩).toContinuousLinearEquiv
  exact MetricForms.pairing_two_comp (pointMetric J α ht x) (pointMetric J α ht x) L
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
    (by change Module.finrank ℝ Space = 4; simp [Space]) (a x) (b x)

namespace GeometricHilbert
variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

local instance instNormedSpaceRealTangentSpaceSpaceModel_2_r7a7433_2 (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
def preJAction : PreL2 A J α hs ht true →ₗᵢ[ℝ] PreL2 A J α hs ht true where
  toFun a := ⟨TamingCompatibility.jAction J a.val,IsSmooth.jAction a.property J⟩
  map_add' a b := Subtype.ext (TamingCompatibility.jAction_add J a.val b.val)
  map_smul' c a := Subtype.ext (TamingCompatibility.jAction_smul J c a.val)
  norm_map' a := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [preL2_norm_sq,preL2_norm_sq]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (jAction_pairing J α ht a.val a.val)

def l2JAction : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  ((smoothL2 A J α hs ht true).toContinuousLinearMap.comp
    (preJAction A J α hs ht).toContinuousLinearMap).extend
      (smoothL2 A J α hs ht true).toContinuousLinearMap

@[simp] lemma l2JAction_smooth (a : PreL2 A J α hs ht true) :
    l2JAction A J α hs ht (smoothL2 A J α hs ht true a) =
      smoothL2 A J α hs ht true (preJAction A J α hs ht a) := by
  exact ContinuousLinearMap.extend_eq _ (smoothL2_dense A J α hs ht true)
    (smoothL2 A J α hs ht true).isometry.isUniformInducing a

def l2AntiProjection : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  (1/2:ℝ) • (ContinuousLinearMap.id ℝ _ - l2JAction A J α hs ht)

@[simp] lemma l2AntiProjection_apply (a : L2 A J α hs ht true) :
    l2AntiProjection A J α hs ht a = (1/2:ℝ) • (a-l2JAction A J α hs ht a) := rfl

end GeometricHilbert
end TamingCompatibility

end
end

end
end

end OAI
end


