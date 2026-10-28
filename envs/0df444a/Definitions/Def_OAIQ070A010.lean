-- Prove2me | Definitions.Def_OAIQ070A010
-- name    : OAIQ070A010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T11:35:00.996706+00:00
-- url     : https://prove2.me/theorems/d8cb2836-742f-47d9-beea-e87e7cefec0b
-- title:
--   Definitions bundle OAIQ070A010 of the split of OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 88 declarations of OpenAI's Lean: 60 definitions and 28 theorems. The definitions and types are `OAI.YauCounterexamples.boundedPhaseSet`, `OAI.YauCounterexamples.chartTensorOfMetric`, `OAI.YauCounterexamples.circleRoundMetric`, `OAI.YauCounterexamples.complexPhaseMatrix`, `OAI.YauCounterexamples.fourProductInner`, `OAI.YauCounterexamples.fourProductMetric`, `OAI.YauCounterexamples.fourWaveCompact`, `OAI.YauCounterexamples.fourWaveEquiv`, `OAI.YauCounterexamples.frozenSobolevOperator`, `OAI.YauCounterexamples.fullStrictJetMap`, `OAI.YauCounterexamples.fullStrictJetSet`, `OAI.YauCounterexamples.laplaceDerivativeBCF`, `OAI.YauCounterexamples.linearPullbackMetric`, `OAI.YauCounterexamples.matrixJetMatrixMapNorm`, `OAI.YauCounterexamples.metricJetFull`, `OAI.YauCounterexamples.metricJetMap`, `OAI.YauCounterexamples.metricJetStrict`, `OAI.YauCounterexamples.metricTriNorm`, `OAI.YauCounterexamples.momentBesselLp`, `OAI.YauCounterexamples.phaseFrameMatrix`, `OAI.YauCounterexamples.phaseImagVector`, `OAI.YauCounterexamples.phaseRealVector`, `OAI.YauCounterexamples.physicalWaveJetMatrix`, `OAI.YauCounterexamples.profileFrequencyEnergy`, `OAI.YauCounterexamples.profileFrequencyScale`, `OAI.YauCounterexamples.rescaledDifferentialPerturbation`, `OAI.YauCounterexamples.sphericalTensorOf`, `OAI.YauCounterexamples.spnMatrixMapNorm`, `OAI.YauCounterexamples.tangentPhase`, `OAI.YauCounterexamples.testEnergy`, `OAI.YauCounterexamples.testGradientSquare`, `OAI.YauCounterexamples.testQuadratic`, `OAI.YauCounterexamples.testSchrodinger`, `OAI.YauCounterexamples.threeAmbientCircleGradient`, `OAI.YauCounterexamples.threeAmbientSphereGradient`, `OAI.YauCounterexamples.threeChartMap`, `OAI.YauCounterexamples.threeChartMetric`, `OAI.YauCounterexamples.threeCollar`, `OAI.YauCounterexamples.threeCoupled`, `OAI.YauCounterexamples.threeCoupledComplex` and 20 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `SmoothYau_DifferentialEq_SphericalOpenFormNorm`, `SmoothYau_Estimates_PhaseFormMatrix`, `SmoothYau_Estimates_RescaledDifferentialPerturbation`, `SmoothYau_Estimates_SphericalPinFormNorm`, `SmoothYau_Estimates_TestPairSubSquareBound`, `SmoothYau_Geometry_ActualHessianForm`, `SmoothYau_Geometry_CoefficientGradientApply`, `SmoothYau_Geometry_SymmLChartTrivialization`, `SmoothYau_Geometry_TestElliptic`, `SmoothYau_Geometry_ThreeLogNormedSpace`, `SmoothYau_Geometry_ZeroInterior`, `SmoothYau_Limits_ClosedPhaseMatrixValid`, `SmoothYau_Limits_PhaseImagVector`, `SmoothYau_ProductMetric_FourWaveThreeSmul`, `SmoothYau_ProductMetric_ThreeInteriorMeridianNormedSpace`, `SmoothYau_Smoothness_ChartTensorCoordLocal1`, `SmoothYau_Smoothness_ComplexPolarWeight`, `SmoothYau_Smoothness_ContinuousCompactSmoothJets`, `SmoothYau_Smoothness_ContinuousSobolevFirstDerivative`, `SmoothYau_Smoothness_DistanceSquare`, `SmoothYau_Smoothness_FourLiftThreeSmul`, `SmoothYau_Smoothness_LinearMetricForm`, `SmoothYau_Smoothness_MomentBesselLp`, `SmoothYau_Smoothness_PulledGradient`, `SmoothYau_Smoothness_SmDualNorm`, `SmoothYau_Smoothness_ThreeCoupledCleanChartJets`, `SmoothYau_Smoothness_ThreeRadiusNormedSpace`, `SmoothYau_Spectrum_JointLocalLaplacian`, `SmoothYau_Spectrum_ProfileFrequencyEnergy`, `SmoothYau_Spectrum_ThreeCoupledNormedSpace`, `SmoothYau_Spectrum_VaryingSpectralResolventBase`, `SmoothYau_SphereMetric_ExistsAlignedUnit`, `SmoothYau_SphereMetric_ExistsThreeScalarProducer`, `SmoothYau_SphereMetric_FourThree`, `SmoothYau_SphereMetric_ThreeExceptional`, `SmoothYau_SphereMetric_ThreeFixedFormNorm`, `SmoothYau_SphereMetric_ThreeFormulaNormedSpace`, `SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace`.
--
--   **Imports.** It imports the published bundle `Def_SmoothYau`; the bundles `OAIQ070A005`, `OAIQ070A006`, `OAIQ070A007` and `OAIQ070A008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ070A011`, `OAIQ070A012` and `OAIQ070A013`; the statements `OAI_YauCounterexamples_CompactMetricAtlas_eventually_product_scalar_factor_raw`, `OAI.YauCounterexamples.CompactMetricAtlas.scalarTestCLM_pinned_deriv`, `OAI.YauCounterexamples.admissible_cutoff_wave_residual`, `OAI.YauCounterexamples.all_admissible_generated_gaussian`, `OAI.YauCounterexamples.compact_actual_sign_noncancellation_supported`, `OAI.YauCounterexamples.compact_actual_waves_sign_and_jets_supported`, `OAI.YauCounterexamples.compact_actual_waves_subregions_supported`, `OAI.YauCounterexamples.compact_metric_packet_sign_gain`, `OAI_YauCounterexamples_compact_normal_forward_bound`, `OAI.YauCounterexamples.compact_packet_angular_gap`, `OAI.YauCounterexamples.exists_global_box_amplified_profile`, `OAI.YauCounterexamples.exists_global_spherical_wave_profile`, `OAI.YauCounterexamples.exists_local_weighted_carleman`, `OAI.YauCounterexamples.exists_spherical_simple_stage`, `OAI.YauCounterexamples.exists_supported_box_nodal_quasimodes_subregions`, `OAI.YauCounterexamples.exists_supported_nodal_quasimodes_subregions`, `OAI_YauCounterexamples_exists_threeCoupled_interior_gradient_rank`, `OAI.YauCounterexamples.exists_threeInteriorMeridianEnergy_deriv`, `OAI.YauCounterexamples.exists_three_chart_quasimodes_with_gaps`, `OAI.YauCounterexamples.exists_three_exact_stage`, `OAI.YauCounterexamples.exists_three_global_quasimodes`, `OAI.YauCounterexamples.exists_three_profile_seed`, `OAI.YauCounterexamples.exists_three_robust_exhaustible_envelopes`, `OAI.YauCounterexamples.exists_three_robust_global_profile_family`, `OAI.YauCounterexamples.exists_three_robust_seed`, `OAI.YauCounterexamples.exists_three_scalar_producer`, `OAI.YauCounterexamples.exists_three_simple_stage`, `OAI.YauCounterexamples.laplaceBeltrami_four_lift`, `OAI.YauCounterexamples.normal_family_canonical_smallBall_uniform`, `OAI.YauCounterexamples.normal_family_wave_localized_estimates`, `OAI.YauCounterexamples.physical_complex_wave_smallBall_uniform`, `OAI.YauCounterexamples.physical_finite_superposition_complete_supported`, `OAI_YauCounterexamples_roundPower_dominant_perturbation_jet_lower`, `OAI_YauCounterexamples_sphericalBaseProfile_neighborhood`, `OAI_YauCounterexamples_spherical_background_sign_small`, `OAI.YauCounterexamples.spherical_pin_near`, `OAI_YauCounterexamples_spherical_wave_centered_first_jet`, `OAI_YauCounterexamples_spherical_wave_lift_jets`, `OAI.YauCounterexamples.threeCoupled_ambient_derivative`, `OAI_YauCounterexamples_threeCoupled_clean_gradient_lower`, `OAI.YauCounterexamples.threeCoupled_conjugate_gradient_lower`, `OAI.YauCounterexamples.threeCoupled_conjugate_projection_uniform`, `OAI_YauCounterexamples_threeCoupled_dominated_chart_jets`, `OAI.YauCounterexamples.threeCoupled_dominated_residual_rapid_decay`, `OAI.YauCounterexamples.threeCoupled_global_noncancellation`, `OAI.YauCounterexamples.threeCoupled_global_residual_rapid_decay`, `OAI_YauCounterexamples_threeCoupled_gradient_chart_analytic`, `OAI.YauCounterexamples.threeCoupled_gradient_value`, `OAI_YauCounterexamples_threeCoupled_profile_rank_dense`, `OAI.YauCounterexamples.threeCoupled_profile_rank_somewhere`, `OAI.YauCounterexamples.threeGlobalLog_local`, `OAI.YauCounterexamples.threeLogEnvelope_trace`, `OAI.YauCounterexamples.threePacket_background_input_bounds`, `OAI_YauCounterexamples_threePower_eigen`, `OAI_YauCounterexamples_threeRadiusSq_second`, `OAI.YauCounterexamples.threeWaveLift_laplacian`, `OAI.YauCounterexamples.three_annular_projection_uniform`, `OAI.YauCounterexamples.three_clean_collar_gradient`, `OAI.YauCounterexamples.three_clean_conjugating_margin`, `OAI.YauCounterexamples.three_collar_rank`, `OAI_YauCounterexamples_three_exceptional_global_coverage`, `OAI.YauCounterexamples.three_exceptional_intrinsic_margin`, `OAI.YauCounterexamples.three_exterior_intrinsic_margin`, `OAI.YauCounterexamples.three_pin_near`, `OAI.YauCounterexamples.three_wave_background_chart_bounds`, `OAI.YauCounterexamples.three_wave_exterior_germ`, `OAI.YauCounterexamples.three_wave_lift_jets`, `OAI.YauCounterexamples.three_wave_residual_support`, `OAI.YauCounterexamples.uniform_coordinate_packets_with_endpoint_ratios_supported` and `OAI.YauCounterexamples.uniform_localized_physical_waves_with_coordinates_supported`; the proofs of `OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple`, `OAI_YauCounterexamples_CompactMetricAtlas_eventually_product_scalar_factor_raw`, `OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_factor_raw`, `OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent_compact`, `OAI.YauCounterexamples.CompactMetricAtlas.scalarTestCLM_pinned_deriv`, `OAI.YauCounterexamples.actual_metric_profile_cycle`, `OAI.YauCounterexamples.actual_metric_radial_finite`, `OAI.YauCounterexamples.actual_preparation_on_compact_patch`, `OAI.YauCounterexamples.admissible_cutoff_wave_residual`, `OAI.YauCounterexamples.all_admissible_generated_gaussian`, `OAI.YauCounterexamples.canonical_phase_triple_smallBall`, `OAI.YauCounterexamples.centered_inverse_for_normal_charts`, `OAI.YauCounterexamples.compact_actual_sign_noncancellation_supported`, `OAI.YauCounterexamples.compact_actual_waves_sign_and_jets_supported`, `OAI.YauCounterexamples.compact_actual_waves_subregions_supported`, `OAI.YauCounterexamples.compact_metric_packet_sign_gain`, `OAI.YauCounterexamples.compact_normal_image_neighborhood`, `OAI.YauCounterexamples.compact_packet_angular_gap`, `OAI.YauCounterexamples.compact_profile_three_phase_data`, `OAI.YauCounterexamples.contDiff_complexLaplaceBeltrami_self`, `OAI.YauCounterexamples.exists_actual_preparation_neighborhood`, `OAI.YauCounterexamples.exists_global_box_amplified_profile`, `OAI.YauCounterexamples.exists_global_spherical_wave_profile`, `OAI.YauCounterexamples.exists_local_metric_radial_patch`, `OAI.YauCounterexamples.exists_local_weighted_carleman`, `OAI.YauCounterexamples.exists_normal_wave_chart_family`, `OAI.YauCounterexamples.exists_spherical_chart_quasimodes`, `OAI.YauCounterexamples.exists_spherical_simple_stage`, `OAI.YauCounterexamples.exists_supported_box_nodal_quasimodes_subregions`, `OAI.YauCounterexamples.exists_supported_nodal_quasimodes_subregions`, `OAI.YauCounterexamples.exists_threeInteriorMeridianEnergy_deriv`, `OAI.YauCounterexamples.exists_three_chart_quasimodes_with_gaps`, `OAI.YauCounterexamples.exists_three_exact_stage`, `OAI.YauCounterexamples.exists_three_global_quasimodes`, `OAI.YauCounterexamples.exists_three_profile_seed`, `OAI_YauCounterexamples_exists_three_radial_cutoff`, `OAI.YauCounterexamples.exists_three_robust_exhaustible_envelopes`, `OAI.YauCounterexamples.exists_three_robust_global_profile_family`, `OAI.YauCounterexamples.exists_three_robust_seed`, `OAI.YauCounterexamples.exists_three_scalar_producer`, `OAI.YauCounterexamples.exists_three_simple_stage`, `OAI.YauCounterexamples.finiteWaveSuperposition_residual`, `OAI.YauCounterexamples.laplaceBeltrami_four_lift`, `OAI.YauCounterexamples.metric_center_polynomial_net_with_coverage`, `OAI.YauCounterexamples.nonempty_compactMetricAtlas`, `OAI.YauCounterexamples.normalChartWave_laplacian`, `OAI.YauCounterexamples.normal_family_canonical_smallBall_uniform`, `OAI.YauCounterexamples.normal_family_wave_localized_estimates`, `OAI.YauCounterexamples.physical_complex_wave_smallBall_uniform`, `OAI.YauCounterexamples.physical_finite_superposition_complete_supported`, `OAI.YauCounterexamples.proportional_eigen_global`, `OAI_YauCounterexamples_roundPower_dominant_perturbation_jet_lower`, `OAI_YauCounterexamples_smooth_first_integral`, `OAI_YauCounterexamples_source_baseProfile_sign_gradient`, `OAI.YauCounterexamples.sphere_two_torus_two`, `OAI.YauCounterexamples.sphericalBaseProfile_chart_margins`, `OAI.YauCounterexamples.sphericalMetricGood_neighborhood`, `OAI_YauCounterexamples_spherical_background_sign_small`, `OAI.YauCounterexamples.spherical_pin_near`, `OAI_YauCounterexamples_spherical_wave_lift_jets`, `OAI.YauCounterexamples.threeCoupled_ambient_derivative`, `OAI_YauCounterexamples_threeCoupled_clean_gradient_lower`, `OAI.YauCounterexamples.threeCoupled_conjugate_gradient_lower`, `OAI.YauCounterexamples.threeCoupled_conjugate_projection_uniform`, `OAI_YauCounterexamples_threeCoupled_dominated_chart_jets`, `OAI.YauCounterexamples.threeCoupled_dominated_residual_rapid_decay`, `OAI.YauCounterexamples.threeCoupled_global_noncancellation`, `OAI.YauCounterexamples.threeCoupled_global_residual_rapid_decay`, `OAI.YauCounterexamples.threeCoupled_gradient_value`, `OAI_YauCounterexamples_threeCoupled_profile_rank_dense`, `OAI.YauCounterexamples.threeCoupled_profile_rank_somewhere`, `OAI.YauCounterexamples.threeGlobalLog_local`, `OAI.YauCounterexamples.threeLogEnvelope_trace`, `OAI.YauCounterexamples.threePacket_background_input_bounds`, `OAI_YauCounterexamples_threePower_eigen`, `OAI.YauCounterexamples.threeWaveLift_laplacian`, `OAI.YauCounterexamples.three_annular_projection_uniform`, `OAI.YauCounterexamples.three_clean_collar_gradient`, `OAI.YauCounterexamples.three_clean_conjugating_margin`, `OAI.YauCounterexamples.three_collar_rank`, `OAI_YauCounterexamples_three_exceptional_global_coverage`, `OAI.YauCounterexamples.three_exceptional_intrinsic_margin`, `OAI.YauCounterexamples.three_exterior_intrinsic_margin`, `OAI.YauCounterexamples.three_pin_near`, `OAI.YauCounterexamples.three_wave_background_chart_bounds`, `OAI.YauCounterexamples.three_wave_exterior_germ`, `OAI.YauCounterexamples.three_wave_lift_jets`, `OAI.YauCounterexamples.three_wave_residual_support`, `OAI_YauCounterexamples_uniformSmoothWaveAmplitudes_genuine`, `OAI.YauCounterexamples.uniform_coordinate_packets_with_endpoint_ratios_supported` and `OAI.YauCounterexamples.uniform_localized_physical_waves_with_coordinates_supported`.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A005
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007
import Definitions.Def_OAIQ070A008

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.metricDualNorm
attribute [local instance] OAI.YauCounterexamples.metricDualSpace
attribute [local instance] OAI.YauCounterexamples.metricFormNorm
attribute [local instance] OAI.YauCounterexamples.metricFormSpace
local instance metricTriNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

attribute [local instance] OAI.YauCounterexamples.metricTriSpace
omit [FiniteDimensional ℝ E] in
lemma contDiff_selfMetricFlat (g : SmoothMetric E E) : ContDiff ℝ ∞ (selfMetricFlat g) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have h := contMDiffAt_localMetricFlat g x
  rw [contMDiffAt_iff_contDiffAt] at h
  have heq : localMetricFlat g x = selfMetricFlat g := funext (localMetricFlat_self g x)
  rwa [heq] at h


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_SymmLChartTrivialization
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
attribute [local instance] OAI.YauCounterexamples.tensorDualNorm
attribute [local instance] OAI.YauCounterexamples.tensorDualSpace
attribute [local instance] OAI.YauCounterexamples.tensorFormSpace
attribute [local instance] OAI.YauCounterexamples.tensorTangentDualAdd
attribute [local instance] OAI.YauCounterexamples.tensorTangentDualSmul
local instance tensorTangentFormAdd_re11c5f_1 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) :=
  inferInstance
local instance tensorTangentFormSmul_re11c5f_1 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance
omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartFormTrivialization_baseSet (p : M) :
    (chartFormTrivialization (E:=E) p).baseSet = (chartAt E p).source := by
  simp [chartFormTrivialization,hom_trivializationAt_baseSet,TangentBundle.trivializationAt_baseSet]

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartFormTrivialization_pairing (p : M) {x : M} (hx : x ∈ (chartAt E p).source)
    (B : TangentForm (E:=E) x) (v w : E) :
    (chartFormTrivialization (E:=E) p ⟨x,B⟩).2 v w =
      B ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symm x v)
        ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symm x w) := by
  have ht : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  simp only [chartFormTrivialization,hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ ht ht (by simp)]
  simp

lemma symmetrizeMetricForm_apply (B : MetricForm E) (v w : E) :
    symmetrizeMetricForm B v w = (B v w+B w v)/2 := by
  change (1/2:ℝ)*(B v w+B w v) = _
  ring
lemma symmetrizeMetricForm_symm (B : MetricForm E) (v w : E) :
    symmetrizeMetricForm B v w = symmetrizeMetricForm B w v := by
  simp only [symmetrizeMetricForm_apply,add_comm]
lemma symmetrizeMetricForm_eq_self (B : MetricForm E) (hB : ∀ v w, B v w=B w v) :
    symmetrizeMetricForm B = B := by
  ext v w
  rw [symmetrizeMetricForm_apply,hB v w]
  ring
end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

omit [T2Space M] in
lemma chartFormTrivialization_metric (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) :
    (chartFormTrivialization (E:=E) p ⟨(chartAt E p).symm y,g.inner ((chartAt E p).symm y)⟩).2 =
      chartMetricForm g p y := by
  have hx : (chartAt E p).symm y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using (chartAt E p).map_target hy
  ext v w
  rw [chartFormTrivialization_pairing p ((chartAt E p).map_target hy),chartMetricForm_pairing]
  have hv := congrArg (fun L : E →L[ℝ] E => L v) (symmL_chart_trivialization p hy)
  have hw := congrArg (fun L : E →L[ℝ] E => L w) (symmL_chart_trivialization p hy)
  have hv := (Trivialization.symmL_apply (R:=ℝ) _ hx v).symm.trans hv
  have hw := (Trivialization.symmL_apply (R:=ℝ) _ hx w).symm.trans hw
  exact congrArg₂ (fun a b => g.inner ((chartAt E p).symm y) a b) hv hw

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartTensorCoordLocal1
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartTrivMetricForm_pairing (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) (v w : E) :
    chartTrivMetricForm g p y v w = g.inner ((chartAt E p).symm y)
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symm ((chartAt E p).symm y) v)
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symm ((chartAt E p).symm y) w) :=
  chartFormTrivialization_pairing p ((chartAt E p).map_target hy) _ _ _

end


section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

variable (g₀ : SmoothMetric E M) (p : M) (K : Compacts E)
variable (ht : (chartAt E p).target = univ)

attribute [local instance] OAI.YauCounterexamples.instNormedAddCommGroupContinuousLinearMapRealId_solutions_1
attribute [local instance] OAI.YauCounterexamples.instNormedSpaceRealContinuousLinearMapId_solutions_1
attribute [local instance] OAI.YauCounterexamples.instNormedAddCommGroupMetricForm_1
attribute [local instance] OAI.YauCounterexamples.instNormedSpaceRealMetricForm_1
def chartTensorOfMetric (g : SmoothMetric E M)
    (he : ∀ x, x ∉ (chartAt E p).symm '' (K : Set E) → g.inner x = g₀.inner x) : 𝓓_{K}(E,MetricForm E) :=
  ⟨fun y => chartMetricForm g p y-chartMetricForm g₀ p y,
    contDiff_iff_contDiffAt.mpr (fun y =>
      ((chartMetricForm_contDiffOn g p).contDiffAt (by rw [ht]; exact univ_mem)).sub
        ((chartMetricForm_contDiffOn g₀ p).contDiffAt (by rw [ht]; exact univ_mem))),by
      intro y hy
      have hx : (chartAt E p).symm y ∉ (chartAt E p).symm '' (K : Set E) := by
        rintro ⟨z,hz,heq⟩
        have hyt : y ∈ (chartAt E p).target := ht ▸ mem_univ y
        have hzt : z ∈ (chartAt E p).target := ht ▸ mem_univ z
        have hz' : z=y := by
          simpa only [(chartAt E p).right_inv hyt,(chartAt E p).right_inv hzt]
            using (congrArg (chartAt E p) heq)
        exact hy (hz' ▸ hz)
      ext v w
      simp only [sub_apply,chartMetricForm_pairing,he _ hx,sub_self,Pi.zero_apply,zero_apply]⟩

omit [T2Space M] in
lemma chartTensorOfMetric_isSymm (g : SmoothMetric E M)
    (he : ∀ x, x ∉ (chartAt E p).symm '' (K : Set E) → g.inner x = g₀.inner x) (y : E) :
    symmetrizeMetricForm (chartTensorOfMetric g₀ p K ht g he y) = chartTensorOfMetric g₀ p K ht g he y := by
  apply symmetrizeMetricForm_eq_self
  intro v w
  change chartMetricForm g p y v w-chartMetricForm g₀ p y v w = _
  rw [chartMetricForm_symm g p y v w,chartMetricForm_symm g₀ p y v w]
  rfl

omit [T2Space M] in
lemma chartTensorOfMetric_positive (g : SmoothMetric E M)
    (he : ∀ x, x ∉ (chartAt E p).symm '' (K : Set E) → g.inner x = g₀.inner x) :
    chartTensorPositive g₀ p K (chartTensorOfMetric g₀ p K ht g he) := by
  intro y hy v _ hv
  rw [chartTensorOfMetric_isSymm]
  change 0 < (chartTrivMetricForm g₀ p y + (chartMetricForm g p y-chartMetricForm g₀ p y)) v v
  rw [show chartTrivMetricForm g₀ p y = chartMetricForm g₀ p y from
    chartFormTrivialization_metric g₀ p (ht ▸ mem_univ y),← add_sub_assoc,add_sub_cancel_left]
  exact chartMetricForm_pos g p (ht ▸ mem_univ y) hv

end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PhaseFormMatrix
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
open Matrix Set Filter
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complexPhaseMatrix (U D : RealForm (EuclideanSpace ℝ ι)) : Matrix ι ι ℂ :=
  fun i j => (phaseFormMatrix U i j : ℂ) + Complex.I * (phaseFormMatrix D i j : ℂ)




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ClosedPhaseMatrixValid
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {X : Type*} [TopologicalSpace X]

def boundedPhaseSet (H : X → RealForm PhaseSpace) (B κ C : ℝ) :
    Set ((X × (Fin 3 → ℂ)) × ComplexPhaseMatrix) :=
  {p | ‖p.1.2‖ ≤ B ∧ (∑ i, p.1.2 i * p.1.2 i = -1) ∧
    PhaseMatrixValid (H p.1.1) p.1.2 κ C p.2}

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ActualHessianForm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix MvPolynomial
open scoped Topology ContDiff Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples

def phaseRealVector (z : Fin 3 → ℂ) : PhaseSpace := WithLp.toLp 2 (fun i => (z i).re)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ComplexPolarWeight
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology Matrix Matrix.Norms.Elementwise ENNReal

def phaseFrameMatrix (ν b c : PhaseSpace) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of (fun i j => ![ν i,b i,c i] j)

def physicalWaveJetMatrix (a ν b c : PhaseSpace) (δ : ℝ) :
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks 1 (Matrix.of (fun _ j => ![1,0,0] j)) (Matrix.of (fun i _ => a i))
    (Matrix.of (fun i j => ![a i+δ*ν i,b i,c i] j))


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ENNReal Matrix.Norms.Elementwise


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ExistsAlignedUnit
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix.Norms.Elementwise
namespace YauCounterexamples

@[simp] lemma phaseRealVector_complexPhaseVector (a b : PhaseSpace) :
    phaseRealVector (complexPhaseVector a b) = a := by
  ext i
  simp [phaseRealVector,complexPhaseVector]

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_TestElliptic
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Compacts E) {ι : Type*} [Fintype ι]
variable (e : ι → E)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
def testEnergy (a : ι → ι → SmoothScalar E) (f g : EllipticTest K) : ℝ :=
  ∑ i, ∑ j, testPair K (testMultiply K (a i j) (testDerivative K (e j) f)) (testDerivative K (e i) g)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_DistanceSquare
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def tangentPhase (ψ : SmoothScalar E) (x₀ : E) : SmoothScalar E := ψ - distanceSquare x₀



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LinearMetricForm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
lemma linearMetricForm_smooth (g : SmoothMetric E E) (L : F ≃L[ℝ] E) :
    ContDiff ℝ ∞ (linearMetricForm g L) := by
  apply contDiff_clm_apply_iff.mpr
  intro v
  apply contDiff_clm_apply_iff.mpr
  intro w
  exact (((contDiff_selfMetricFlat g).comp L.contDiff).clm_apply contDiff_const).clm_apply contDiff_const

def linearPullbackMetric (g : SmoothMetric E E) (L : F ≃L[ℝ] E) : SmoothMetric F F :=
  flatMetricOfForm (linearMetricForm g L) (linearMetricForm_smooth g L)
    (fun x v w => selfMetricFlat_symm g (L x) (L v) (L w))
    (fun x v hv => selfMetricFlat_pos g (L x) (by simpa using L.injective.ne hv))
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_PhaseImagVector
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

def phaseImagVector (z : Fin 3 → ℂ) : PhaseSpace := WithLp.toLp 2 (fun i => (z i).im)

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ProfileFrequencyEnergy
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

def profileFrequencyEnergy (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (x : NormalWaveSpace) : ℝ :=
  1+selfMetricFlat g x (coordinateMetricGradient g φ x) (coordinateMetricGradient g φ x)

def profileFrequencyScale (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (x : NormalWaveSpace) : ℝ :=
  Real.sqrt (profileFrequencyEnergy g φ x)

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContinuousCompactSmoothJets
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {n : ℕ}
attribute [local instance] OAI.YauCounterexamples.spnENorm
attribute [local instance] OAI.YauCounterexamples.spnESpace
attribute [local instance] OAI.YauCounterexamples.spnDualNorm
attribute [local instance] OAI.YauCounterexamples.spnDualSpace
attribute [local instance] OAI.YauCounterexamples.spnFormNorm
attribute [local instance] OAI.YauCounterexamples.spnFormSpace
local instance spnDerivNorm_re11c5f_1 : NormedAddCommGroup (Euclidean n →L[ℝ] CoordinateForm (Euclidean n)) := inferInstance
local instance spnDerivSpace_re11c5f_1 : NormedSpace ℝ (Euclidean n →L[ℝ] CoordinateForm (Euclidean n)) := inferInstance
local instance spnMatrixMapNorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (Matrix ι κ ℝ →L[ℝ] CoordinateForm (Euclidean n)) :=
  inferInstanceAs (NormedAddCommGroup ((ι → κ → ℝ) →L[ℝ] CoordinateForm (Euclidean n)))


end

section
open Set Filter Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]
attribute [local instance] OAI.YauCounterexamples.matrixJetInst1
attribute [local instance] OAI.YauCounterexamples.matrixJetInst2
attribute [local instance] OAI.YauCounterexamples.matrixJetInst3
attribute [local instance] OAI.YauCounterexamples.matrixJetInst4
local instance matrixJetMatrixMapNorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (Matrix ι κ ℝ →L[ℝ] CoordinateForm (E)) :=
  inferInstanceAs (NormedAddCommGroup ((ι → κ → ℝ) →L[ℝ] CoordinateForm (E)))
end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SmDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def metricJetMap (g : SmoothMetric E E) (z : MetricJet E) : CoordinateForm E × E :=
  (metricProfileTraceForm (selfMetricFlat g z.1) z.2.1 ((selfMetricFlat g z.1).inverse z.2.2),
    (InnerProductSpace.toDual ℝ E).symm z.2.2)

def metricJetStrict (g : SmoothMetric E E) (z : MetricJet E) : Prop :=
  (metricJetMap g z).2 ≠ 0 ∧ quadraticPlaneStrict (metricJetMap g z).1 (metricJetMap g z).2

def metricJetFull (g : SmoothMetric E E) (z : MetricJet E) : Prop :=
  (metricJetMap g z).2 ≠ 0 ∧ quadraticPlaneFull (metricJetMap g z).1 (metricJetMap g z).2


end

open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def fullStrictJetMap (z : HessianJetData E) : CoordinateForm E × E :=
  (metricProfileTraceForm z.1.1 (metricHessianFromFullJet z) (z.1.1.inverse z.2.1),
    (InnerProductSpace.toDual ℝ E).symm z.2.1)
def fullStrictJetSet : Set (HessianJetData E) :=
  {z | (fullStrictJetMap z).2 ≠ 0 ∧
    quadraticPlaneStrict (fullStrictJetMap z).1 (fullStrictJetMap z).2}

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoefficientGradientApply
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

def testGradientSquare (f : EllipticTest K) : ℝ :=
  ∑ i, testPair K (testDerivative K (e i) f) (testDerivative K (e i) f)


end

section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι]

def testQuadratic (a : ι → ι → SmoothScalar E) (f : ι → EllipticTest K) : ℝ :=
  ∑ i, ∑ j, weightedPair K (a i j) (f i) (f j)


end

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_MomentBesselLp
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
namespace YauCounterexamples
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def momentBesselLp {s : ℝ} (n : ℕ) (hs : Module.finrank ℝ E < 2 * (s - n)) :
    Lp ℂ 2 (volume : Measure E) :=
  (memLp_moment_bessel_weight n hs).ofReal.toLp
    (fun x : E => Complex.ofReal (‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-s / 2)))

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContinuousSobolevFirstDerivative
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real
open scoped LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def frozenSobolevOperator {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (A : Matrix ι ι ℝ) (s α : ℝ) :
    FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s :=
  (α : ℂ) • sobolevInclusion (s + 2) s (by linarith) -
    ∑ i, ∑ j, (A i j : ℂ) • sobolevSecondDerivative (s + 2) (b i) (b j)


end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RescaledDifferentialPerturbation
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]
variable (b : Module.Basis ι ℝ E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (p : E) {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)

def rescaledDifferentialPerturbation (r : ℝ) :
    FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s :=
  coefficientPerturbation b hs
    (fun i j => schwartzToSobolev s (rescaledCoefficient (fun x => (a i j x : ℂ)) χ
      (Complex.ofRealCLM.contDiff.comp (ha i j)) hχ hχc p r))
    (fun i => schwartzToSobolev s (scaledLowerCoefficient 1 (fun x => (c i x : ℂ)) χ
      (Complex.ofRealCLM.contDiff.comp (hc i)) hχ hχc p r))




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (q : ℝ → SmoothMetric E M)
variable (hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
  ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y))
variable {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
include hq hu

lemma continuous_joint_laplaceBeltrami_time_deriv :
    Continuous (fun z : ℝ × M => deriv (fun t => laplaceBeltrami (q t) u z.2) z.1) := by
  apply continuous_joint_of_chart (E := E) (fun t x => deriv (fun r => laplaceBeltrami (q r) u x) t)
  intro t p
  exact (contDiffAt_partial_time_deriv (joint_laplaceBeltrami_chart q hq hu t p
    ((chartAt E p).map_source (mem_chart_source E p)))).continuousAt

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_TestPairSubSquareBound
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

def testSchrodinger (a : ι → ι → SmoothScalar E) (V : SmoothScalar E) :
    EllipticTest K →ₗ[ℝ] EllipticTest K := testElliptic K e a + testMultiply K V



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ZeroInterior
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
open MeasureTheory TopologicalSpace Filter Set Metric
open scoped Distributions ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def zeroInterior (u : SmoothScalar E) : Set E := {x | (u : E → ℝ) =ᶠ[𝓝 x] 0}

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_VaryingSpectralResolventBase
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]

variable (q : ℝ → SmoothMetric E M)
variable (hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
  ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y))
variable {a : M → ℝ} (ha : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ a)

def laplaceDerivativeBCF (t : ℝ) : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
  ⟨fun x => deriv (fun r => laplaceBeltrami (q r) a x) t,
    by
      have hh := (continuous_joint_laplaceBeltrami_time_deriv q hq ha).comp
        (show Continuous (fun x : M => (t,x)) from continuous_const.prodMk continuous_id)
      simpa only [Function.comp_def] using hh⟩

end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_FourThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
def threeFrame (p : ThreeManifold) : ThreeModel →ₗᵢ[ℝ] ThreeAmbient :=
  lpProductIsometry (sphereFrame p.1) (unitSphereFrame (n:=1) p.2)
def threeChartMap (p : ThreeManifold) : ThreeModel → ThreeAmbient :=
  lpProductFunction (roundChart (p.1 : Euclidean 3) (sphereFrame p.1))
    (roundChart (p.2 : ℂ) (unitSphereFrame (n:=1) p.2))
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
def circleRoundMetric : SmoothMetric (Euclidean 1) Circle :=
  inducedMetric (fun z : Circle => (z:ℂ)) circle_immersion_smooth circle_immersion_injective

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_SphericalPinFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions
lemma sphericalTensorSupport_image :
    (chartAt (Euclidean 3) sourcePole).symm '' (sphericalTensorSupport : Set (Euclidean 3)) =
      {q | sphericalRadius sourceAxisOne sourceAxisTwo q ≤ 3/10} := by
  ext q
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (mem_sphericalCoverage_iff sourcePole sourceAxisOne sourceAxisTwo
      sphericalRadius_neg_sourcePole (by norm_num) y).mp hy
  · intro hq
    refine ⟨(chartAt (Euclidean 3) sourcePole) q,⟨q,hq,rfl⟩,?_⟩
    exact (chartAt (Euclidean 3) sourcePole).left_inv
      (sphericalRadius_sublevel_in_source sourcePole sourceAxisOne sourceAxisTwo
        sphericalRadius_neg_sourcePole (by norm_num : (3/10:ℝ)<1) hq)
lemma sphericalExterior_support {g₀ g : SmoothMetric (Euclidean 3) (Sphere 3)}
    {R : ℝ} (hR : R ≤ 3/10) (he : sphericalExterior g₀ g R) :
    ∀ q, q ∉ (chartAt (Euclidean 3) sourcePole).symm ''
      (sphericalTensorSupport : Set (Euclidean 3)) → g.inner q=g₀.inner q := by
  intro q hq
  rw [sphericalTensorSupport_image] at hq
  exact he q (hR.trans_lt (lt_of_not_ge hq))
def sphericalTensorOf (g₀ g : SmoothMetric (Euclidean 3) (Sphere 3))
    (he : sphericalExterior g₀ g (3/10)) : SphericalTensor :=
  chartTensorOfMetric g₀ sourcePole sphericalTensorSupport (sphere_chart_target sourcePole) g
    (sphericalExterior_support le_rfl he)
attribute [local instance] OAI.YauCounterexamples.sphericalAmbientFormNorm
attribute [local instance] OAI.YauCounterexamples.sphericalAmbientFormSpace
lemma sphericalTensorOf_zero (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) :
    sphericalTensorOf g₀ g₀ (fun _ _ => rfl)=0 := by
  apply DFunLike.ext
  intro y
  change chartMetricForm g₀ sourcePole y-chartMetricForm g₀ sourcePole y=0
  exact sub_self _
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_SphericalOpenFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions
namespace YauCounterexamples
lemma sphericalTensorOf_positive (g₀ g : SmoothMetric (Euclidean 3) (Sphere 3))
    (he : sphericalExterior g₀ g (3/10)) : sphericalTensorOf g₀ g he ∈ sphericalPositiveSet g₀ :=
  chartTensorOfMetric_positive g₀ sourcePole sphericalTensorSupport (sphere_chart_target sourcePole)
    g (sphericalExterior_support le_rfl he)
local instance sphericalOpenFormNorm_re11c5f_1 : NormedAddCommGroup (MetricForm (Euclidean 3)) := inferInstanceAs (NormedAddCommGroup (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
local instance sphericalOpenFormSpace_re11c5f_1 : NormedSpace ℝ (MetricForm (Euclidean 3)) := inferInstanceAs (NormedSpace ℝ (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
lemma sphericalPositive_zero (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) :
    (0 : SphericalTensor) ∈ sphericalPositiveSet g₀ := by
  simpa only [sphericalTensorOf_zero] using sphericalTensorOf_positive g₀ g₀ (fun _ _ => rfl)
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ThreeCoupledNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples

def threeCoupledComplex (r : ℝ) (k : ℕ) (p : ThreeManifold) : ℂ :=
  (productA p.1^k+(r:ℂ)^k*productB p.1^k)*(p.2:ℂ)^k
def threeCoupled (r : ℝ) (k : ℕ) (p : ThreeManifold) : ℝ := (threeCoupledComplex r k p).re
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeRadiusNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace

attribute [local instance] OAI.YauCounterexamples.threeChartNormedSpace
local instance threeChartContinuousSMul_re11c5f_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
def threeChartMetric (g : SmoothMetric ThreeModel ThreeManifold) (p : ThreeManifold) :
    SmoothMetric ThreeModel ThreeModel :=
  flatMetricOfForm (chartMetricForm g p)
    (contDiffOn_univ.mp (by simpa only [three_chart_target] using chartMetricForm_contDiffOn g p))
    (chartMetricForm_symm g p)
    (fun y v hv => chartMetricForm_pos g p (by rw [three_chart_target]; trivial) hv)
end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace

def threeSphereMap (p : ThreeManifold) : ThreeModel → Euclidean 3 :=
  roundChart (p.1:Euclidean 3) (sphereFrame p.1) ∘ WithLp.fstL 2 ℝ (Euclidean 2) (Euclidean 1)

def threeSphereCoord (p : ThreeManifold) (i : Fin 3) (y : ThreeModel) : ℝ :=
  inner ℝ (productAxis i) (threeSphereMap p y)

def threeRadiusSq (p : ThreeManifold) (y : ThreeModel) : ℝ :=
  threeSphereCoord p 0 y^2+threeSphereCoord p 1 y^2

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ThreeLogNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples

def threeLogEnvelope (p : ThreeManifold) (c : ℝ) (y : ThreeModel) : ℝ :=
  c/2*Real.log (threeRadiusSq p y)
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FourLiftThreeSmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
def fourProductInner (g : SmoothMetric ThreeModel ThreeManifold) (x : FourManifold) :
    TangentSpace 𝓘(ℝ,FourModel) x →L[ℝ] TangentSpace 𝓘(ℝ,FourModel) x →L[ℝ] ℝ :=
  metricPullbackInner (E:=FourModel) g fourToThree x+
    metricPullbackInner (E:=FourModel) circleRoundMetric fourToCircle x
lemma fourProductInner_apply (g : SmoothMetric ThreeModel ThreeManifold) (x : FourManifold) (v w : FourModel) :
    fourProductInner g x v w=g.inner (fourToThree x) (threeModelEquiv (v.1,v.2.1))
      (threeModelEquiv (w.1,w.2.1))+circleRoundMetric.inner (fourToCircle x) v.2.2 w.2.2 := by
  change g.inner (fourToThree x) (mfderiv _ _ fourToThree x v) (mfderiv _ _ fourToThree x w) +
    circleRoundMetric.inner (fourToCircle x) (mfderiv _ _ fourToCircle x v) (mfderiv _ _ fourToCircle x w) = _
  rw [mfderiv_fourToThree,mfderiv_fourToThree,mfderiv_fourToCircle,mfderiv_fourToCircle]

lemma fourProductInner_pos (g : SmoothMetric ThreeModel ThreeManifold) (x : FourManifold)
    (v : FourModel) (hv : v≠0) : 0<fourProductInner g x v v := by
  rw [fourProductInner_apply]
  by_cases h : threeModelEquiv (v.1,v.2.1)=0
  · have hvc : v.2.2≠0 := by
      intro hc
      apply hv
      have hs := (map_eq_zero_iff threeModelEquiv threeModelEquiv.injective).mp h
      exact Prod.ext (congrArg (Prod.fst : ThreeProductModel → Euclidean 2) hs) (Prod.ext (congrArg (Prod.snd : ThreeProductModel → Euclidean 1) hs) hc)
    exact add_pos_of_nonneg_of_pos (metric_inner_nonneg g _ _) (circleRoundMetric.pos _ _ hvc)
  · exact add_pos_of_pos_of_nonneg (g.pos _ _ h) (metric_inner_nonneg circleRoundMetric _ _)
lemma fourProductInner_bounded (g : SmoothMetric ThreeModel ThreeManifold) (x : FourManifold) :
    Bornology.IsVonNBounded ℝ {v : FourModel | fourProductInner g x v v<1} := by
  let L : FourModel ≃L[ℝ] ThreeModel × Euclidean 1 :=
    (ContinuousLinearEquiv.prodAssoc ℝ (Euclidean 2) (Euclidean 1) (Euclidean 1)).symm.trans
      (threeModelEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (Euclidean 1)))
  rw [NormedSpace.isVonNBounded_iff ℝ]
  have hgb := (NormedSpace.isVonNBounded_iff ℝ).mp (show Bornology.IsVonNBounded ℝ
    {v : ThreeModel | g.inner (fourToThree x) v v < 1} from g.isVonNBounded (fourToThree x))
  have hcb := (NormedSpace.isVonNBounded_iff ℝ).mp (show Bornology.IsVonNBounded ℝ
    {v : Euclidean 1 | circleRoundMetric.inner (fourToCircle x) v v < 1} from circleRoundMetric.isVonNBounded (fourToCircle x))
  apply (L.antilipschitz.isBounded_preimage (hgb.prod hcb)).subset
  intro v hv
  change fourProductInner g x v v < 1 at hv
  rw [fourProductInner_apply] at hv
  change g.inner (fourToThree x) (threeModelEquiv (v.1,v.2.1)) (threeModelEquiv (v.1,v.2.1)) < 1 ∧
    circleRoundMetric.inner (fourToCircle x) v.2.2 v.2.2 < 1
  constructor
  · linarith [metric_inner_nonneg circleRoundMetric (fourToCircle x) v.2.2]
  · linarith [metric_inner_nonneg g (fourToThree x) (threeModelEquiv (v.1,v.2.1))]
attribute [local instance] OAI.YauCounterexamples.fourLiftRealSmul
lemma fourProductInner_smooth (g : SmoothMetric ThreeModel ThreeManifold) :
    ContMDiff 𝓘(ℝ,FourModel) ((𝓘(ℝ,FourModel)).prod 𝓘(ℝ,FourModel →L[ℝ] FourModel →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (FourModel →L[ℝ] FourModel →L[ℝ] ℝ) x (fourProductInner g x)) := by
  intro x₀
  have h1 := metricPullbackInner_smooth g fourToThree fourToThree_smooth x₀
  have h2 := metricPullbackInner_smooth circleRoundMetric fourToCircle fourToCircle_smooth x₀
  rw [contMDiffAt_section x₀] at h1 h2 ⊢
  apply (h1.add h2).congr_of_eventuallyEq
  have hn := (trivializationAt FourModel (TangentSpace 𝓘(ℝ,FourModel)) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt FourModel _ x₀)
  filter_upwards [hn] with x hx
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [hom_trivializationAt_apply,add_apply,Pi.add_apply]
  rw [inCoordinates_apply_eq₂ hx hx (by simp),inCoordinates_apply_eq₂ hx hx (by simp),inCoordinates_apply_eq₂ hx hx (by simp)]
  simp only [fourProductInner, add_apply, map_add]

def fourProductMetric (g : SmoothMetric ThreeModel ThreeManifold) : SmoothMetric FourModel FourManifold where
  inner := fourProductInner g
  symm x v w := by
    change fourProductInner g x (v:FourModel) (w:FourModel)=fourProductInner g x (w:FourModel) (v:FourModel)
    erw [fourProductInner_apply,fourProductInner_apply,g.symm,circleRoundMetric.symm]
  pos := fourProductInner_pos g
  isVonNBounded := fourProductInner_bounded g
  contMDiff := fourProductInner_smooth g

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeFormulaNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples

def threeAmbientSphereGradient (r : ℝ) (k : ℕ) (p : ThreeManifold) : Euclidean 3 :=
  let α := (p.2:ℂ)^k*productA p.1^(k-1)
  let β := (p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)
  (k:ℝ) • ((α.re+β.re) • productAxis 0-α.im • productAxis 1-β.im • productAxis 2)
def threeAmbientCircleGradient (r : ℝ) (k : ℕ) (p : ThreeManifold) : ℂ :=
  (-(k:ℝ)*(threeCoupledComplex r k p).im) • (Complex.I*(p.2:ℂ))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
def threeGlobalRadius (p : ThreeManifold) : ℝ :=
  max ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)
def threeGlobalLog (p : ThreeManifold) : ℝ :=
  threeEnvelopeExponent*Real.log (threeGlobalRadius p)
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace
def threeNormalGlue (C : ℝ) (f : NormalWaveSpace → ℝ) : ThreeManifold → ℝ :=
  fun p => C+manifoldChartPush threeProfileCenter ((fun y => f y-C) ∘ threeNormalEquiv.symm) p
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

attribute [local instance] OAI.YauCounterexamples.threeRobustNormedSpace
local instance threeRobustContinuousSMul_re11c5f_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
def threeNormalMetricOf (g : SmoothMetric ThreeModel ThreeManifold) :
    SmoothMetric NormalWaveSpace NormalWaveSpace :=
  linearPullbackMetric (threeChartMetric g threeProfileCenter) threeNormalEquiv

end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_ProductMetric_ThreeInteriorMeridianNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
lemma threeInteriorMeridianAmbient_norm (t : ℝ) : ‖threeInteriorMeridianAmbient t‖=1 := by
  have hn : ‖threeInteriorMeridianAmbient t‖^2=1 := by
    rw [←real_inner_self_eq_norm_sq]
    simp only [threeInteriorMeridianAmbient,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,productAxis_inner]
    norm_num [Fin.ext_iff]
    nlinarith [Real.sin_sq_add_cos_sq t]
  nlinarith [norm_nonneg (threeInteriorMeridianAmbient t)]
def threeInteriorMeridian (t : ℝ) : ThreeManifold :=
  (⟨threeInteriorMeridianAmbient t,by simpa only [mem_sphere,dist_zero_right] using threeInteriorMeridianAmbient_norm t⟩,1)
def threeInteriorMeridianEnergy (r : ℝ) (m : ℕ) : ℝ → ℝ :=
  coordinateGradientPair threeBackgroundMetric (threeCoupled r (4*m+1))
    (threeCoupled r (4*m+1)) ∘ threeInteriorMeridian

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeCoupledCleanChartJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Metric MeasureTheory
open scoped Topology ContDiff InnerProductSpace

def threeWeight (φ : ThreeManifold → ℝ) (k : ℕ) (p : ThreeManifold) : ℝ :=
  Real.exp (productWaveFrequency k*φ p)+threeGlobalRadius p^k
end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeExceptional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff

def threePacketA : (Fin 3 → ℝ) → ℂ :=
  threeComplexPower (productAxis 0) (productAxis 1) 1 ∘ threeNormalInv ∘ normalWaveEquiv
def threePacketB : (Fin 3 → ℝ) → ℂ :=
  fun y => (threeCouplingRadius:ℂ)*(threeComplexPower (productAxis 0) (productAxis 2) 1 (threeNormalInv (normalWaveEquiv y)))
def threePacketWeight (φ : ThreeManifold → ℝ) (k : ℕ) (y : Fin 3 → ℝ) : ℝ :=
  Real.exp (productWaveFrequency k*φ (threeNormalInv (normalWaveEquiv y)))+‖threePacketA y‖^k+‖threePacketB y‖^k
def threeExceptionalInChart (φ : ThreeManifold → ℝ) (k : ℕ) : Set (Fin 3 → ℝ) :=
  {y | ‖threePacketA y‖^k+‖threePacketB y‖^k ≤ (productWaveFrequency k)^6*
    Real.exp (productWaveFrequency k*φ (threeNormalInv (normalWaveEquiv y)))}
end


open Set Filter Function Manifold Metric
open scoped Topology ContDiff
def threeExceptional (φ : ThreeManifold → ℝ) (k : ℕ) : Set ThreeManifold :=
  {p | productWeight threeCouplingRadius k p ≤ productWaveFrequency k^6*Real.exp (productWaveFrequency k*φ p)}

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ExistsThreeScalarProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff

def threeWaveLift (u : NormalWaveSpace → ℝ) : ThreeManifold → ℝ :=
  manifoldChartPush threeProfileCenter (u ∘ threeNormalEquiv.symm)
end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeFixedFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions
lemma threeTensorSupport_image (R : ℝ) :
    (chartAt ThreeModel threeProfileCenter).symm '' (threeTensorSupport R : Set ThreeModel)=
      threeNormalInv '' closedBall 0 (R/2) := by
  change (chartAt ThreeModel threeProfileCenter).symm '' (threeNormalEquiv '' closedBall 0 (R/2))=_
  rw [←image_comp]
  rfl
lemma threeExterior_support {g : SmoothMetric ThreeModel ThreeManifold} {R r : ℝ}
    (hr : r≤R/2) (he : ThreeExterior g r) :
    ∀ q∉(chartAt ThreeModel threeProfileCenter).symm '' (threeTensorSupport R : Set ThreeModel),
      g.inner q=threeBackgroundMetric.inner q := by
  rw [threeTensorSupport_image]
  exact he.mono hr
def threeTensorOf (R : ℝ) (g : SmoothMetric ThreeModel ThreeManifold)
    (he : ThreeExterior g (R/2)) : ThreeTensor R :=
  chartTensorOfMetric threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
    (three_chart_target threeProfileCenter) g (threeExterior_support le_rfl he)
attribute [local instance] OAI.YauCounterexamples.threeAmbientFormNorm
attribute [local instance] OAI.YauCounterexamples.threeAmbientFormSpace
lemma threeTensorOf_zero (R : ℝ) : threeTensorOf R threeBackgroundMetric (fun _ _ => rfl)=0 := by
  apply DFunLike.ext
  intro y
  change chartMetricForm threeBackgroundMetric threeProfileCenter y-chartMetricForm threeBackgroundMetric threeProfileCenter y=0
  exact sub_self _
lemma threeTensorOf_positive (R : ℝ) (g : SmoothMetric ThreeModel ThreeManifold)
    (he : ThreeExterior g (R/2)) : threeTensorOf R g he∈threePositiveSet R :=
  chartTensorOfMetric_positive threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
    (three_chart_target threeProfileCenter) g (threeExterior_support le_rfl he)
lemma threePositive_zero (R : ℝ) : (0:ThreeTensor R)∈threePositiveSet R := by
  simpa only [threeTensorOf_zero] using threeTensorOf_positive R threeBackgroundMetric (fun _ _ => rfl)
end


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions ENNReal NNReal
def threeCollar (b c : ℝ) : Set ThreeManifold :=
  (threeNormalInv '' ball 0 c) \ (threeNormalInv '' closedBall 0 b)
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_ProductMetric_FourWaveThreeSmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Manifold Bundle Function Matrix BoxIntegral MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise ENNReal NNReal
def fourWaveEquiv : (Fin 4 → ℝ) ≃L[ℝ] FourModel :=
  fourTailHeadEquiv.trans (((normalWaveEquiv.trans threeNormalEquiv).prodCongr fourCircleCoord).trans fourSplitEquiv.symm)
def fourWaveCompact (R : ℝ) : Set FourModel :=
  fourWaveEquiv '' (fourTailHeadEquiv.symm ''
    ((normalWaveEquiv.symm '' Metric.closedBall 0 (R/2)) ×ˢ Icc 0 1))

end YauCounterexamples
end

end OAI
end


