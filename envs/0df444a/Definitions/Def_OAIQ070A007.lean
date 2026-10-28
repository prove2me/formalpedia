-- Prove2me | Definitions.Def_OAIQ070A007
-- name    : OAIQ070A007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T11:22:42.392931+00:00
-- url     : https://prove2.me/theorems/f85f155f-ca99-4e5c-9e0a-1254ef269357
-- title:
--   Definitions bundle OAIQ070A007 of the split of OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 183 declarations of OpenAI's Lean: 142 definitions, 2 instances and 39 theorems. The definitions and types are `OAI.YauCounterexamples.anisotropicHalfSobolevResolvent`, `OAI.YauCounterexamples.anisotropicSobolevResolvent`, `OAI.YauCounterexamples.ballPhase`, `OAI.YauCounterexamples.canonicalCutoffWave`, `OAI.YauCounterexamples.carlemanGradient`, `OAI.YauCounterexamples.carlemanMatrix`, `OAI.YauCounterexamples.carlemanSkew`, `OAI.YauCounterexamples.carlemanSymmetric`, `OAI.YauCounterexamples.chartGradientField`, `OAI.YauCounterexamples.chartGradientProjection`, `OAI.YauCounterexamples.chartInverseDifferentialBound`, `OAI.YauCounterexamples.chartTensorCoordLocal11`, `OAI.YauCounterexamples.chartTensorCoordLocal12`, `OAI.YauCounterexamples.chartTensorCoordLocal3`, `OAI.YauCounterexamples.chartTensorCoordLocal4`, `OAI.YauCounterexamples.chartTensorNeighborhoodInst3`, `OAI.YauCounterexamples.chartTensorNeighborhoodInst4`, `OAI.YauCounterexamples.christoffelFromJet`, `OAI.YauCounterexamples.coefficientDivergence`, `OAI.YauCounterexamples.coefficientElliptic`, `OAI.YauCounterexamples.coefficientGradient`, `OAI.YauCounterexamples.coefficientNorm`, `OAI.YauCounterexamples.coefficientSchrodinger`, `OAI.YauCounterexamples.coefficientTransport`, `OAI.YauCounterexamples.compactSmoothContinuityInst3`, `OAI.YauCounterexamples.compactSmoothContinuityInst4`, `OAI.YauCounterexamples.continuedPhaseMatrix`, `OAI.YauCounterexamples.convexifyPhase`, `OAI.YauCounterexamples.coordinateRegionMeasure`, `OAI.YauCounterexamples.corrugationSecondRemainder`, `OAI.YauCounterexamples.differentialMetric`, `OAI.YauCounterexamples.distanceSquare`, `OAI.YauCounterexamples.exponentialMetric`, `OAI.YauCounterexamples.exponentialWeight`, `OAI.YauCounterexamples.finiteWaveTransport`, `OAI.YauCounterexamples.flowIntegralDerivative`, `OAI.YauCounterexamples.flowIntegralMap`, `OAI.YauCounterexamples.fourProfileCenter`, `OAI.YauCounterexamples.fourProjCircle`, `OAI.YauCounterexamples.fourProjThree` and 102 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `SmoothYau_DifferentialEq_MfderivReModelTarget`, `SmoothYau_Estimates_AnisotropicCompositionSmall`, `SmoothYau_Estimates_CanonicalCutoffWave`, `SmoothYau_Estimates_CoefficientElliptic`, `SmoothYau_Estimates_NormalFamilyPhase`, `SmoothYau_Estimates_PhaseFormMatrix`, `SmoothYau_Estimates_QuadraticInnerSpace`, `SmoothYau_Estimates_RadialSpeedPositiveAnnulus`, `SmoothYau_Estimates_RealImagCovector`, `SmoothYau_Estimates_ThreeNoncancelNormedSpace`, `SmoothYau_Geometry_ChartTensorNeighborhoodInst1`, `SmoothYau_Geometry_CoefficientGradientApply`, `SmoothYau_Geometry_CoordinateGradientPairScalarCorrection`, `SmoothYau_Geometry_MetricGradient`, `SmoothYau_Geometry_PacketAxisShift`, `SmoothYau_Geometry_PinnedMetricJointGradientPair`, `SmoothYau_Geometry_PrepDualNorm`, `SmoothYau_Geometry_PulledGradientNorm`, `SmoothYau_Geometry_RadialFiniteDualNorm`, `SmoothYau_Geometry_RealForm`, `SmoothYau_Geometry_RoundMetricExists`, `SmoothYau_Geometry_SymmLChartTrivialization`, `SmoothYau_Geometry_TestElliptic`, `SmoothYau_Geometry_WaveDerivSum`, `SmoothYau_Geometry_ZeroInterior`, `SmoothYau_Limits_CompactFullProfileMargin`, `SmoothYau_Limits_CoordinateForm`, `SmoothYau_Limits_CutoffFactorCompactRaw`, `SmoothYau_Limits_ExistsCompactSignedEnvelope`, `SmoothYau_Limits_FrameDualNorm`, `SmoothYau_Limits_PhaseImagVector`, `SmoothYau_NodalMeasure_CompactRegularLevelIntrinsicFinite`, `SmoothYau_NodalMeasure_ExtrusionEquiv`, `SmoothYau_ProductMetric_FourWaveThreeSmul`, `SmoothYau_Smoothness_AdmissibleCutoffWaveLocalizedDerivatives`, `SmoothYau_Smoothness_BoundedDegreeMonomials`, `SmoothYau_Smoothness_BundleMetricInner`, `SmoothYau_Smoothness_ChartGradientProjectionSmooth`, `SmoothYau_Smoothness_ChartTensorCoordLocal1`, `SmoothYau_Smoothness_CompactMetricInverseJets`, `SmoothYau_Smoothness_ContDiffSmoothFiniteWave`, `SmoothYau_Smoothness_ContinuousCompactSmoothJets`, `SmoothYau_Smoothness_ContinuousSobolevFirstDerivative`, `SmoothYau_Smoothness_DistanceSquare`, `SmoothYau_Smoothness_FlowParameters`, `SmoothYau_Smoothness_FourLiftThreeSmul`, `SmoothYau_Smoothness_FrameInverseApply`, `SmoothYau_Smoothness_LinearMetricForm`, `SmoothYau_Smoothness_LocalIntegrationParts`, `SmoothYau_Smoothness_NormalChartWave`, `SmoothYau_Smoothness_NormalCoordinateMap`, `SmoothYau_Smoothness_NormalInverseVecNorm`, `SmoothYau_Smoothness_NormalJetMapFirstPhase`, `SmoothYau_Smoothness_PinningTensorSpace`, `SmoothYau_Smoothness_PolynomialFiniteWave`, `SmoothYau_Smoothness_ProfilePeriodizeEventuallyZero`, `SmoothYau_Smoothness_PulledGradient`, `SmoothYau_Smoothness_RoundPowerRadius`, `SmoothYau_Smoothness_SmDualNorm`, `SmoothYau_Smoothness_SmoothFiniteWaveSum`, `SmoothYau_Smoothness_SourceSignBox`, `SmoothYau_Smoothness_SphericalBaseProfileRadius`, `SmoothYau_Smoothness_TestAsSmooth`, `SmoothYau_Smoothness_TestDerivativeComm`, `SmoothYau_Smoothness_ThreeCoupledCleanChartJets`, `SmoothYau_Smoothness_WaveDeriv`, `SmoothYau_Smoothness_WeightedPair`, `SmoothYau_Spectrum_AnisotropicConstant`, `SmoothYau_Spectrum_BilinearCoordinateMatrixPosDef`, `SmoothYau_Spectrum_JointLocalLaplacian`, `SmoothYau_Spectrum_SphereProjection`, `SmoothYau_Spectrum_ThreeCoupledNormedSpace`, `SmoothYau_SphereMetric_FourThree`, `SmoothYau_SphereMetric_ThreeFixedFormNorm`.
--
--   **Imports.** It imports the published bundle `Def_SmoothYau`; the bundles `OAIQ070A000`, `OAIQ070A001`, `OAIQ070A002`, `OAIQ070A003` and `OAIQ070A004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ070A009`, `OAIQ070A010` and `OAIQ070A012`; the statements `OAI.YauCounterexamples.CompactMetricAtlas.eventually_product_scalar_exactification`, `OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_exactification`, `OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_factor_raw`, `OAI.YauCounterexamples.actual_radialCorrugation_strict_shift`, `OAI.YauCounterexamples.annular_eigenfunction_separating_tensor`, `OAI.YauCounterexamples.annular_orthogonal_transverse_nonzero`, `OAI.YauCounterexamples.canonical_phase_triple_smallBall`, `OAI.YauCounterexamples.centered_inverse_for_normal_charts`, `OAI.YauCounterexamples.compact_normal_image_neighborhood`, `OAI.YauCounterexamples.cutoff_exactification_in_smooth_neighborhood`, `OAI.YauCounterexamples.cutoff_polynomial_wave_residual_bound`, `OAI.YauCounterexamples.exists_annular_simple_pinned_family`, `OAI.YauCounterexamples.exists_normal_wave_chart_family`, `OAI.YauCounterexamples.exists_spherical_chart_quasimodes`, `OAI.YauCounterexamples.exists_spherical_exact_stage`, `OAI.YauCounterexamples.exists_spherical_global_quasimodes`, `OAI.YauCounterexamples.exists_spherical_scalar_producer`, `OAI.YauCounterexamples.exists_three_simple_pinned_family`, `OAI.YauCounterexamples.four_nodal_finite`, `OAI.YauCounterexamples.generated_composed_wave_endpoint_ratio`, `OAI.YauCounterexamples.generated_cutoff_waves_near_center`, `OAI.YauCounterexamples.generated_wave_uniform_jets`, `OAI.YauCounterexamples.localized_packet_sign_probability`, `OAI.YauCounterexamples.metric_center_polynomial_net_with_coverage`, `OAI.YauCounterexamples.normalChartWave_laplacian`, `OAI.YauCounterexamples.normalChartWave_residual_germ`, `OAI.YauCounterexamples.normalFamilyWave_at_zero`, `OAI.YauCounterexamples.pinnedMetric_laplacian`, `OAI.YauCounterexamples.radial_uniform_strict_bundle`, `OAI.YauCounterexamples.roundPower_conjugate_projection_uniform`, `OAI.YauCounterexamples.roundPower_global_profile_residual_rapid_decay`, `OAI.YauCounterexamples.roundPower_strict_profile_residual_rapid_decay`, `OAI.YauCounterexamples.round_pair_rank_transfer`, `OAI.YauCounterexamples.sphericalBaseProfile_chart_margins`, `OAI.YauCounterexamples.spherical_annular_projection_uniform`, `OAI.YauCounterexamples.spherical_exterior_conjugating_margin`, `OAI.YauCounterexamples.spherical_global_jet_lower`, `OAI.YauCounterexamples.spherical_wave_background_chart_bounds`, `OAI.YauCounterexamples.spherical_wave_residual_support` and `OAI.YauCounterexamples.three_rank_separating_tensor`; the proofs of `OAI.YauCounterexamples.CompactMetricAtlas.eventually_product_scalar_exactification`, `OAI_YauCounterexamples_CompactMetricAtlas_eventually_product_scalar_factor_raw`, `OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_exactification`, `OAI.YauCounterexamples.CompactMetricAtlas.global_cutoff_raw_controls`, `OAI.YauCounterexamples.actual_radialCorrugation_strict_shift`, `OAI.YauCounterexamples.annular_eigenfunction_separating_tensor`, `OAI.YauCounterexamples.annular_orthogonal_transverse_nonzero`, `OAI.YauCounterexamples.cutoff_exactification_in_smooth_neighborhood`, `OAI.YauCounterexamples.cutoff_polynomial_wave_residual_bound`, `OAI.YauCounterexamples.exists_spherical_exact_stage`, `OAI.YauCounterexamples.exists_spherical_global_quasimodes`, `OAI.YauCounterexamples.exists_spherical_scalar_producer`, `OAI.YauCounterexamples.exists_supported_separating_tensor`, `OAI.YauCounterexamples.four_nodal_finite`, `OAI.YauCounterexamples.generated_composed_wave_endpoint_ratio`, `OAI.YauCounterexamples.generated_cutoff_waves_near_center`, `OAI.YauCounterexamples.generated_wave_uniform_jets`, `OAI_YauCounterexamples_local_eigen_proportional_of_annular_rank`, `OAI_YauCounterexamples_local_eigen_proportional_of_gradient_rank`, `OAI.YauCounterexamples.localized_packet_sign_probability`, `OAI.YauCounterexamples.normalChartWave_residual_germ`, `OAI.YauCounterexamples.normalFamilyWave_at_zero`, `OAI.YauCounterexamples.pinnedMetric_laplacian`, `OAI.YauCounterexamples.radial_uniform_strict_bundle`, `OAI.YauCounterexamples.roundPower_conjugate_projection_uniform`, `OAI.YauCounterexamples.roundPower_global_profile_residual_rapid_decay`, `OAI.YauCounterexamples.round_pair_rank_transfer`, `OAI.YauCounterexamples.spherical_annular_projection_uniform`, `OAI.YauCounterexamples.spherical_exterior_conjugating_margin`, `OAI.YauCounterexamples.spherical_global_jet_lower` and `OAI.YauCounterexamples.three_rank_separating_tensor`.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A000
import Definitions.Def_OAIQ070A001
import Definitions.Def_OAIQ070A002
import Definitions.Def_OAIQ070A003
import Definitions.Def_OAIQ070A004

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_MfderivReModelTarget
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
variable {E F G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace F M]
  [TopologicalSpace N] [ChartedSpace G N]

lemma contMDiff_reModel_target (L : F ≃L[ℝ] E) {f : N → M}
    (hf : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,F) ∞ f) :
    letI := reModelChartedSpace (M:=M) L
    ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,E) ∞ f := by
  let := reModelChartedSpace (M:=M) L
  intro x
  have h := (contMDiffAt_iff.mp (hf x))
  rw [contMDiffAt_iff]
  refine ⟨h.1,?_⟩
  simp only [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ] at h ⊢
  simp only [extChartAt, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id] at h ⊢
  have hh := L.contDiff.contDiffAt.comp (chartAt G x x) h.2
  have hc : (chartAt E (f x) : M → E) = L ∘ (chartAt F (f x)) := rfl
  rw [hc]
  simpa only [comp_assoc] using hh

end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
variable {E F G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace F M]
  [TopologicalSpace N] [ChartedSpace G N]
lemma mfderiv_reModel_target (L : F ≃L[ℝ] E) {f : N → M}
    (hf : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,F) ∞ f) (x : N) :
    let D : G →L[ℝ] F := mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) f x
    letI := reModelChartedSpace (M:=M) L
    mfderiv 𝓘(ℝ,G) 𝓘(ℝ,E) f x = L.toContinuousLinearMap.comp D := by
  let D : G →L[ℝ] F := mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) f x
  have hd := (hf.mdifferentiable (by simp) x).hasMFDerivAt
  rw [HasMFDerivAt] at hd
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, range_id, hasFDerivWithinAt_univ,
    id_comp, comp_id] at hd
  change ContinuousAt f x ∧ HasFDerivWithinAt (↑(chartAt F (f x)) ∘ f ∘ ↑(chartAt G x).symm) D Set.univ (chartAt G x x) at hd
  rw [hasFDerivWithinAt_univ] at hd
  let := reModelChartedSpace (M:=M) L
  change mfderiv 𝓘(ℝ,G) 𝓘(ℝ,E) f x = L.toContinuousLinearMap.comp D
  apply HasMFDerivAt.mfderiv
  change ContinuousAt f x ∧ HasFDerivWithinAt _ _ _ _
  refine ⟨hd.1,?_⟩
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, range_id, hasFDerivWithinAt_univ,
    id_comp, comp_id]
  change HasFDerivWithinAt (↑(chartAt E (f x)) ∘ f ∘ ↑(chartAt G x).symm)
    (L.toContinuousLinearMap.comp D : G →L[ℝ] E) Set.univ (chartAt G x x)
  rw [hasFDerivWithinAt_univ]
  have hc : (chartAt E (f x) : M → E) = L ∘ (chartAt F (f x)) := rfl
  rw [hc]
  have hh := L.toContinuousLinearMap.hasFDerivAt.comp (chartAt G x x) hd.2
  simpa only [comp_assoc,comp_apply,ContinuousLinearEquiv.coe_coe] using hh

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_AnisotropicConstant
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples
open MeasureTheory SchwartzMap TemperedDistribution
open scoped FourierTransform ContDiff
variable {E G F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def anisotropicSobolevResolvent (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α) :
    FourierSobolevSpace E F s →L[ℂ] FourierSobolevSpace E F (s + 2) :=
  sobolevBoundedMultiplier s (anisotropicResolventSymbol L α hα)

omit [CompleteSpace F] in
lemma norm_anisotropicSobolevResolvent_le (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α) :
    ‖anisotropicSobolevResolvent (F := F) L s α hα‖ ≤ anisotropicConstant L :=
  (norm_sobolevBoundedMultiplier_le _ _).trans (norm_anisotropicResolventSymbol_le L α hα)

def anisotropicHalfSobolevResolvent (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α) :
    FourierSobolevSpace E F s →L[ℂ] FourierSobolevSpace E F (s + 1) :=
  sobolevBoundedMultiplier s (anisotropicHalfResolventSymbol L α hα)

end YauCounterexamples

open Set Filter
open scoped SchwartzMap ContDiff Topology

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_AnisotropicCompositionSmall
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
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
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

lemma anisotropic_composition_small (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (P : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s)
    (hP : anisotropicConstant L * ‖P‖ ≤ 1 / 2) :
    ‖anisotropicSobolevResolvent L s α hα ∘L P‖ < 1 := by
  apply lt_of_le_of_lt ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right (norm_anisotropicSobolevResolvent_le L s α hα)
      (norm_nonneg P)).trans hP))
  norm_num

def localEllipticInverse (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (P : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s)
    (hP : anisotropicConstant L * ‖P‖ ≤ 1 / 2) :
    FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s + 2) :=
  neumannCorrectedInverse (anisotropicSobolevResolvent L s α hα) P
    (anisotropic_composition_small L s α hα P hP)


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_BoundedDegreeMonomials
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
section ActualEikonal
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def smoothEikonalResidual (g : σ → σ → (σ → ℝ) → ℂ) (S : MvPolynomial σ ℂ) :
    (σ → ℝ) → ℂ := fun x => 1 + ∑ i, ∑ j,
      g i j x * realPolyEval (pderiv i S) x * realPolyEval (pderiv j S) x

end ActualEikonal

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def smoothWaveTransport (a : σ → (σ → ℝ) → ℂ) (b : (σ → ℝ) → ℂ)
    (V : MvPolynomial σ ℂ) : (σ → ℝ) → ℂ :=
  fun x => (∑ i, a i x * realPolyEval (pderiv i V) x) + b x * realPolyEval V x



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



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_WaveDeriv
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
namespace YauCounterexamples

section WaveDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

def waveCoordinateOperator (e : ι → E) (G : ι → ι → E → ℂ)
    (b : ι → E → ℂ) (f : E → ℂ) (x : E) : ℂ :=
  (∑ i, ∑ j, G i j x * waveDeriv (e i) (waveDeriv (e j) f) x) +
    ∑ i, b i x * waveDeriv (e i) f x

def waveGradientPair (e : ι → E) (G : ι → ι → E → ℂ)
    (f g : E → ℂ) (x : E) : ℂ :=
  ∑ i, ∑ j, G i j x * waveDeriv (e i) f x * waveDeriv (e j) g x

end WaveDifferentiation


end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_WaveDerivSum
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
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι α : Type*} [Fintype ι]

def finiteWaveTransport (e : ι → E) (G : ι → ι → E → ℂ)
    (b : ι → E → ℂ) (S V : E → ℂ) (x : E) : ℂ :=
  waveGradientPair e G V S x + waveGradientPair e G S V x +
    (waveCoordinateOperator e G b S x + 2) * V x

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PolynomialFiniteWave
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
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def polynomialWaveRemainder (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (S : MvPolynomial σ ℂ) (V : ℕ → MvPolynomial σ ℂ) :
    ℕ → (σ → ℝ) → ℂ
  | 0 => smoothWaveTransport (smoothPhaseTransportVector g S)
      (smoothPhaseTransportScalar g b S) (V 0)
  | j+1 => fun x => smoothWaveTransport (smoothPhaseTransportVector g S)
      (smoothPhaseTransportScalar g b S) (V (j+1)) x + smoothPolynomialLaplacian g b (V j) x

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RealForm
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
namespace YauCounterexamples
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem innerForm_isSymm : (innerForm : RealForm V).IsSymm :=
  ⟨fun x y => real_inner_comm y x⟩

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
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def continuedPhaseMatrix (Q : Matrix ι ι ℂ) (z : ι → ℂ) : Matrix ι ι ℂ :=
  (phaseProjection z)ᵀ * Q * phaseProjection z

omit [Fintype ι] in
@[fun_prop] lemma continuous_phaseProjection : Continuous (phaseProjection (ι := ι)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun z : ι → ℂ => (1 : Matrix ι ι ℂ) i j + z i * z j)
  fun_prop


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
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
open Matrix Set Filter
open scoped Topology Matrix Matrix.Norms.Elementwise




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SmoothFiniteWaveSum
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
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def smoothWaveRemainder (e : ι → E) (g : ι → ι → E → ℂ) (b : ι → E → ℂ)
    (S : E → ℂ) (V : ℕ → E → ℂ) : ℕ → E → ℂ
  | 0 => finiteWaveTransport e g b S (V 0)
  | j+1 => fun x => finiteWaveTransport e g b S (V (j+1)) x + waveCoordinateOperator e g b (V j) x

def smoothWaveEikonal (e : ι → E) (g : ι → ι → E → ℂ) (S : E → ℂ) (x : E) : ℂ :=
  1 + waveGradientPair e g S S x

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
open Set Filter
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_CanonicalCutoffWave
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
open scoped Topology
open Set Filter Matrix MvPolynomial
open scoped Topology ContDiff Matrix.Norms.Elementwise

def canonicalCutoffWave (g : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b : Fin 3 → (Fin 3 → ℝ) → ℂ) (s : ℂ) (z : Fin 3 → ℂ)
    (Q : ComplexPhaseMatrix) (ζ : (Fin 3 → ℝ) → ℂ) (m D : ℕ) (n : ℝ) :
    (Fin 3 → ℝ) → ℂ :=
  let K := 2*D+3*m+6
  let J := D+m+1
  let S := smoothPhasePolynomial g s z Q (K+J+1)
  let V := uniformSmoothWaveAmplitudes g b S z K J
  smoothFiniteWave (realPolyEval S) (fun j x => ζ x * realPolyEval (V j) x) J n


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_TestDerivativeComm
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

variable (K : Compacts E)
def testDerivative (v : E) : EllipticTest K →ₗ[ℝ] EllipticTest K :=
  (ContDiffMapSupportedIn.postcompLM (ContinuousLinearMap.apply ℝ ℝ v)).comp
    (ContDiffMapSupportedIn.fderivLM ℝ ⊤ ⊤)

@[simp] lemma testDerivative_apply (v : E) (f : EllipticTest K) (x : E) :
    testDerivative K v f x = fderiv ℝ f x v := by
  simp [testDerivative]

def testMultiply (a : SmoothScalar E) : EllipticTest K →ₗ[ℝ] EllipticTest K :=
  (ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) (SmoothScalar.contDiff a)).toLinearMap
@[simp] lemma testMultiply_apply (a : SmoothScalar E) (f : EllipticTest K) (x : E) :
    testMultiply K a f x = a x * f x := by dsimp [testMultiply]; ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def testPair (f g : EllipticTest K) : ℝ := ∫ x, f x * g x

end

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Compacts E)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
@[simp] lemma testPair_zero_left (f : EllipticTest K) : testPair K 0 f = 0 := by simp [testPair]
@[simp] lemma testPair_zero_right (f : EllipticTest K) : testPair K f 0 = 0 := by simp [testPair]



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

def testElliptic (a : ι → ι → SmoothScalar E) : EllipticTest K →ₗ[ℝ] EllipticTest K :=
  ∑ i, ∑ j, (testDerivative K (e i)).comp ((testMultiply K (a i j)).comp (testDerivative K (e j)))
def testTransport (X : ι → SmoothScalar E) : EllipticTest K →ₗ[ℝ] EllipticTest K :=
  ∑ i, (testMultiply K (X i)).comp (testDerivative K (e i))
def coefficientDivergence (X : ι → SmoothScalar E) : SmoothScalar E :=
  ∑ i, SmoothScalar.directional (e i) (X i)
def testSkewTransport (X : ι → SmoothScalar E) : EllipticTest K →ₗ[ℝ] EllipticTest K :=
  (2 : ℝ) • testTransport K e X + testMultiply K (coefficientDivergence e X)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_WeightedPair
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
variable (K : Compacts E)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
def weightedPair (a : SmoothScalar E) (f g : EllipticTest K) : ℝ :=
  testPair K (testMultiply K a f) g
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_CoefficientElliptic
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
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

def coefficientElliptic (a : ι → ι → SmoothScalar E) (q : SmoothScalar E) : SmoothScalar E :=
  ∑ i, ∑ j, SmoothScalar.directional (e i) (a i j * SmoothScalar.directional (e j) q)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactFullProfileMargin
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
section ProfileForms
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def profileTrace (H : ProfileForm E) (a v : E) : ℝ := H a a + (1 + ‖a‖ ^ 2) * H v v

def profileStrict (H : ProfileForm E) (a : E) : Prop :=
  ∃ v : E, ‖v‖ = 1 ∧ inner ℝ a v = 0 ∧ 0 < profileTrace H a v

def profileFull (H : ProfileForm E) (a : E) : Prop :=
  ∀ v : E, ‖v‖ = 1 → inner ℝ a v = 0 → 0 < profileTrace H a v

end ProfileForms

end

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def profileRankOne (l : E →L[ℝ] ℝ) : ProfileForm E := l.smulRight l

omit [FiniteDimensional ℝ E] in
@[simp] lemma profileRankOne_apply (l : E →L[ℝ] ℝ) (v w : E) :
    profileRankOne l v w = l v * l w := rfl

end

open Set Filter Function Metric
open scoped Topology
open scoped InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ProfilePeriodizeEventuallyZero
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
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

def profilePeriodize (f : ProfilePlane → ℝ) (x : ProfilePlane) : ℝ :=
  ∑ᶠ k : ProfileLattice, f (x-profileLatticePoint k)


end

section
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

def radialSquaredBase (β : ℝ → ℝ) (b : ℝ) (x : ProfilePlane) : ℝ :=
  radialPrimitive β (x.1^2+x.2^2) - radialPrimitive β b


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

def planeRadialCovector (z : ProfilePlane) : ProfilePlane →L[ℝ] ℝ :=
  if z = 0 then ContinuousLinearMap.fst ℝ ℝ ℝ else
    (z.1/Real.sqrt (z.1^2+z.2^2)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (z.2/Real.sqrt (z.1^2+z.2^2)) • ContinuousLinearMap.snd ℝ ℝ ℝ

def planeAngularCovector (z : ProfilePlane) : ProfilePlane →L[ℝ] ℝ :=
  if z = 0 then ContinuousLinearMap.snd ℝ ℝ ℝ else
    (-z.2/Real.sqrt (z.1^2+z.2^2)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (z.1/Real.sqrt (z.1^2+z.2^2)) • ContinuousLinearMap.snd ℝ ℝ ℝ



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RadialSpeedPositiveAnnulus
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
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

def periodicRadialFunction (β : ℝ → ℝ) (b : ℝ) (x : ProfilePlane) : ℝ :=
  radialPrimitive β b + profilePeriodize (radialSquaredBase β b) x


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



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_MetricGradient
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI





noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma metricGradient_pairing (g : SmoothMetric E M) (u : M → ℝ) (x : M)
    (v : TangentSpace 𝓘(ℝ,E) x) :
    g.inner x (metricGradient g u x) v = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u x v := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) :=
    show FiniteDimensional ℝ E from inferInstance
  exact congrArg (fun L : TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ => L v)
    ((InnerProductSpace.toDual ℝ (TangentSpace 𝓘(ℝ,E) x)).apply_symm_apply _)

lemma metricGradient_unique (g : SmoothMetric E M) (u : M → ℝ) (x : M)
    (v : TangentSpace 𝓘(ℝ,E) x)
    (hv : ∀ w, g.inner x v w = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u x w) :
    v = metricGradient g u x := by
  apply positive_bilinear_unique (E := E) (g.inner x) (g.pos x) v (metricGradient g u x)
  intro w
  exact (hv w).trans (metricGradient_pairing g u x w).symm

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CoordinateForm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def quadraticPlaneStrict (T : CoordinateForm E) (q : E) : Prop :=
  ∃ v, ‖v‖ = 1 ∧ inner ℝ q v = 0 ∧ 0 < T v v

def quadraticPlaneFull (T : CoordinateForm E) (q : E) : Prop :=
  ∀ v, ‖v‖ = 1 → inner ℝ q v = 0 → 0 < T v v

def scaledSubForm (B C : CoordinateForm E) : CoordinateForm E := (4:ℝ) • B - C

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma localMetricFlat_invertible (g : SmoothMetric E M) (p x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet) :
    (localMetricFlat g p x).IsInvertible := by
  let e := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).continuousLinearEquivAt ℝ x hx
  have hi : Function.Injective (localMetricFlat g p x) := by
    apply (localMetricFlat g p x).ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    by_contra hn
    have he : e.symm v ≠ 0 := by simpa only [ne_eq,EmbeddingLike.map_eq_zero_iff] using hn
    have hp := g.pos x (e.symm v) he
    have hz := congrArg (fun f : E →L[ℝ] ℝ => f v) hv
    change localMetricFlat g p x v v = 0 at hz
    rw [localMetricFlat_pairing g p x hx] at hz
    change g.inner x (e.symm v) (e.symm v) = 0 at hz
    linarith
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ E).toLinearEquiv.finrank_eq
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi
  exact ⟨(LinearEquiv.ofBijective (localMetricFlat g p x).toLinearMap ⟨hi,hs⟩).toContinuousLinearEquiv,rfl⟩

lemma local_metricGradient (g : SmoothMetric E M) (u : M → ℝ) (p x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet) :
    (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p ⟨x,metricGradient g u x⟩).2 =
      (localMetricFlat g p x).inverse
        (inTangentCoordinates 𝓘(ℝ,E) 𝓘(ℝ,ℝ) id u
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u) p x) := by
  symm
  apply (localMetricFlat_invertible g p x hx).inverse_apply_eq.mpr
  ext w
  rw [localMetricFlat_pairing g p x hx,Trivialization.symm_apply_apply_mk _ hx,
    metricGradient_pairing]
  unfold inTangentCoordinates
  simp only [id_eq]
  have he := ContinuousLinearMap.inCoordinates_eq (ϕ := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u x) hx
    (show u x ∈ (trivializationAt ℝ (TangentSpace 𝓘(ℝ,ℝ)) (u p)).baseSet by
      simp [TangentBundle.trivializationAt_baseSet, chartAt_self_eq])
  have hew := congrArg (fun L : E →L[ℝ] ℝ => L w) he
  exact hew.trans (by
    simp [Trivialization.continuousLinearEquivAt_apply,
      Trivialization.continuousLinearEquivAt_symm_apply]
    rfl)

theorem contMDiff_metricGradient (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun x => TotalSpace.mk' E x (metricGradient g u x)) := by
  intro p
  rw [contMDiffAt_section p]
  have hg := contMDiffAt_localMetricFlat g p
  have hi := (localMetricFlat_invertible g p p (mem_baseSet_trivializationAt E _ p)).contDiffAt_map_inverse (n := ∞)
  have hs := (hi.comp_contMDiffAt hg).clm_apply ((hu p).mfderiv_const (m := ∞) (by simp))
  apply hs.congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ p)] with x hx
  exact local_metricGradient g u p x hx

end

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
local instance metricFormNorm_r16d908_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance metricFormSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance metricTriNorm_r16d908_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance metricTriSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

omit [FiniteDimensional ℝ E] in
lemma localMetricFlat_self (g : SmoothMetric E E) (p x : E) :
    localMetricFlat g p x = selfMetricFlat g x := by
  ext v w
  rw [localMetricFlat_pairing g p x (by simp [TangentBundle.trivializationAt_baseSet, chartAt_self_eq])]
  have hv (v : E) : (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symm x v = v := by
    rw [←Trivialization.symmL_apply (R := ℝ) _ (by simp [TangentBundle.trivializationAt_baseSet, chartAt_self_eq]) v,
      TangentBundle.symmL_model_space]
    rfl
  rw [hv,hv]
  rfl

omit [FiniteDimensional ℝ E] in
lemma selfMetricFlat_symm (g : SmoothMetric E E) (x v w : E) :
    selfMetricFlat g x v w = selfMetricFlat g x w v := g.symm x v w

omit [FiniteDimensional ℝ E] in
lemma selfMetricFlat_pos (g : SmoothMetric E E) (x : E) {v : E} (hv : v ≠ 0) :
    0 < selfMetricFlat g x v v := g.pos x v hv


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
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

def pulledHessian (Γ : E → E →L[ℝ] E →L[ℝ] E) (j : V →L[ℝ] E)
    (u : E → ℝ) (x : E) : ProfileForm V :=
  (coordinateCovariantSecond Γ u x).bilinearComp j j

def radialCorrugation (ψ χ : E → ℝ) (y : E → ProfilePlane) (β : ℝ → ℝ)
    (b δ A N : ℝ) (x : E) : ℝ :=
  ψ x+(δ*A/N)*(χ x*periodicRadialFunction β b (N • y x))



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalJetMapFirstPhase
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def normalMetricTensor (g : SmoothMetric E E) (p : E) (A : E →L[ℝ] E)
    (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let C := (metricChristoffel g p).bilinearComp A A
  (selfMetricFlat g (normalJetMap p A C x)).bilinearComp (A - C x) (A - C x)


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
open Set Filter Manifold
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_FrameDualNorm
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
open Set
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def metricFrameSet (g : SmoothMetric E E) (K : Set E) : Set (E × (E →L[ℝ] E)) :=
  {q | q.1 ∈ K ∧ ∀ v w : E, selfMetricFlat g q.1 (q.2 v) (q.2 w) = inner ℝ v w}

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FlowParameters
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

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
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def flowIntegralMap (V : E → E) (hV : Continuous V) (p : FlowParameters E) : FlowParameters E :=
  (p.1, p.2 - ContinuousMap.const unitInterval p.1.2 - p.1.1 • volterra (superposition V hV p.2))

def flowIntegralDerivative (S : C(unitInterval, E)) : FlowParameters E ≃L[ℝ] FlowParameters E where
  toFun p := (p.1, p.2 - ContinuousMap.const unitInterval p.1.2 - p.1.1 • S)
  invFun p := (p.1, p.2 + ContinuousMap.const unitInterval p.1.2 + p.1.1 • S)
  left_inv p := by ext <;> simp; abel
  right_inv p := by ext <;> simp; abel
  map_add' p q := by ext <;> simp [add_smul]; abel
  map_smul' c p := by ext <;> simp [smul_sub, smul_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffSmoothFiniteWave
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
open Set Filter Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Elementwise

def normalWaveMetric (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) (x : NormalWaveSpace) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => normalMetricTensor g q.1 q.2 x
    (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)

def normalWaveFirstCoefficient (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) (x : NormalWaveSpace) (j : Fin 3) : ℝ :=
  ∑ i, (fderiv ℝ (fun y => (normalWaveMetric g q y)⁻¹ i j) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) +
    (1/2 : ℝ) * (normalWaveMetric g q x)⁻¹ i j * (normalWaveMetric g q x).det⁻¹ *
      fderiv ℝ (fun y => (normalWaveMetric g q y).det) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i))


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
open Set Filter
open scoped Topology ContDiff

def normalWavePiOperator (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) (f : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) : ℂ :=
  waveCoordinateOperator (EuclideanSpace.basisFun (Fin 3) ℝ)
    (fun i j y => ((normalWaveMetric g q y)⁻¹ i j : ℂ))
    (fun j y => (normalWaveFirstCoefficient g q y j : ℂ))
    (f ∘ normalWaveEquiv.symm) (normalWaveEquiv x)



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_AdmissibleCutoffWaveLocalizedDerivatives
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
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

def normalWaveProfile (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (q : NormalWaveParameter) (x : NormalWaveSpace) : ℝ :=
  φ (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x)

def normalFamilyWave (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ)
    (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
    (q : NormalWaveParameter) (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix)
    (ζ : (Fin 3 → ℝ) → ℂ) (m D : ℕ) (n : ℝ) : (Fin 3 → ℝ) → ℂ :=
  canonicalCutoffWave (fun i j x => A (q,x) i j) (fun j x => b (q,x) j)
    (normalWaveProfile g φ q 0 : ℂ) z Q ζ m D n

end

open Set Filter Matrix
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_NormalFamilyPhase
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples



open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

def normalFamilyPhase (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ)
    (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (q : NormalWaveParameter) (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix) (m D : ℕ) :
    (Fin 3 → ℝ) → ℂ :=
  realPolyEval (smoothPhasePolynomial (fun i j x => A (q,x) i j)
    (normalWaveProfile g φ q 0 : ℂ) z Q ((2*D+3*m+6)+(D+m+1)+1))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_QuadraticInnerSpace
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
namespace YauCounterexamples

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) (hA : A.PosDef)

def quadraticNormEquiv : E ≃L[ℝ] QuadraticInnerSpace A hA := by
  classical
  exact LinearEquiv.toContinuousLinearEquiv <|
    ((InnerProductSpace.toDual ℝ E).toLinearEquiv.trans LinearMap.toContinuousLinearMap.symm).trans
      b.dualBasis.equivFun

end YauCounterexamples

open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalInverseVecNorm
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
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.normalInverseVecNorm
attribute [local instance] OAI.YauCounterexamples.normalInverseVecSpace
local instance normalInverseBiVecNorm_r16d908_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance normalInverseBiVecSpace_r16d908_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
def normalFamilySource (g : SmoothMetric E E) : Set ((E × (E →L[ℝ] E)) × E) :=
  {w | w.1.2.IsInvertible ∧ ‖w.1.2.inverse‖ *
    ‖(metricChristoffel g w.1.1).bilinearComp w.1.2 w.1.2‖ * ‖w.2‖ < 1/2}

def normalFamilyTotal (g : SmoothMetric E E) (w : (E × (E →L[ℝ] E)) × E) :=
  (w.1,normalJetMap w.1.1 w.1.2
    ((metricChristoffel g w.1.1).bilinearComp w.1.2 w.1.2) w.2)


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_ExtrusionEquiv
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples

def coordinateRegionMeasure (C : Set (Fin 3 → ℝ)) : Measure NormalWaveSpace :=
  Measure.map normalWaveEquiv (volume.restrict C)

instance coordinateRegionMeasure_finite (C : Set (Fin 3 → ℝ))
    [IsFiniteMeasure (volume.restrict C)] : IsFiniteMeasure (coordinateRegionMeasure C) :=
  Measure.isFiniteMeasure_map _ _

end YauCounterexamples

end

open Set Function MeasureTheory
open scoped ENNReal
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
section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

def coefficientTransport (X : ι → SmoothScalar E) (p : SmoothScalar E) : SmoothScalar E :=
  ∑ i, X i * SmoothScalar.directional (e i) p

def carlemanSymmetric (a : ι → ι → SmoothScalar E) (p : SmoothScalar E) (τ : ℝ) :
    EllipticTest K →ₗ[ℝ] EllipticTest K :=
  testElliptic K e a + τ^2 • testMultiply K p

def carlemanSkew (X : ι → SmoothScalar E) (τ : ℝ) :
    EllipticTest K →ₗ[ℝ] EllipticTest K :=
  (-τ) • testSkewTransport K e X


end

section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] (e : ι → E)

def coefficientGradient (a : ι → ι → SmoothScalar E) (φ : SmoothScalar E) :
    ι → SmoothScalar E := fun i => ∑ j, a i j * SmoothScalar.directional (e j) φ

def coefficientNorm (a : ι → ι → SmoothScalar E) (φ : SmoothScalar E) : SmoothScalar E :=
  ∑ i, SmoothScalar.directional (e i) φ * coefficientGradient e a φ i

def convexifyPhase (ψ : SmoothScalar E) (H : ℝ) : SmoothScalar E :=
  ψ + (H/2) • (ψ*ψ)


end

section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

def exponentialWeight (φ : SmoothScalar E) (τ : ℝ) : SmoothScalar E :=
  ⟨fun x => Real.exp (τ * φ x), Real.contDiff_exp.comp (contDiff_const.mul (SmoothScalar.contDiff φ))⟩
@[simp] lemma exponentialWeight_apply (φ : SmoothScalar E) (τ : ℝ) (x : E) :
    exponentialWeight φ τ x = Real.exp (τ * φ x) := rfl


end

open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def distanceSquare (x₀ : E) : SmoothScalar E :=
  ⟨fun x => ‖x-x₀‖^2, by
    change ContDiff ℝ ∞ (fun x : E => ‖x-x₀‖^2)
    exact (contDiff_id.sub (contDiff_const (c := x₀))).norm_sq ℝ⟩
@[simp] lemma distanceSquare_apply (x₀ x : E) : distanceSquare x₀ x = ‖x-x₀‖^2 := rfl



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SphereProjection
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
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace

variable {n : ℕ}

attribute [local instance] OAI.YauCounterexamples.instFactEqNatFinrankRealEuclideanHAddOfNat
def sphereFrame (p : Sphere n) : Euclidean n →ₗᵢ[ℝ] Euclidean (n+1) :=
  (ℝ ∙ (-(p : Euclidean (n+1))))ᗮ.subtypeₗᵢ.comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere (-p))).repr.symm.toLinearIsometry


end

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
open Set Filter Manifold BoxIntegral Metric
open scoped Topology ContDiff InnerProductSpace

lemma mem_sphericalCoverage_iff (p : Sphere 3) (a b : Euclidean 4)
    (hp : sphericalRadius a b (-p) = 1) {R : ℝ} (hR : R < 1) (y : Euclidean 3) :
    y ∈ sphericalCoverage p a b R ↔
      sphericalRadius a b ((chartAt (Euclidean 3) p).symm y) ≤ R := by
  constructor
  · rintro ⟨q,hq,rfl⟩
    rw [(chartAt (Euclidean 3) p).left_inv (sphericalRadius_sublevel_in_source p a b hp hR hq)]
    exact hq
  · intro hy
    exact ⟨(chartAt (Euclidean 3) p).symm y,hy,
      (chartAt (Euclidean 3) p).right_inv (by rw [sphere_chart_target]; trivial)⟩


end

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
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
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
open Set Filter Function Module Manifold
open scoped Topology ContDiff InnerProductSpace Matrix



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SphericalBaseProfileRadius
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

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
open scoped Topology ContDiff
open Set Filter Manifold BoxIntegral
open scoped Topology ContDiff

def sphericalProfileGlue (p : Sphere 3) (a b : Euclidean 4) (t : ℝ)
    (ψ : Euclidean 3 → ℝ) : Sphere 3 → ℝ :=
  fun q => sphericalBaseProfile a b t q + manifoldChartPush p
    (fun y => ψ y-sphericalBaseProfile a b t ((chartAt (Euclidean 3) p).symm y)) q



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LinearMetricForm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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

def linearMetricForm (g : SmoothMetric E E) (L : F ≃L[ℝ] E) (x : F) : CoordinateForm F :=
  (selfMetricFlat g (L x)).bilinearComp L.toContinuousLinearMap L.toContinuousLinearMap
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_BilinearCoordinateMatrixPosDef
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
open Set Filter
open scoped ContDiff Topology
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter Matrix Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def selfWaveMatrix (g : SmoothMetric E E) (x : E) : Matrix (CoordIndex E) (CoordIndex E) ℝ :=
  bilinearCoordinateMatrix (Module.finBasis ℝ E) (selfMetricFlat g x)

end


open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalChartWave
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
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff

def normalChartWave (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    (f : (Fin 3 → ℝ) → ℂ) : NormalWaveSpace → ℂ :=
  smoothChartPush e (f ∘ normalWaveEquiv.symm)



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalCoordinateMap
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite
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
open Set Filter
open scoped ContDiff Topology
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

def normalCoordinateMap (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  normalWaveEquiv.symm (normalJetMap q.1 q.2
    ((metricChristoffel g q.1).bilinearComp q.2 q.2) (normalWaveEquiv x))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FrameInverseApply
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

def normalPhaseCovector (q : NormalWaveParameter) (z : Fin 3 → ℂ) : NormalWaveSpace →L[ℝ] ℂ :=
  ∑ i : Fin 3, ((ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
    (normalWaveEquiv.symm.toContinuousLinearMap.comp q.2.inverse)).smulRight (z i)

end



open Set Filter
open scoped Topology ContDiff RealInnerProductSpace

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

def normalImagCovector (q : NormalWaveParameter) (z : Fin 3 → ℂ) : NormalWaveSpace →L[ℝ] ℝ :=
  Complex.imCLM.comp (normalPhaseCovector q z)

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RealImagCovector
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples



open Set Filter
open scoped Topology ContDiff RealInnerProductSpace

def realImagCovector (a b : NormalWaveSpace →L[ℝ] ℝ) : NormalWaveSpace →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp a + Complex.I • (Complex.ofRealCLM.comp b)

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LocalIntegrationParts
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
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
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
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}

def roundPlanarChart (a b : Euclidean (d+1)) (p : Sphere d) : Euclidean d → ℂ :=
  fun y => planarLinear a b ((chartAt (Euclidean d) p).symm y : Euclidean (d+1))

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff


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

def carlemanGradient (a : ι → ι → SmoothScalar E) (X : ι → SmoothScalar E)
    (f : EllipticTest K) : ℝ :=
  4 * (∑ i, ∑ j, ∑ k,
      weightedPair K (a i j * SmoothScalar.directional (e i) (X k))
        (testDerivative K (e j) f) (testDerivative K (e k) f)) -
  2 * (∑ i, ∑ j, ∑ k,
      weightedPair K (X k * SmoothScalar.directional (e k) (a i j))
        (testDerivative K (e j) f) (testDerivative K (e i) f))


end

section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι]

def pointwiseQuadratic (a : ι → ι → SmoothScalar E) (x : E) (v : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, a i j x * v i * v j

variable (e : ι → E)

def carlemanMatrix (a : ι → ι → SmoothScalar E) (X : ι → SmoothScalar E)
    (C : ℝ) : ι → ι → SmoothScalar E := fun j k =>
  (4 : ℝ) • (∑ i, a i j * SmoothScalar.directional (e i) (X k)) -
    (2 : ℝ) • (∑ l, X l * SmoothScalar.directional (e l) (a k j)) + (2*C) • a k j


end

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_TestAsSmooth
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
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

def testAsSmooth (u : EllipticTest K) : SmoothScalar E := ⟨u, u.contDiff⟩
@[simp] lemma testAsSmooth_apply (u : EllipticTest K) (x : E) : testAsSmooth K u x = u x := rfl

def coefficientSchrodinger (a : ι → ι → SmoothScalar E) (V u : SmoothScalar E) : SmoothScalar E :=
  coefficientElliptic e a u + V*u

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContinuousSobolevFirstDerivative
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

def physicalQuadraticEquiv (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    E ≃L[ℝ] QuadraticInnerSpace A hA :=
  (LinearEquiv.smulOfNeZero ℝ E (2 * Real.pi) (by positivity)).toContinuousLinearEquiv.trans
    (quadraticNormEquiv b A hA)

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
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
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
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
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
variable {d : ℕ}

def roundPower (a b : Euclidean (d+1)) (k : ℕ) (p : Sphere d) : ℝ :=
  ((planarLinear a b (p : Euclidean (d+1)))^k).re


end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

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

def ballPhase (y : E) (r : ℝ) : SmoothScalar E :=
  algebraMap ℝ (SmoothScalar E) (r^2) - distanceSquare y
@[simp] lemma ballPhase_apply (y x : E) (r : ℝ) : ballPhase y r x = r^2-‖x-y‖^2 := rfl

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RoundMetricExists
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def localGradientPair (g : SmoothMetric E M) (u v : M → ℝ) (p : M) (y : E) : ℝ :=
  (fun i => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i)) ⬝ᵥ
    (metricCoefficients g p y)⁻¹ *ᵥ
      (fun j => fderiv ℝ (v ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j))

lemma localGradientPair_change {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v)
    (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    localGradientPair g u v q y = localGradientPair g u v p (chartTransition p q y) := by
  let J := coordinateTransitionMatrix p q y
  let du : CoordIndex E → ℝ := fun i =>
    fderiv ℝ (u ∘ (chartAt E p).symm) (chartTransition p q y) (Module.finBasis ℝ E i)
  let dv : CoordIndex E → ℝ := fun i =>
    fderiv ℝ (v ∘ (chartAt E p).symm) (chartTransition p q y) (Module.finBasis ℝ E i)
  have hu' : (fun i => fderiv ℝ (u ∘ (chartAt E q).symm) y (Module.finBasis ℝ E i)) =
      Jᵀ *ᵥ du := by
    ext i
    rw [fderiv_inChart_change hu p q hy hp]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, J,du, mul_comm]
  have hv' : (fun i => fderiv ℝ (v ∘ (chartAt E q).symm) y (Module.finBasis ℝ E i)) =
      Jᵀ *ᵥ dv := by
    ext i
    rw [fderiv_inChart_change hv p q hy hp]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, J,dv, mul_comm]
  have hid : J * ((metricCoefficients g q y)⁻¹ * Jᵀ) =
      (metricCoefficients g p (chartTransition p q y))⁻¹ := by
    rw [metricInverse_change_left g p q hy hp, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (coordinateTransitionMatrix_det_ne_zero g p q hy hp)),
      Matrix.one_mul]
  unfold localGradientPair
  rw [hu', hv', Matrix.mulVec_mulVec]
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hid, dotProduct_comm]

lemma coordinateGradientPair_inChart {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v)
    (g : SmoothMetric E M) (p x : M) (hx : x ∈ (chartAt E p).source) :
    coordinateGradientPair g u v x = localGradientPair g u v p ((chartAt E p) x) := by
  have he := localGradientPair_change hu hv g p x
    ((chartAt E x).map_source (mem_chart_source E x))
    (by simpa only [(chartAt E x).left_inv (mem_chart_source E x)] using hx)
  have hbase : coordinateGradientPair g u v x =
      localGradientPair g u v x ((chartAt E x) x) := by
    simp only [coordinateGradientPair, localGradientPair, dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hbase, he]
  simp only [chartTransition, Function.comp_apply, (chartAt E x).left_inv (mem_chart_source E x)]

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
lemma metric_inner_nonneg (g : SmoothMetric E M) (x : M)
    (v : TangentSpace 𝓘(ℝ, E) x) : 0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

lemma chart_metric_quadratic (g : SmoothMetric E M) (p : M) (y : E) (z : CoordIndex E → ℝ) :
    g.inner ((chartAt E p).symm y)
      (∑ i, z i • coordinateVector p y i) (∑ i, z i • coordinateVector p y i) =
      z ⬝ᵥ ((metricCoefficients g p y) *ᵥ z) := by
  classical
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [metricCoefficients]
  rw [g.symm _ (coordinateVector p y j)]
  ring

lemma scalarDifferential_dual_bound_chart {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target)
    (v : TangentSpace 𝓘(ℝ, E) ((chartAt E p).symm y)) :
    (scalarDifferential u ((chartAt E p).symm y) v) ^ 2 ≤
      localGradientPair g u u p y * g.inner ((chartAt E p).symm y) v v := by
  classical
  have he : (chartAt E p).MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_chart (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableOn (by simp),
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableOn (by simp)⟩
  obtain ⟨w, rfl⟩ := he.symm.mfderiv_surjective hy v
  let D : E →L[ℝ] TangentSpace 𝓘(ℝ, E) ((chartAt E p).symm y) :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y
  let wE : E := w
  let z := (Module.finBasis ℝ E).equivFun wE
  have hw : wE = ∑ i, z i • Module.finBasis ℝ E i := by
    symm
    exact (Module.finBasis ℝ E).sum_repr wE
  change (scalarDifferential u _ (D wE)) ^ 2 ≤
    localGradientPair g u u p y * g.inner _ (D wE) (D wE)
  rw [hw, map_sum]
  simp only [map_smul]
  change (scalarDifferential u _ (∑ i, z i • coordinateVector p y i)) ^ 2 ≤ _
  erw [chart_metric_quadratic]
  simp only [map_sum, map_smul, smul_eq_mul, scalarDifferential_coordinateVector hu p hy]
  let du : CoordIndex E → ℝ := fun i =>
    fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i)
  have hc := real_dual_matrix_cauchy (metricCoefficients_posDef g p hy) du z
  simpa only [localGradientPair, dotProduct, mul_comm, du] using hc

lemma scalarDifferential_dual_bound {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
    (scalarDifferential u x v) ^ 2 ≤
      coordinateGradientPair g u u x * g.inner x v v := by
  have hx := mem_chart_source E x
  have hy := (chartAt E x).map_source hx
  have he := (chartAt E x).left_inv hx
  have H := scalarDifferential_dual_bound_chart hu g x hy
  rw [coordinateGradientPair_inChart hu hu g x x hx]
  apply (congrArg (fun z : M => (scalarDifferential u z v) ^ 2 ≤
    localGradientPair g u u x ((chartAt E x) x) * g.inner z v v) he).mp
  exact H v

def rankOneMetric (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (a b : M → ℝ)
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b) (F : M → ℝ)
    (ha0 : ∀ x, 0 < a x) (hab0 : ∀ x, 0 < a x + b x * F x)
    (hdual : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
      (scalarDifferential u x v) ^ 2 ≤ F x * g.inner x v v) :
    SmoothMetric E M where
  inner x := a x • g.inner x + b x • pullbackInner (scalarDifferential u x)
  symm x v w := by
    change a x * g.inner x v w + b x * inner ℝ (scalarDifferential u x v) (scalarDifferential u x w) =
      a x * g.inner x w v + b x * inner ℝ (scalarDifferential u x w) (scalarDifferential u x v)
    rw [g.symm, real_inner_comm (scalarDifferential u x v) (scalarDifferential u x w)]
  pos x v hv := by
    have hδ : 0 < min (a x) (a x + b x * F x) := lt_min (ha0 x) (hab0 x)
    have h := rankOne_coercive (a x) (b x) (F x) (g.inner x v v)
      (scalarDifferential u x v) (metric_inner_nonneg g x v) (hdual x v)
    change 0 < a x * g.inner x v v + b x * (scalarDifferential u x v * scalarDifferential u x v)
    simpa only [pow_two] using (mul_pos hδ (g.pos x v hv)).trans_le h
  isVonNBounded x := by
    let δ := min (a x) (a x + b x * F x)
    have hδ : 0 < δ := lt_min (ha0 x) (hab0 x)
    have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
    apply ((g.isVonNBounded x).image ((Real.sqrt δ)⁻¹ •
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) x))).subset
    intro v hv
    refine ⟨Real.sqrt δ • v, ?_, ?_⟩
    · change g.inner x (Real.sqrt δ • v) (Real.sqrt δ • v) < 1
      have h := rankOne_coercive (a x) (b x) (F x) (g.inner x v v)
        (scalarDifferential u x v) (metric_inner_nonneg g x v) (hdual x v)
      have hv' : a x * g.inner x v v + b x * (scalarDifferential u x v) ^ 2 < 1 := by
        change a x * g.inner x v v + b x * (scalarDifferential u x v * scalarDifferential u x v) < 1 at hv
        simpa only [pow_two] using hv
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← pow_two, Real.sq_sqrt hδ.le]
      exact h.trans_lt hv'
    · simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
      exact inv_smul_smul₀ (ne_of_gt hsq) v
  contMDiff := (ha.smul_section g.contMDiff).add_section
    (hb.smul_section (contMDiff_pullbackInner u hu))

def differentialMetric (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (a b : M → ℝ)
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (ha0 : ∀ x, 0 < a x)
    (hab0 : ∀ x, 0 < a x + b x * coordinateGradientPair g u u x) : SmoothMetric E M :=
  rankOneMetric g u hu a b ha hb (coordinateGradientPair g u u) ha0 hab0
    (scalarDifferential_dual_bound hu g)


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoordinateGradientPairScalarCorrection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def intrinsicCorrectionD (g : SmoothMetric E M) (n : ℝ) (u : M → ℝ) (x : M) : ℝ :=
  n ^ 2 * u x ^ 2 + coordinateGradientPair g u u x

def intrinsicCorrectionF (g : SmoothMetric E M) (n Λ : ℝ) (u : M → ℝ) (x : M) : ℝ :=
  (laplaceBeltrami g u x + Λ * u x) / intrinsicCorrectionD g n u x

def intrinsicCorrectionB (g : SmoothMetric E M) (n Λ : ℝ) (u : M → ℝ) (x : M) : ℝ :=
  1 - intrinsicCorrectionF g n Λ u x * u x

def intrinsicCorrectionS (g : SmoothMetric E M) (n Λ : ℝ) (u : M → ℝ) (x : M) : ℝ :=
  1 - Λ⁻¹ * (n ^ 2 * intrinsicCorrectionF g n Λ u x * u x -
    weightedLaplacian g (intrinsicCorrectionF g n Λ u) u x)



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartGradientProjectionSmooth
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def chartGradientField (g : SmoothMetric E M) (u : M → ℝ) (p : M)
    (i : CoordIndex E) (y : E) : ℝ :=
  coordinateFlux (Module.finBasis ℝ E) (fun z => (metricCoefficients g p z)⁻¹)
    (u ∘ (chartAt E p).symm) i y


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff

open scoped Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def chartGradientProjection (g : SmoothMetric E M) (u : M → ℝ) (p : M)
    (i j : CoordIndex E) (y : E) : ℝ :=
  chartGradientField g u p i y *
    fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j) /
      localGradientPair g u u p y

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactMetricInverseJets
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
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
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
open Set Filter Function Manifold BoxIntegral Metric
open scoped Topology ContDiff

def sphericalChartWeight (φ : Sphere 3 → ℝ) (n : ℕ) (y : Fin 3 → ℝ) : ℝ :=
  Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm (normalWaveEquiv y)))+
    ‖roundPlanarChart sourceAxisOne sourceAxisTwo sourcePole (normalWaveEquiv y)‖^n

def sphericalExceptionalInChart (φ : Sphere 3 → ℝ) (n : ℕ) : Set (Fin 3 → ℝ) :=
  {y | ‖roundPlanarChart sourceAxisOne sourceAxisTwo sourcePole (normalWaveEquiv y)‖^n ≤
    (n:ℝ)^6*Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm (normalWaveEquiv y)))}


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_BundleMetricInner
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def exponentialMetric (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) : SmoothMetric E M :=
  bundlePullbackMetric g (bundleExp K) (bundleExp_smooth K hK) (bundleExp_injective K)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PinnedMetricJointGradientPair
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def pinnedMetric (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) (t : ℝ) : SmoothMetric E M :=
  exponentialMetric g (fun x => (-t/2) • K x) (hK.const_smul_section (a := -t/2))


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem pinnedMetric_joint_coefficients (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (p : M) (i j : CoordIndex E) (t : ℝ) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (pinnedMetric g K hK z.1) p z.2 i j) (t,y) := by
  have hs : ContMDiffAt 𝓘(ℝ,ℝ × E) 𝓘(ℝ,E) ∞ (fun z : ℝ × E => z.2) (t,y) :=
    contDiffAt_snd.contMDiffAt
  have hf : ContMDiffAt 𝓘(ℝ,ℝ × E) 𝓘(ℝ,E) ∞
      (fun z : ℝ × E => (chartAt E p).symm z.2) (t,y) :=
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy).comp (t,y) hs
  have hk := (hK _).comp (t,y) hf
  have ha : ContMDiffAt 𝓘(ℝ,ℝ × E) 𝓘(ℝ,ℝ) ∞ (fun z : ℝ × E => -z.1/2) (t,y) :=
    (contDiffAt_fst.neg.div_const 2).contMDiffAt
  have he := contMDiffAt_exp_along _ (contMDiffAt_smul_along _ hk ha)
  have hi := (contMDiffAt_coordinateVector p i hy).comp (t,y) hs
  have hj := (contMDiffAt_coordinateVector p j hy).comp (t,y) hs
  have hh := ((g.contMDiff _).comp (t,y) hf).clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : M => ℝ)
    (he.clm_bundle_apply hi) (he.clm_bundle_apply hj)
  rw [contMDiffAt_totalSpace] at hh
  exact contMDiffAt_iff_contDiffAt.mp hh.2

end


open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff Matrix BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PinningTensorSpace
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def pinningTensorSpace (g : SmoothMetric E M) (u : M → ℝ) (U : Set M) :
    Submodule ℝ (∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x) where
  carrier := {K | ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)) ∧
    (∀ x a b, g.inner x (K x a) b = g.inner x a (K x b)) ∧
    (∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0) ∧
    (∀ x, K x (metricGradient g u x) = 0) ∧ (∀ x, x ∉ U → K x = 0)}
  zero_mem' := by
    refine ⟨contMDiff_zeroSection ℝ _,?_,?_,?_,?_⟩
    · intros; simp
    · intro x
      change LinearMap.trace ℝ E (0 : E →ₗ[ℝ] E) = 0
      exact map_zero _
    · intros; simp
    · intros; rfl
  add_mem' := by
    rintro K L ⟨hK,hKs,hKt,hKu,hKU⟩ ⟨hL,hLs,hLt,hLu,hLU⟩
    refine ⟨hK.add_section hL,?_,?_,?_,?_⟩
    · intro x a b
      simp only [Pi.add_apply,add_apply,map_add,hKs,hLs]
    · intro x
      change LinearMap.trace ℝ E ((show E →L[ℝ] E from K x).toLinearMap +
        (show E →L[ℝ] E from L x).toLinearMap) = 0
      rw [map_add,hKt,hLt,add_zero]
    · intro x
      simp only [Pi.add_apply,add_apply,hKu,hLu,add_zero]
    · intro x hx
      simp only [Pi.add_apply,hKU x hx,hLU x hx,add_zero]
  smul_mem' := by
    rintro c K ⟨hK,hKs,hKt,hKu,hKU⟩
    refine ⟨contMDiff_const.smul_section hK,?_,?_,?_,?_⟩
    · intro x a b
      simp only [Pi.smul_apply,smul_apply,map_smul,hKs]
    · intro x
      change LinearMap.trace ℝ E (c • (show E →L[ℝ] E from K x).toLinearMap) = 0
      rw [map_smul,hKt,smul_zero]
    · intro x
      simp only [Pi.smul_apply,smul_apply,hKu,smul_zero]
    · intro x hx
      simp only [Pi.smul_apply,hKU x hx,smul_zero]

def smoothMetricGradientLM (g : SmoothMetric E M) (x : M) :
    RealSmoothFunctions E M →ₗ[ℝ] E where
  toFun u := metricGradient g u x
  map_add' u v := by
    symm
    apply metricGradient_unique
    intro w
    change g.inner x (metricGradient g u x + metricGradient g v x) w =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ((u : M → ℝ)+(v : M → ℝ)) x w
    rw [mfderiv_add (u.contMDiff.mdifferentiable (by simp) x)
      (v.contMDiff.mdifferentiable (by simp) x)]
    simp only [map_add,add_apply,metricGradient_pairing]
    rfl
  map_smul' c u := by
    symm
    apply metricGradient_unique
    intro w
    have hh := ((u.contMDiff.mdifferentiable (by simp) x).hasMFDerivAt.const_smul c).mfderiv
    change g.inner x (c • metricGradient g u x) w =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (c • (u : M → ℝ)) x w
    rw [hh]
    simp only [map_smul,smul_apply,metricGradient_pairing]
    rfl

lemma contMDiff_tensorEnergy (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞
      (fun x => g.inner x (metricGradient g u x) (K x (metricGradient g v x))) := by
  intro x
  have hh := (g.contMDiff x).clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : M => ℝ)
    (contMDiff_metricGradient g hu x) ((hK x).clm_bundle_apply (contMDiff_metricGradient g hv x))
  rw [contMDiffAt_totalSpace] at hh
  exact hh.2
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_SymmLChartTrivialization
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
local instance tensorFormNorm : NormedAddCommGroup (MetricForm E) := inferInstanceAs
  (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
local instance tensorFormSpace : NormedSpace ℝ (MetricForm E) := inferInstanceAs
  (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartTensorCoordLocal1
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
attribute [local instance] OAI.YauCounterexamples.instNormedAddCommGroupContinuousLinearMapRealId_solutions_1
attribute [local instance] OAI.YauCounterexamples.instNormedSpaceRealContinuousLinearMapId_solutions_1
local instance instNormedAddCommGroupMetricForm_1 : NormedAddCommGroup (MetricForm E) := inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
local instance instNormedSpaceRealMetricForm_1 : NormedSpace ℝ (MetricForm E) := inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))

end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
section ChartTensorCoordinate
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal1
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal2
local instance chartTensorCoordLocal3 : NormedAddCommGroup (MetricForm E) := inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
local instance chartTensorCoordLocal4 : NormedSpace ℝ (MetricForm E) := inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
end ChartTensorCoordinate

variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal9
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal10
local instance chartTensorCoordLocal11 : NormedAddCommGroup (MetricForm E) := inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
local instance chartTensorCoordLocal12 : NormedSpace ℝ (MetricForm E) := inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_RoundPowerRadius
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
open Set Filter
open scoped Topology ContDiff ComplexConjugate
variable {d : ℕ}

def roundPowerRadius (a b : Euclidean (d+1)) (k : ℕ) (p : Sphere d) : ℝ × ℝ :=
  powerRadiusMap k (planarLinear a b (p : Euclidean (d+1)))



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


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
def fourToThree (q : FourManifold) : ThreeManifold := (q.1,q.2.1)
lemma fourToThree_product_smooth : ContMDiff 𝓘(ℝ,FourModel) 𝓘(ℝ,ThreeProductModel) ∞ fourToThree := by
  unfold FourModel ThreeProductModel
  rw [modelWithCornersSelf_prod,modelWithCornersSelf_prod,modelWithCornersSelf_prod]
  exact contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)
lemma fourToThree_smooth : ContMDiff 𝓘(ℝ,FourModel) 𝓘(ℝ,ThreeModel) ∞ fourToThree :=
  contMDiff_reModel_target threeModelEquiv fourToThree_product_smooth
lemma fourToCircle_smooth : ContMDiff 𝓘(ℝ,FourModel) 𝓘(ℝ,Euclidean 1) ∞ fourToCircle := by
  unfold FourModel
  rw [modelWithCornersSelf_prod,modelWithCornersSelf_prod]
  exact contMDiff_snd.comp contMDiff_snd
lemma mfderiv_fourToThree (q : FourManifold) (v : FourModel) :
    mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,ThreeModel) fourToThree q v=threeModelEquiv (v.1,v.2.1) := by
  rw [mfderiv_reModel_target threeModelEquiv fourToThree_product_smooth]
  change threeModelEquiv ((mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,ThreeProductModel) fourToThree q : FourModel →L[ℝ] ThreeProductModel) v) = _
  congr 1
  unfold FourModel ThreeProductModel fourToThree
  rw [modelWithCornersSelf_prod,modelWithCornersSelf_prod,modelWithCornersSelf_prod]
  change ((mfderiv _ _ (fun q : FourManifold => (Prod.fst q, (Prod.fst ∘ Prod.snd) q)) q) v) = _
  rw [mfderiv_prodMk mdifferentiableAt_fst (mdifferentiableAt_fst.comp _ mdifferentiableAt_snd)]
  rw [mfderiv_comp _ mdifferentiableAt_fst mdifferentiableAt_snd]
  rw [mfderiv_fst,mfderiv_snd,mfderiv_fst]
  rfl
lemma mfderiv_fourToCircle (q : FourManifold) (v : FourModel) :
    mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,Euclidean 1) fourToCircle q v=v.2.2 := by
  unfold FourModel fourToCircle
  rw [modelWithCornersSelf_prod,modelWithCornersSelf_prod]
  change (mfderiv _ _ (Prod.snd ∘ Prod.snd) q) v = v.2.2
  rw [mfderiv_comp _ mdifferentiableAt_snd mdifferentiableAt_snd]
  rw [mfderiv_snd,mfderiv_snd]
  rfl

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
lemma productAxis_inner (i j : Fin 3) : inner ℝ (productAxis i) (productAxis j) = if i=j then 1 else 0 := by
  simp [productAxis,EuclideanSpace.inner_single_left,PiLp.single_apply]
def productB (x : Euclidean 3) : ℂ := planarLinear (productAxis 0) (productAxis 2) x
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ThreeNoncancelNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
def productWeight (r : ℝ) (k : ℕ) (p : ThreeManifold) : ℝ :=
  ‖productA p.1‖^k+r^k*‖productB p.1‖^k

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.mcfDualNorm
attribute [local instance] OAI.YauCounterexamples.mcfDualSpace
attribute [local instance] OAI.YauCounterexamples.mcfFormNorm
attribute [local instance] OAI.YauCounterexamples.mcfFormSpace
attribute [local instance] OAI.YauCounterexamples.mcfMatrixMapNorm
attribute [local instance] OAI.YauCounterexamples.mcfMapMatrixNorm
def metricMatrixFormCLM : Matrix (CoordIndex E) (CoordIndex E) ℝ →L[ℝ] CoordinateForm E :=
  ({ toFun := metricMatrixForm
     map_add' := by
       intro A B
       simp only [metricMatrixForm, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
     map_smul' := by
       intro c A
       simp only [metricMatrixForm, Matrix.smul_apply, smul_eq_mul, mul_smul,
         Finset.smul_sum, RingHom.id_apply] } :
    Matrix (CoordIndex E) (CoordIndex E) ℝ →ₗ[ℝ] CoordinateForm E).toContinuousLinearMap


end

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
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.hmsDualNorm
attribute [local instance] OAI.YauCounterexamples.hmsDualSpace
local instance hmsFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance hmsFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance
local instance hmsDerivNorm : NormedAddCommGroup (E →L[ℝ] CoordinateForm E) := inferInstance

local instance hmsDerivSpace_r16d908_1 : NormedSpace ℝ (E →L[ℝ] CoordinateForm E) := inferInstance
def christoffelFromJet (B : CoordinateForm E) (D : E →L[ℝ] CoordinateForm E) :
    E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E) B.inverse).comp (coordinateKoszul D)

def metricHessianFromFullJet (z : HessianJetData E) : CoordinateForm E :=
  z.2.2 - (ContinuousLinearMap.compL ℝ E E ℝ z.2.1).comp (christoffelFromJet z.1.1 z.1.2)

def metricScalarJet (g : SmoothMetric E E) (f : E → ℝ) (x : E) : HessianJetData E :=
  ((selfMetricFlat g x,fderiv ℝ (selfMetricFlat g) x),
    (fderiv ℝ f x,fderiv ℝ (fderiv ℝ f) x))

def hessianJetMarginSet : Set (HessianJetData E) :=
    {z | hessianMargins z.1.1 (metricHessianFromFullJet z)}


end

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
local instance spnFormNorm : NormedAddCommGroup (CoordinateForm (Euclidean n)) := inferInstance


end

section
open Set Filter Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]
attribute [local instance] OAI.YauCounterexamples.matrixJetInst1
attribute [local instance] OAI.YauCounterexamples.matrixJetInst2
local instance matrixJetInst3 : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance matrixJetInst4 : NormedSpace ℝ (CoordinateForm E) := inferInstance
end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction Matrix.Norms.Elementwise
variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
attribute [local instance] OAI.YauCounterexamples.compactSmoothContinuityInst1
attribute [local instance] OAI.YauCounterexamples.compactSmoothContinuityInst2
local instance compactSmoothContinuityInst3 : NormedAddCommGroup (MetricForm E) := inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
local instance compactSmoothContinuityInst4 : NormedSpace ℝ (MetricForm E) := inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ChartTensorNeighborhoodInst1
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
attribute [local instance] OAI.YauCounterexamples.chartTensorNeighborhoodInst1
attribute [local instance] OAI.YauCounterexamples.chartTensorNeighborhoodInst2
local instance chartTensorNeighborhoodInst3 : NormedAddCommGroup (MetricForm E) := inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
local instance chartTensorNeighborhoodInst4 : NormedSpace ℝ (MetricForm E) := inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PacketAxisShift
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

def packetAxisShift (x : NormalWaveSpace) (n ε ℓ : ℝ) (j : Fin 3) : NormalWaveSpace :=
  x+(ε/(n*ℓ)) • EuclideanSpace.basisFun (Fin 3) ℝ j

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PrepDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
namespace YauCounterexamples
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
attribute [local instance] OAI.YauCounterexamples.prepDualNorm
attribute [local instance] OAI.YauCounterexamples.prepDualSpace
local instance prepFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PulledGradientNorm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def corrugationSecondRemainder
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (ψ χ : E → ℝ) (F : V → ℝ) (y : E → V)
    (d N : ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  coordinateCovariantSecond Γ (fun z => ψ z+(d/N)*(χ z*F (N • y z))) x -
    coordinateCovariantSecond Γ ψ x -
      (d*N*χ x) • (fderiv ℝ (fderiv ℝ F) (N • y x)).bilinearComp
        (fderiv ℝ y x) (fderiv ℝ y x)


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
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

def pulledRadialLeading (j : V →L[ℝ] E) (y : E → ProfilePlane) (β : ℝ → ℝ)
    (b N : ℝ) (x : E) : ProfileForm V :=
  (fderiv ℝ (fderiv ℝ (periodicRadialFunction β b)) (N • y x)).bilinearComp
    ((fderiv ℝ y x).comp j) ((fderiv ℝ y x).comp j)

def pulledRadialRemainder (Γ : E → E →L[ℝ] E →L[ℝ] E) (j : V →L[ℝ] E)
    (ψ χ : E → ℝ) (y : E → ProfilePlane) (β : ℝ → ℝ) (b δ A N : ℝ) (x : E) : ProfileForm V :=
  (corrugationSecondRemainder Γ ψ χ (periodicRadialFunction β b) y (δ*A) N x).bilinearComp j j



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SmDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
attribute [local instance] OAI.YauCounterexamples.smDualNorm
attribute [local instance] OAI.YauCounterexamples.smDualSpace
local instance smFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance smFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance
local instance smDerivNorm : NormedAddCommGroup (E →L[ℝ] CoordinateForm E) := inferInstance

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RadialFiniteDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section


section
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff
def profileTorusLift (τ : ProfileTorus) : ProfilePlane := ((AddCircle.equivIco (1:ℝ) 0 τ.1 : ℝ),(AddCircle.equivIco (1:ℝ) 0 τ.2 : ℝ))

end


open Set Function Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ENNReal InnerProductSpace ContDiff

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CutoffFactorCompactRaw
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Manifold
open scoped Topology ContDiff InnerProductSpace

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def chartInverseDifferentialBound (g : SmoothMetric E M) (p : M) (y : E) : ℝ :=
  ∑ i, ∑ j, |(metricCoefficients g p y)⁻¹ i j| *
    ‖Module.finBasis ℝ E i‖*‖Module.finBasis ℝ E j‖

end



open Set Filter Function Manifold
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ExistsCompactSignedEnvelope
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] OAI.YauCounterexamples.perturbDualNorm
attribute [local instance] OAI.YauCounterexamples.perturbDualSpace
local instance perturbFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
end


open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_CompactRegularLevelIntrinsicFinite
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter MeasureTheory BoxIntegral
open scoped Topology ContDiff

def normalCoordinateVolume : Measure NormalWaveSpace := Measure.map normalWaveEquiv volume

instance normalCoordinateVolume_finiteOnCompacts : IsFiniteMeasureOnCompacts normalCoordinateVolume where
  lt_top_of_isCompact K hK := by
    rw [normalCoordinateVolume,Measure.map_apply normalWaveEquiv.continuous.measurable hK.measurableSet]
    have he : normalWaveEquiv ⁻¹' K = normalWaveEquiv.symm '' K := by
      ext x
      constructor
      · intro hx; exact ⟨normalWaveEquiv x,hx,normalWaveEquiv.symm_apply_apply x⟩
      · rintro ⟨y,hy,h⟩
        change normalWaveEquiv x ∈ K
        rw [←h,normalWaveEquiv.apply_symm_apply]
        exact hy
    rw [he]
    exact (hK.image normalWaveEquiv.symm.continuous).measure_lt_top

end



open Set Filter Metric Manifold MeasureTheory Bundle
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Function Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SourceSignBox
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
open scoped Topology ContDiff
open Set Filter Manifold MeasureTheory BoxIntegral
open scoped Topology ContDiff
namespace YauCounterexamples

def sourceSignRegion : Set (Sphere 3) :=
  (chartAt (Euclidean 3) sourcePole).symm '' (normalWaveEquiv '' Box.Ioo sourceSignBox)

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
section
open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
def metricPullbackInner (g : SmoothMetric F N) (f : M → N) (x : M) :
    TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ :=
  ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x).precomp ℝ).comp
    ((g.inner (f x)).comp (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x))
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma metricPullbackInner_smooth (g : SmoothMetric F N) (f : M → N)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) :
    ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (metricPullbackInner (E:=E) g f x)) := by
  intro x₀
  rw [contMDiffAt_section x₀]
  have hd := (hf x₀).mfderiv_const (m:=∞) (by simp)
  have hg := g.contMDiff (f x₀)
  rw [contMDiffAt_section (f x₀)] at hg
  have hgf := hg.comp x₀ (hf x₀)
  have hh := hd.clm_precomp (F₃:=ℝ) |>.clm_comp (hgf.clm_comp hd)
  apply hh.congr_of_eventuallyEq
  have hn := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x₀)
  have hnf := (hf x₀).continuousAt.eventually ((trivializationAt F (TangentSpace 𝓘(ℝ,F)) (f x₀)).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F _ (f x₀)))
  filter_upwards [hn,hnf] with x hx hy
  ext v w
  simp only [hom_trivializationAt_apply,ContinuousLinearMap.comp_apply,inTangentCoordinates,Function.comp_apply,id_eq]
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  rw [ContinuousLinearMap.inCoordinates_eq hx hy]
  simp only [ContinuousLinearMap.precomp_apply,ContinuousLinearMap.comp_apply]
  rw [inCoordinates_apply_eq₂ hy hy (by simp)]
  simp [metricPullbackInner,
    Trivialization.continuousLinearEquivAt_apply,
    Trivialization.continuousLinearEquivAt_symm_apply,
    Trivialization.symm_apply_apply_mk (trivializationAt F (TangentSpace 𝓘(ℝ,F)) (f x₀)) hy]
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff

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
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
open Set Filter Manifold
open scoped Topology ContDiff

def sphericalWaveLift (u : Euclidean 3 → ℝ) : Sphere 3 → ℝ := manifoldChartPush sourcePole u


end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

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
open Set Filter Function Manifold Bundle MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
local instance instMeasurableSpaceThreeManifold : MeasurableSpace ThreeManifold := borel ThreeManifold
end


section
open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
local instance instMeasurableSpaceThreeManifold_1 : MeasurableSpace ThreeManifold := borel ThreeManifold
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
section
open Set Filter Manifold Bundle Function Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
def fourSplitEquiv : FourModel ≃L[ℝ] ThreeModel × Euclidean 1 :=
  (ContinuousLinearEquiv.prodAssoc ℝ (Euclidean 2) (Euclidean 1) (Euclidean 1)).symm.trans
    (threeModelEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (Euclidean 1)))
def fourProjThree : FourModel →L[ℝ] ThreeModel :=
  (ContinuousLinearMap.fst ℝ ThreeModel (Euclidean 1)).comp fourSplitEquiv.toContinuousLinearMap
def fourProjCircle : FourModel →L[ℝ] Euclidean 1 :=
  (ContinuousLinearMap.snd ℝ ThreeModel (Euclidean 1)).comp fourSplitEquiv.toContinuousLinearMap
end


section
open Set Filter Manifold Bundle Function Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
def fourSplitBasis : Module.Basis (CoordIndex ThreeModel ⊕ CoordIndex (Euclidean 1)) ℝ FourModel :=
  ((Module.finBasis ℝ ThreeModel).prod (Module.finBasis ℝ (Euclidean 1))).map fourSplitEquiv.symm.toLinearEquiv
end


open Set Filter Manifold Bundle Function Matrix BoxIntegral MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise ENNReal NNReal
def fourProfileCenter : FourManifold := (threeProfileCenter.1,(threeProfileCenter.2,1))

end YauCounterexamples
end

end OAI
end


