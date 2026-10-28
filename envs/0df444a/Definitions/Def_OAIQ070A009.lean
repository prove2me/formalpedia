-- Prove2me | Definitions.Def_OAIQ070A009
-- name    : OAIQ070A009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T11:28:52.659216+00:00
-- url     : https://prove2.me/theorems/056aac02-5ffa-41ea-ad49-94021c5d946c
-- title:
--   Definitions bundle OAIQ070A009 of the split of OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 94 declarations of OpenAI's Lean: 37 definitions, 1 instance and 56 theorems. The definitions and types are `OAI.YauCounterexamples.CompactMetricAtlas.localizedFirstJet`, `OAI.YauCounterexamples.CompactMetricAtlas.localizedRealValue`, `OAI.YauCounterexamples.CompactMetricAtlas.parametrix`, `OAI.YauCounterexamples.CompactMetricAtlas.parametrixBound`, `OAI.YauCounterexamples.CompactMetricAtlas.patchOutput`, `OAI.YauCounterexamples.CompactMetricAtlas.patchParametrix`, `OAI.YauCounterexamples.CompactMetricAtlas.polynomial`, `OAI.YauCounterexamples.CompactMetricAtlas.power`, `OAI.YauCounterexamples.CompactMetricAtlas.product`, `OAI.YauCounterexamples.CompactMetricAtlas.productConstant`, `OAI.YauCounterexamples.CompactMetricAtlas.realDivergence`, `OAI.YauCounterexamples.CompactMetricAtlas.realInclusion`, `OAI.YauCounterexamples.CompactMetricAtlas.realLaplacian`, `OAI.YauCounterexamples.CompactMetricAtlas.realOfSmooth`, `OAI.YauCounterexamples.CompactMetricAtlas.realProduct`, `OAI.YauCounterexamples.CompactMetricAtlas.realResolvent`, `OAI.YauCounterexamples.CompactMetricAtlas.realSmoothRepresentativeLM`, `OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent`, `OAI.YauCounterexamples.CompactMetricAtlas.resolvent`, `OAI.YauCounterexamples.CompactMetricAtlas.smoothProduct`, `OAI.YauCounterexamples.CompactMetricAtlas.spectralResolvent`, `OAI.YauCounterexamples.CompactMetricAtlas.varyingLaplacianCLM`, `OAI.YauCounterexamples.CompactMetricAtlas.varyingLaplacianPatch`, `OAI.YauCounterexamples.CompactMetricAtlas.varyingRealLaplacian`, `OAI.YauCounterexamples.CompactMetricAtlas.varyingResolvent`, `OAI.YauCounterexamples.CompactMetricAtlas.varyingShift`, `OAI.YauCounterexamples.CompactMetricAtlas.varyingSpectralResolvent`, `OAI.YauCounterexamples.actualProfileCycleGain`, `OAI.YauCounterexamples.actualProfileFull`, `OAI.YauCounterexamples.actualProfileMass`, `OAI.YauCounterexamples.actualProfileSpeed`, `OAI.YauCounterexamples.actualProfileStrict`, `OAI.YauCounterexamples.actualProfileWeightedMeasure`, `OAI.YauCounterexamples.admissibleCritical`, `OAI.YauCounterexamples.admissibleNoncritical`, `OAI.YauCounterexamples.fixedRadialChoice`, `OAI.YauCounterexamples.smoothMulLinear`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `SmoothYau_DifferentialEq_TransferAcross`, `SmoothYau_Estimates_CoefficientPerturbationTendsto`, `SmoothYau_Estimates_FixedRadialChoice`, `SmoothYau_Estimates_RealValueCubic`, `SmoothYau_Estimates_RescaledCommutatorSobolev`, `SmoothYau_Estimates_RescaledDifferentialPerturbation`, `SmoothYau_Estimates_ScalarAffineDetNeZero`, `SmoothYau_Estimates_VaryingPatchCoefficients`, `SmoothYau_Geometry_ActualProfileCycleGain`, `SmoothYau_Geometry_MetricPatchSource`, `SmoothYau_Geometry_RealForm`, `SmoothYau_Geometry_SymmLChartTrivialization`, `SmoothYau_Limits_RestrictedPinningPencil`, `SmoothYau_NodalMeasure_ActualProfileSpeedNonneg`, `SmoothYau_Smoothness_ChartDerivativeNeZeroTransfer`, `SmoothYau_Smoothness_ContinuousSobolevFirstDerivative`, `SmoothYau_Smoothness_CutoffPullbackLinear`, `SmoothYau_Smoothness_GlobalPrepDualNorm`, `SmoothYau_Smoothness_MomentBesselLp`, `SmoothYau_Smoothness_PulledGradient`, `SmoothYau_Smoothness_SobolevRepresentativeOrderCongr`, `SmoothYau_Spectrum_ContinuousEigenpairLinearization`, `SmoothYau_Spectrum_ScalarCompDirectional`, `SmoothYau_Spectrum_SpectralResolvent`, `SmoothYau_Spectrum_VaryingSpectralResolventBase`.
--
--   **Imports.** It imports the published bundle `Def_SmoothYau`; the bundles `OAIQ070A005`, `OAIQ070A006` and `OAIQ070A007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ070A011`, `OAIQ070A012` and `OAIQ070A013`; the statements `OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple`, `OAI.YauCounterexamples.CompactMetricAtlas.eventually_positive_factor`, `OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent_compact`, `OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent_symmetric`, `OAI.YauCounterexamples.CompactMetricAtlas.smoothFamily_resolvent_tendsto`, `OAI.YauCounterexamples.actual_metric_profile_cycle`, `OAI.YauCounterexamples.actual_metric_radial_finite`, `OAI.YauCounterexamples.actual_preparation_on_compact_patch`, `OAI.YauCounterexamples.compact_actual_sign_noncancellation_supported`, `OAI.YauCounterexamples.compact_actual_waves_sign_and_jets_supported`, `OAI.YauCounterexamples.compact_actual_waves_subregions_supported`, `OAI_YauCounterexamples_conductivity_metric_in_smooth_neighborhood`, `OAI_YauCounterexamples_corrugationSecondRemainder_small_product_scaled_shift`, `OAI.YauCounterexamples.exists_actual_preparation_neighborhood`, `OAI.YauCounterexamples.exists_global_box_amplified_profile`, `OAI.YauCounterexamples.exists_global_spherical_wave_profile`, `OAI.YauCounterexamples.exists_local_metric_radial_patch`, `OAI.YauCounterexamples.exists_supported_box_nodal_quasimodes_subregions`, `OAI.YauCounterexamples.exists_supported_nodal_quasimodes_subregions`, `OAI.YauCounterexamples.exists_three_profile_seed`, `OAI.YauCounterexamples.exists_three_robust_exhaustible_envelopes`, `OAI.YauCounterexamples.exists_three_robust_global_profile_family`, `OAI.YauCounterexamples.exists_three_robust_seed`, `OAI_YauCounterexamples_four_signCertificate_bound`, `OAI_YauCounterexamples_generated_cutoff_wave_residual_estimate`, `OAI_YauCounterexamples_source_baseProfile_sign_gradient` and `OAI_YauCounterexamples_uniformSmoothWaveAmplitudes_genuine`; the proofs of `OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple`, `OAI.YauCounterexamples.CompactMetricAtlas.actual_simple_eigenpair_persistence`, `OAI.YauCounterexamples.CompactMetricAtlas.eventually_positive_factor`, `OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_factor_raw`, `OAI.YauCounterexamples.CompactMetricAtlas.laplaceVariationTest_eigen_zero`, `OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent_compact`, `OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent_symmetric`, `OAI.YauCounterexamples.CompactMetricAtlas.smoothFamily_resolvent_tendsto`, `OAI.YauCounterexamples.actual_metric_profile_cycle`, `OAI.YauCounterexamples.actual_metric_radial_finite`, `OAI.YauCounterexamples.actual_preparation_on_compact_patch`, `OAI.YauCounterexamples.compact_actual_sign_noncancellation_supported`, `OAI.YauCounterexamples.compact_actual_waves_sign_and_jets_supported`, `OAI.YauCounterexamples.compact_actual_waves_subregions_supported`, `OAI.YauCounterexamples.compact_profile_three_phase_data`, `OAI_YauCounterexamples_corrugationSecondRemainder_small_product_scaled_shift`, `OAI.YauCounterexamples.exists_actual_preparation_neighborhood`, `OAI.YauCounterexamples.exists_global_box_amplified_profile`, `OAI.YauCounterexamples.exists_global_spherical_wave_profile`, `OAI.YauCounterexamples.exists_local_metric_radial_patch`, `OAI.YauCounterexamples.exists_spherical_chart_quasimodes`, `OAI.YauCounterexamples.exists_supported_box_nodal_quasimodes_subregions`, `OAI.YauCounterexamples.exists_supported_nodal_quasimodes_subregions`, `OAI.YauCounterexamples.exists_three_chart_quasimodes_with_gaps`, `OAI.YauCounterexamples.exists_three_profile_seed`, `OAI.YauCounterexamples.exists_three_robust_exhaustible_envelopes`, `OAI.YauCounterexamples.exists_three_robust_global_profile_family`, `OAI.YauCounterexamples.exists_three_robust_seed`, `OAI.YauCounterexamples.exists_three_scalar_producer`, `OAI.YauCounterexamples.nonempty_compactMetricAtlas`, `OAI.YauCounterexamples.proportional_eigen_global`, `OAI.YauCounterexamples.roundPower_strict_profile_residual_rapid_decay`, `OAI_YauCounterexamples_smooth_first_integral`, `OAI_YauCounterexamples_source_baseProfile_sign_gradient`, `OAI.YauCounterexamples.spherical_largeWitness_eventually`, `OAI.YauCounterexamples.spherical_wave_background_chart_bounds`, `OAI.YauCounterexamples.spherical_wave_residual_support`, `OAI.YauCounterexamples.threeCoupled_dominated_residual_rapid_decay`, `OAI.YauCounterexamples.threeCoupled_global_residual_rapid_decay`, `OAI.YauCounterexamples.three_wave_background_chart_bounds`, `OAI.YauCounterexamples.three_wave_residual_support` and `OAI_YauCounterexamples_uniformSmoothWaveAmplitudes_genuine`.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A005
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007

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

theorem completePhaseColumns_isSymm (U : RealForm V) (a b : V) :
    (completePhaseColumns U a b).IsSymm := by
  constructor
  intro x y
  simp only [completePhaseColumns_apply]
  ring

theorem completePhaseColumns_column_a (U : RealForm V) (hU : U.IsSymm)
    (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) (hab : inner ℝ a b = 0)
    (x : V) :
    completePhaseColumns U a b a x = -U b x := by
  have ha2 : inner ℝ a a ≠ 0 := ne_of_gt (real_inner_self_pos.mpr ha)
  have hb2 : inner ℝ b b ≠ 0 := ne_of_gt (real_inner_self_pos.mpr hb)
  have hba : inner ℝ b a = 0 := by rw [real_inner_comm, hab]
  rw [completePhaseColumns_apply, hba, hU.eq b a]
  simp only [zero_mul, zero_add, mul_zero]
  field_simp
  ring

theorem completePhaseColumns_column_b (U : RealForm V) (a b : V)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : inner ℝ a b = 0)
    (htrace : U a a + U b b = 0) (x : V) :
    completePhaseColumns U a b b x = U a x := by
  have ha2 : inner ℝ a a ≠ 0 := ne_of_gt (real_inner_self_pos.mpr ha)
  have hb2 : inner ℝ b b ≠ 0 := ne_of_gt (real_inner_self_pos.mpr hb)
  have huu : U b b = -U a a := by linarith
  rw [completePhaseColumns_apply, hab, huu]
  simp only [zero_mul, zero_add, mul_zero]
  field_simp
  ring

def admissibleNoncritical (H : RealForm V) (hH : H.IsSymm)
    (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) (hab : inner ℝ a b = 0)
    (hstrict : 0 < H a a + H b b) : AdmissiblePhaseHessian H a b := by
  let α := (H a a + H b b) / (inner ℝ a a + inner ℝ b b)
  have hden : 0 < inner ℝ a a + inner ℝ b b :=
    add_pos (real_inner_self_pos.mpr ha) (real_inner_self_pos.mpr hb)
  have hα : 0 < α := div_pos hstrict hden
  let U : RealForm V := H - α • innerForm
  have hU : U.IsSymm := hH.sub (innerForm_isSymm.smul α)
  have htrace : U a a + U b b = 0 := by
    change (H a a - α * inner ℝ a a) + (H b b - α * inner ℝ b b) = 0
    dsimp [α]
    field_simp
    ring
  exact {
    realPart := U
    imagPart := completePhaseColumns U a b
    real_symm := hU
    imag_symm := completePhaseColumns_isSymm U a b
    column_b := completePhaseColumns_column_b U a b ha hb hab htrace
    column_a := completePhaseColumns_column_a U hU a b ha hb hab
    gap := by
      intro x hx
      change H x x - α * inner ℝ x x < H x x
      exact sub_lt_self _ (mul_pos hα (real_inner_self_pos.mpr hx)) }

theorem phaseCriticalProjection_self (H : RealForm V) (b : V) (hb : H b b ≠ 0) :
    phaseCriticalProjection H b b = 0 := by
  simp [hb]

theorem phaseCriticalCorrection_isSymm (H : RealForm V) (b : V) :
    (phaseCriticalCorrection H b).IsSymm := by
  constructor
  intro x y
  simp only [phaseCriticalCorrection_apply]
  rw [real_inner_comm (phaseCriticalProjection H b y) (phaseCriticalProjection H b x)]
  ring

theorem phaseCriticalCorrection_pos (H : RealForm V) (b : V) (hb : 0 < H b b)
    (x : V) (hx : x ≠ 0) : 0 < phaseCriticalCorrection H b x x := by
  rw [phaseCriticalCorrection_apply]
  by_cases hbx : H b x = 0
  · simpa [phaseCriticalProjection_apply, hbx] using real_inner_self_pos.mpr hx
  · have hfirst : 0 < (H b b)⁻¹ * (H b x * H b x) :=
      mul_pos (inv_pos.mpr hb) (mul_self_pos.mpr hbx)
    exact add_pos_of_pos_of_nonneg hfirst (real_inner_self_nonneg)

theorem phaseCriticalCorrection_column (H : RealForm V) (b : V) (hb : H b b ≠ 0)
    (x : V) : phaseCriticalCorrection H b b x = H b x := by
  rw [phaseCriticalCorrection_apply, phaseCriticalProjection_self H b hb]
  simp [hb]

def admissibleCritical (H : RealForm V) (hH : H.IsSymm)
    (b : V) (hb : 0 < H b b) : AdmissiblePhaseHessian H 0 b := by
  let U := H - phaseCriticalCorrection H b
  have hUb (x : V) : U b x = 0 := by
    change H b x - phaseCriticalCorrection H b b x = 0
    rw [phaseCriticalCorrection_column H b (ne_of_gt hb), sub_self]
  exact {
    realPart := U
    imagPart := 0
    real_symm := hH.sub (phaseCriticalCorrection_isSymm H b)
    imag_symm := ⟨by simp⟩
    column_b := by intro x; simp
    column_a := by intro x; simp [hUb]
    gap := by
      intro x hx
      change H x x - phaseCriticalCorrection H b x x < H x x
      exact sub_lt_self _ (phaseCriticalCorrection_pos H b hb x hx) }

end YauCounterexamples
end

end OAI
end

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
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def actualProfileStrict (g : SmoothMetric E E) (u : E → ℝ) (x : E) : Prop :=
  quadraticPlaneStrict (actualProfileTraceForm g u x)
    ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))

def actualProfileFull (g : SmoothMetric E E) (u : E → ℝ) (x : E) : Prop :=
  quadraticPlaneFull (actualProfileTraceForm g u x)
    ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))


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

theorem periodicRadial_coefficients_bounded {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) (hβv : ∀ t, β t ∈ Icc 0 1)
    {R : ℝ} (hR : 0 < R) :
    ∃ M S K : ℝ, 0 < M ∧ 0 < S ∧ 0 < K ∧ ∀ x : ProfilePlane,
      0 ≤ periodicRadialSpeed β R x ∧ periodicRadialSpeed β R x ≤ M ∧
      0 ≤ periodicAngularSecond β R x ∧
      (periodicRadialSpeed β R x)^2 ≤ S*periodicAngularSecond β R x ∧
      |periodicRadialSecond β R x| ≤ K := by
  obtain ⟨D,hD⟩ := (hβc.deriv.isCompact_range (hβ.continuous_deriv (by simp))).exists_bound_of_continuousOn
    (f := id) continuous_id.continuousOn
  let D' := max D 0
  have hD' : 0 ≤ D' := le_max_right _ _
  have hDb : ∀ t, |deriv β t| ≤ D' := fun t =>
    (hD _ (mem_range_self t)).trans (le_max_left _ _)
  refine ⟨4*R+1,4*R^2+1,3+8*R^2*D',by positivity,by positivity,by positivity,?_⟩
  intro x
  let z := periodicRadialOffset R x
  let t := z.1^2+z.2^2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htb : t ≤ 2*R^2 := periodicRadialOffset_radius_sq_le hR.le x
  have hs : (Real.sqrt t)^2 = t := Real.sq_sqrt ht
  have hsp : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hsb : Real.sqrt t ≤ 2*R := by nlinarith only [hs,hsp,htb,hR]
  have hp := (hβv t).1
  have hb := (hβv t).2
  have hbp : 0 ≤ β t*(1-β t) := mul_nonneg hp (sub_nonneg.mpr hb)
  change 0 ≤ 2*Real.sqrt t*β t ∧ 2*Real.sqrt t*β t ≤ 4*R+1 ∧
    0 ≤ 2*β t ∧ (2*Real.sqrt t*β t)^2 ≤ (4*R^2+1)*(2*β t) ∧
    |2*β t+4*t*deriv β t| ≤ 3+8*R^2*D'
  refine ⟨by positivity,?_,by positivity,?_,?_⟩
  · have hh := mul_le_mul hsb hb hp (by positivity : 0 ≤ 2*R)
    nlinarith only [hh]
  · calc
      (2*Real.sqrt t*β t)^2 = 4*t*(β t)^2 := by rw [mul_pow,mul_pow,hs]; ring
      _ ≤ 4*t*β t := mul_le_mul_of_nonneg_left (by nlinarith only [hbp]) (by positivity)
      _ ≤ 8*R^2*β t := by nlinarith only [mul_le_mul_of_nonneg_right htb hp]
      _ ≤ (4*R^2+1)*(2*β t) := by nlinarith only [hp]
  · calc
      |2*β t+4*t*deriv β t| ≤ |2*β t|+|4*t*deriv β t| := abs_add_le _ _
      _ = 2*β t+4*t*|deriv β t| := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 2*β t),abs_mul,abs_of_nonneg (by positivity : 0 ≤ 4*t)]
      _ ≤ 2+4*(2*R^2)*D' := add_le_add (by linarith only [hb])
        (mul_le_mul (by nlinarith only [htb]) (hDb t) (abs_nonneg _) (by positivity))
      _ ≤ 3+8*R^2*D' := by ring_nf; linarith


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_MomentBesselLp
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
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
open FourierTransform MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sobolevProduct_schwartz {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (f g : 𝓢(E, ℂ)) :
    sobolevProduct hs (schwartzToSobolev s f) (schwartzToSobolev s g) =
      schwartzToSobolev s (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g) :=
  bilinearExtension_apply _ _ _ _ _ (sobolevAlgebraConstant_nonneg s) f g

theorem sobolevRepresentative_product {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (u v : FourierSobolevSpace E ℂ s) :
    sobolevRepresentative hs (sobolevProduct hs u v) =
      sobolevRepresentative hs u * sobolevRepresentative hs v := by
  refine (denseRange_schwartzToSobolev (E := E) s).induction_on₂ ?_ ?_ u v
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro f g
    rw [sobolevProduct_schwartz, sobolevRepresentative_schwartz,
      sobolevRepresentative_schwartz, sobolevRepresentative_schwartz]
    ext x
    simp [SchwartzMap.pairing_apply_apply]

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

lemma sobolevSecondDerivative_representative {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * (s - 2)) (ht : Module.finrank ℝ E < 2 * s)
    (u : FourierSobolevSpace E ℂ s) (v w x : E) :
    sobolevRepresentative hs (sobolevSecondDerivative s v w u) x =
      fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y w) x v := by
  have hs1 : Module.finrank ℝ E < 2 * (s - 1) := by linarith
  have hs2 : Module.finrank ℝ E < 2 * ((s - 1) - 1) := by linarith
  have hh := sobolevDerivative_representative hs2 hs1 (sobolevDerivative s w u) v x
  have he : (sobolevRepresentative hs1 (sobolevDerivative s w u) : E → ℂ) =
      fun y => fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y w := by
    ext y
    exact sobolevDerivative_representative hs1 ht u w y
  rw [he] at hh
  have hr : sobolevRepresentative hs = sobolevRepresentative hs2 :=
    sobolevRepresentative_congr _ _ (by ring) hs hs2
  rw [sobolevSecondDerivative, ContinuousLinearMap.comp_apply, hr]
  exact hh


end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SobolevRepresentativeOrderCongr
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
open scoped SchwartzMap BoundedContinuousFunction
section FirstOrderSobolev
open scoped SchwartzMap BoundedContinuousFunction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

lemma firstOrderSobolev_representative {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (ht : Module.finrank ℝ E < 2 * (s + 1))
    (β₀ : 𝓢(E, ℂ)) (β : ι → 𝓢(E, ℂ)) (b : ι → E)
    (u : FourierSobolevSpace E ℂ (s + 1)) (x : E) :
    sobolevRepresentative hs (firstOrderSobolev hs β₀ β b u) x =
      β₀ x * sobolevRepresentative ht u x +
        ∑ i, β i x * fderiv ℝ (sobolevRepresentative ht u : E → ℂ) x (b i) := by
  have hd (i : ι) : sobolevRepresentative hs (sobolevDerivative (s + 1) (b i) u) x =
      fderiv ℝ (sobolevRepresentative ht u : E → ℂ) x (b i) := by
    convert sobolevDerivative_representative (s := s + 1)
      (by simpa only [add_sub_cancel_right] using hs) ht u (b i) x using 1
    all_goals try with_reducible_and_instances rfl
    exact congrArg (fun v : E →ᵇ ℂ => v x)
      (sobolevRepresentative_order_congr (s := s) (t := s + 1 - 1) (by ring) hs _ _)
  simp only [firstOrderSobolev, add_apply, sum_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sum, sobolevRepresentative_product,
    sobolevRepresentative_schwartz, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply,
    SchwartzMap.toBoundedContinuousFunction_apply,
    sobolevInclusion_representative (s + 1) s (by linarith) ht hs, hd]
end FirstOrderSobolev



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RescaledCommutatorSobolev
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

lemma rescaledCommutatorSobolev_representative {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * (s + 1))
    (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (p : E) (r : ℝ) (hr : r ≠ 0)
    (u : FourierSobolevSpace E ℂ (s + 1)) (y : E) :
    sobolevRepresentative hs (rescaledCommutatorSobolev hs b a c ha hc χ hχ hχc p r hr u) y =
      euclideanElliptic b a c χ (p + r • y) * sobolevRepresentative ht u y +
        ∑ i, ∑ j, (r : ℂ)⁻¹ * (a i j (p + r • y) : ℂ) *
          (fderiv ℝ χ (p + r • y) (b i) *
              fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b j) +
            fderiv ℝ χ (p + r • y) (b j) *
              fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b i)) := by
  simp only [rescaledCommutatorSobolev, add_apply, map_add,
    BoundedContinuousFunction.add_apply, firstOrderSobolev_representative hs ht,
    affineSchwartz_apply,
    smul_apply, smul_eq_mul, zero_apply, zero_mul,
    zero_add, Fintype.sum_prod_type]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change (r : ℂ)⁻¹ * ((a i j (p + r • y) : ℂ) * fderiv ℝ χ (p + r • y) (b i)) *
      fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b j) +
    (r : ℂ)⁻¹ * ((a i j (p + r • y) : ℂ) * fderiv ℝ χ (p + r • y) (b j)) *
      fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b i) = _
  ring

lemma rescaledCommutatorSobolev_physical {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * (s + 1))
    (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (p : E) (r : ℝ) (hr : r ≠ 0)
    (u : FourierSobolevSpace E ℂ (s + 1)) (x : E) :
    sobolevRepresentative hs (rescaledCommutatorSobolev hs b a c ha hc χ hχ hχc p r hr u)
        (r⁻¹ • (x - p)) =
      ellipticCommutator b a c χ
        (fun y => sobolevRepresentative ht u (r⁻¹ • (y - p))) x := by
  have hi : p + r • (r⁻¹ • (x - p)) = x := by
    simp only [smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
  have hu : Differentiable ℝ (sobolevRepresentative ht u : E → ℂ) :=
    (contDiff_sobolevRepresentative 1 (by norm_num; linarith) ht u).differentiable (by simp)
  rw [rescaledCommutatorSobolev_representative hs ht]
  simp only [hi, ellipticCommutator, fderiv_inverseScalarAffine p r _ _ (hu _),
    Complex.ofReal_inv]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CutoffPullbackLinear
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
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
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sobolevCutoffPullback_schwartz (η : E → ℂ) (hηc : HasCompactSupport η)
    (hη : ContDiff ℝ ∞ η) (φ : E → E) (hφ : ContDiff ℝ ∞ φ)
    (hinj : Set.InjOn φ (tsupport η)) (J : ℝ≥0)
    (hJ : ∀ x ∈ tsupport η, 1 ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(fderiv ℝ φ x).det|)
    (k : ℕ) (f : 𝓢(E, ℂ)) :
    sobolevCutoffPullback η hηc hη φ hφ k (schwartzToSobolev (2 * (k : ℝ)) f) =
      schwartzToSobolev (2 * (k : ℝ)) (cutoffPullback η hηc hη φ hφ f) := by
  obtain ⟨C, _, hC⟩ := cutoffPullback_sobolev_bound η hηc hη φ hφ hinj J hJ k
  exact LinearMap.extendOfNorm_eq (denseRange_schwartzToSobolev _)
    ⟨C, hC⟩ f

theorem sobolevRepresentative_cutoffPullback (η : E → ℂ) (hηc : HasCompactSupport η)
    (hη : ContDiff ℝ ∞ η) (φ : E → E) (hφ : ContDiff ℝ ∞ φ)
    (hinj : Set.InjOn φ (tsupport η)) (J : ℝ≥0)
    (hJ : ∀ x ∈ tsupport η, 1 ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(fderiv ℝ φ x).det|)
    (k : ℕ) (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ)))
    (u : FourierSobolevSpace E ℂ (2 * (k : ℝ))) (x : E) :
    sobolevRepresentative hs (sobolevCutoffPullback η hηc hη φ hφ k u) x =
      η x * sobolevRepresentative hs u (φ x) := by
  refine (denseRange_schwartzToSobolev (E := E) (2 * (k : ℝ))).induction_on u ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro f
    rw [sobolevCutoffPullback_schwartz η hηc hη φ hφ hinj J hJ,
      sobolevRepresentative_schwartz, sobolevRepresentative_schwartz]
    rfl

end YauCounterexamples

open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ScalarAffineDetNeZero
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sobolevAffineCutoff_representative (η : E → ℂ) (hηc : HasCompactSupport η)
    (hη : ContDiff ℝ ∞ η) (p : E) {r : ℝ} (hr : r ≠ 0)
    (k : ℕ) (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ)))
    (u : FourierSobolevSpace E ℂ (2 * (k : ℝ))) (x : E) :
    sobolevRepresentative hs (sobolevAffineCutoff η hηc hη p r k u) x =
      η x * sobolevRepresentative hs u (p + r • x) := by
  obtain ⟨J, hJ⟩ := compact_jacobian_bound hηc (show ContDiff ℝ ∞ (fun y : E => p + r • y) by fun_prop)
    (fun y _ => scalarAffine_det_ne_zero p hr y)
  apply sobolevRepresentative_cutoffPullback η hηc hη _ _ _ J hJ k hs u x
  intro y _ z _ he
  exact (smul_right_injective E hr) (add_left_cancel he)

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
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sobolevFirstLower_representative (s : ℝ) (v : E)
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * (s + 2))
    (u : FourierSobolevSpace E ℂ (s + 2)) (x : E) :
    sobolevRepresentative hs (sobolevFirstLower s v u) x =
      fderiv ℝ (sobolevRepresentative ht u : E → ℂ) x v := by
  have hl : Module.finrank ℝ E < 2 * (s + 2 - 1) := by linarith
  rw [sobolevFirstLower, ContinuousLinearMap.comp_apply,
    sobolevInclusion_representative _ _ _ hl hs]
  exact sobolevDerivative_representative hl ht u v x

lemma coefficientPerturbation_representative {ι : Type*} [Fintype ι] (b : ι → E) {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * (s + 2))
    (a : ι → ι → FourierSobolevSpace E ℂ s) (c : ι → FourierSobolevSpace E ℂ s)
    (u : FourierSobolevSpace E ℂ (s + 2)) (x : E) :
    sobolevRepresentative hs (coefficientPerturbation b hs a c u) x =
      (∑ i, ∑ j, sobolevRepresentative hs (a i j) x *
        fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b j)) x (b i)) +
      ∑ i, sobolevRepresentative hs (c i) x *
        fderiv ℝ (sobolevRepresentative ht u : E → ℂ) x (b i) := by
  have hd (i j : ι) : sobolevRepresentative hs
      (sobolevSecondDerivative (s + 2) (b i) (b j) u) x =
      fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b j)) x (b i) := by
    have hh := sobolevSecondDerivative_representative
      (s := s + 2) (show Module.finrank ℝ E < 2 * (s + 2 - 2) by linarith)
      ht u (b i) (b j) x
    rw [sobolevRepresentative_congr (s + 2 - 2) s (by ring) _ hs] at hh
    exact hh
  simp only [coefficientPerturbation, _root_.add_apply, _root_.sum_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sum,
    BoundedContinuousFunction.add_apply, BoundedContinuousFunction.sum_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [sobolevRepresentative_product, BoundedContinuousFunction.mul_apply, hd]
  · apply Finset.sum_congr rfl
    intro i _
    rw [sobolevRepresentative_product, BoundedContinuousFunction.mul_apply,
      sobolevFirstLower_representative s _ hs ht]


end

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




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_MetricPatchSource
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma metricPatchSource_representative (p : M) (r : ℝ) (hr : r ≠ 0) (k : ℕ)
    (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ)))
    (f : FourierSobolevSpace E ℂ (2 * (k : ℝ))) (y : E) (hy : ‖y‖ ≤ 1) :
    sobolevRepresentative hs (metricPatchSource (E := E) p r k f) y =
      (r : ℂ) ^ 2 * sobolevRepresentative hs f ((chartAt E p) p + r • y) := by
  simp only [metricPatchSource, smul_apply, map_smul, BoundedContinuousFunction.smul_apply,
    smul_eq_mul]
  rw [sobolevAffineCutoff_representative (complexUnitBump E)
    (hasCompactSupport_complexUnitBump E) (contDiff_complexUnitBump E)
    ((chartAt E p) p) hr k hs f y, complexUnitBump_eq_one E hy, one_mul]

lemma metricPatchRawInverse_physical_equation (g : SmoothMetric E M) (p : M) (k : ℕ)
    (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ)))
    (D : LocalMetricInverse g p (2 * (k : ℝ)) hs)
    (α : ℝ) (hα : 1 ≤ α * D.radius ^ 2)
    (ht : Module.finrank ℝ E < 2 * (2 * (k : ℝ) + 2))
    (f : FourierSobolevSpace E ℂ (2 * (k : ℝ))) (x : E)
    (hx : ‖D.radius⁻¹ • (x - (chartAt E p) p)‖ ≤ 1) :
    (α : ℂ) * sobolevRepresentative ht (metricPatchRawInverse g p k hs D α hα f)
        (D.radius⁻¹ • (x - (chartAt E p) p)) -
      euclideanElliptic (Module.finBasis ℝ E)
        (fun i j y => (metricCoefficients g p y)⁻¹ i j) (metricFirstCoefficient g p)
        (fun y => sobolevRepresentative ht (metricPatchRawInverse g p k hs D α hα f)
          (D.radius⁻¹ • (y - (chartAt E p) p))) x =
      sobolevRepresentative hs f x := by
  let w := metricPatchRawInverse g p k hs D α hα f
  have hw : ContDiff ℝ 2 (sobolevRepresentative ht w : E → ℂ) :=
    contDiff_sobolevRepresentative 2 (by norm_num; linarith) ht w
  apply unscale_local_equation (Module.finBasis ℝ E) _ _ ((chartAt E p) p)
    D.radius_pos.ne' α hw (sobolevRepresentative hs f) x
  have he := D.equation (α * D.radius ^ 2) hα ht (metricPatchSource (E := E) p D.radius k f)
    (D.radius⁻¹ • (x - (chartAt E p) p)) hx
  rw [metricPatchSource_representative p D.radius D.radius_pos.ne' k hs f _ hx] at he
  have hi : (chartAt E p) p + D.radius • (D.radius⁻¹ • (x - (chartAt E p) p)) = x := by
    simp only [smul_smul, mul_inv_cancel₀ D.radius_pos.ne', one_smul, add_sub_cancel]
  rw [hi] at he
  simpa only [euclideanElliptic, hi, Complex.ofReal_mul, mul_assoc, ← Finset.mul_sum, sub_add_eq_sub_sub,
    w, metricPatchRawInverse, ContinuousLinearMap.comp_apply] using he
end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ScalarCompDirectional
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Filter Set Matrix Unitary
open scoped Topology ContDiff
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma localLaplacian_change_C2 {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M)
    (p q : M) {y : E} (hy : y ∈ (chartAt E q).target)
    (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    localLaplacian g u q y = localLaplacian g u p (chartTransition p q y) := by
  classical
  have he (i : CoordIndex E) : (fun z => metricFlux g u q z i) =ᶠ[𝓝 y]
      (fun z => ∑ k, |(coordinateTransitionMatrix p q z).det| *
        (coordinateTransitionMatrix p q z)⁻¹ i k * metricFlux g u p (chartTransition p q z) k) := by
    filter_upwards [chart_overlap_nhds p q hy hp] with z hz
    exact metricFlux_change_C2 hu g p q hz.1 hz.2 i
  have hJ : IsUnit (coordinateTransitionMatrix p q y).det :=
    isUnit_iff_ne_zero.mpr (coordinateTransitionMatrix_det_ne_zero g p q hy hp)
  have hi := piola_divergence_abs ((contDiffAt_chartTransition p q hy hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (differentiableAt_metricFlux_C2 hu g p ((chartAt E p).map_source hp))
    (Module.finBasis ℝ E) hJ
  change (∑ i, fderiv ℝ (fun z => ∑ k, |(coordinateTransitionMatrix p q z).det| *
    (coordinateTransitionMatrix p q z)⁻¹ i k * metricFlux g u p (chartTransition p q z) k) y
      (Module.finBasis ℝ E i)) = _ at hi
  simp only [localLaplacian, (he _).fderiv_eq]
  rw [hi, metricDensity_change g p q hy hp]
  have hn := abs_ne_zero.mpr (coordinateTransitionMatrix_det_ne_zero g p q hy hp)
  change (|(coordinateTransitionMatrix p q y).det| * _)⁻¹ *
    (|(coordinateTransitionMatrix p q y).det| * _) = _
  field_simp

lemma laplaceBeltrami_inChart_C2 {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M)
    (p x : M) (hx : x ∈ (chartAt E p).source) :
    laplaceBeltrami g u x = localLaplacian g u p (chartAt E p x) := by
  change localLaplacian g u x (chartAt E x x) = _
  have he := localLaplacian_change_C2 hu g p x ((chartAt E x).map_source (mem_chart_source E x))
    (by simpa only [(chartAt E x).left_inv (mem_chart_source E x)] using hx)
  simpa only [chartTransition, Function.comp_apply, (chartAt E x).left_inv (mem_chart_source E x)] using he


open Set Function Filter
open scoped Topology ContDiff

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Filter Set Matrix Unitary
open scoped Topology ContDiff
open Set Function Filter
open scoped Topology ContDiff
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma complexLaplaceBeltrami_inChart {u : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u) (g : SmoothMetric E M)
    (p : M) {x : M} (hx : x ∈ (chartAt E p).source) :
    complexLaplaceBeltrami g u x =
      euclideanElliptic (Module.finBasis ℝ E)
        (fun i j y => (metricCoefficients g p y)⁻¹ i j)
        (metricFirstCoefficient g p) (u ∘ (chartAt E p).symm) ((chartAt E p) x) := by
  have hur : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (Complex.re ∘ u) :=
    Complex.reCLM.contMDiff.comp hu
  have hui : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (Complex.im ∘ u) :=
    Complex.imCLM.contMDiff.comp hu
  have hf : ContDiffAt ℝ 2 (u ∘ (chartAt E p).symm) ((chartAt E p) x) :=
    contMDiffAt_iff_contDiffAt.mp (hu.contMDiffAt.comp _
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p)
        ((chartAt E p).map_source hx)))
  have hfd := hf.differentiableAt (by norm_num)
  apply Complex.ext
  · change laplaceBeltrami g (Complex.re ∘ u) x = _
    rw [laplaceBeltrami_inChart_C2 hur g p x hx, localLaplacian_expansion_C2 hur g p
      ((chartAt E p).map_source hx)]
    simp only [euclideanElliptic, Complex.add_re, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact clm_second_fderiv Complex.reCLM hf _ _
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact clm_fderiv_apply Complex.reCLM hfd _
  · change laplaceBeltrami g (Complex.im ∘ u) x = _
    rw [laplaceBeltrami_inChart_C2 hui g p x hx, localLaplacian_expansion_C2 hui g p
      ((chartAt E p).map_source hx)]
    simp only [euclideanElliptic, Complex.add_im, Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact clm_second_fderiv Complex.imCLM hf _ _
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact clm_fderiv_apply Complex.imCLM hfd _


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma complexLaplaceBeltrami_add {u v : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 v) (g : SmoothMetric E M) (x : M) :
    complexLaplaceBeltrami g (fun y => u y + v y) x =
      complexLaplaceBeltrami g u x + complexLaplaceBeltrami g v x := by
  erw [complexLaplaceBeltrami_inChart (hu.add hv) g x (mem_chart_source E x),
    complexLaplaceBeltrami_inChart hu g x (mem_chart_source E x),
    complexLaplaceBeltrami_inChart hv g x (mem_chart_source E x)]
  exact euclideanElliptic_add_at _ _ _ (contDiffAt_complex_inChart hu x (mem_chart_source E x))
    (contDiffAt_complex_inChart hv x (mem_chart_source E x))

lemma complexLaplaceBeltrami_zero (g : SmoothMetric E M) (x : M) :
    complexLaplaceBeltrami g 0 x = 0 := by
  erw [complexLaplaceBeltrami_inChart contMDiff_const g x (mem_chart_source E x)]
  exact euclideanElliptic_zero _ _ _ _

lemma complexLaplaceBeltrami_congr {u v : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 v) (g : SmoothMetric E M) {x : M}
    (h : u =ᶠ[𝓝 x] v) : complexLaplaceBeltrami g u x = complexLaplaceBeltrami g v x := by
  erw [complexLaplaceBeltrami_inChart hu g x (mem_chart_source E x),
    complexLaplaceBeltrami_inChart hv g x (mem_chart_source E x)]
  apply euclideanElliptic_congr
  have ht := ((chartAt E x).continuousAt_symm ((chartAt E x).map_source
    (mem_chart_source E x))).tendsto
  rw [(chartAt E x).left_inv (mem_chart_source E x)] at ht
  exact h.comp_tendsto ht

lemma complexLaplaceBeltrami_sum {ι : Type*} (t : Finset ι) (u : ι → M → ℂ)
    (hu : ∀ i ∈ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 (u i))
    (g : SmoothMetric E M) (x : M) :
    complexLaplaceBeltrami g (fun y => ∑ i ∈ t, u i y) x =
      ∑ i ∈ t, complexLaplaceBeltrami g (u i) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using
      (show complexLaplaceBeltrami g (fun _ : M => (0 : ℂ)) x = 0 from
        complexLaplaceBeltrami_zero g x)
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    rw [complexLaplaceBeltrami_add (hu _ (Finset.mem_insert_self _ _))
      (ContMDiff.sum (fun j hj => hu j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))]

lemma complexLaplaceBeltrami_chartLift [T2Space M] (g : SmoothMetric E M)
    (p : M) (χ : M → ℂ) (hχs : tsupport χ ⊆ (chartAt E p).source)
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ χ) {u : E → ℂ}
    (hu : ContDiff ℝ 2 u) {x : M} (hx : x ∈ (chartAt E p).source) :
    complexLaplaceBeltrami g (chartLift (E := E) p χ u) x =
      euclideanElliptic (Module.finBasis ℝ E)
        (fun i j y => (metricCoefficients g p y)⁻¹ i j) (metricFirstCoefficient g p)
        (fun y => chartLocalize (E := E) p χ 1 y * u y) ((chartAt E p) x) := by
  erw [complexLaplaceBeltrami_inChart (contMDiff_chartLift_order p χ hχs hχ 2 hu) g p hx]
  apply euclideanElliptic_congr
  filter_upwards [(chartAt E p).open_target.mem_nhds ((chartAt E p).map_source hx)] with y hy
  simp only [Function.comp_apply, chartLift, chartLocalize_eq p χ 1 hy, Pi.one_apply,
    mul_one, (chartAt E p).right_inv hy]


end

open Set Filter Manifold
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartDerivativeNeZeroTransfer
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def patchParametrix (α : ℝ) (i : A.t) (hα : 1 ≤ α * (A.localInverse i).radius ^ 2) :
    A.H (2 * (k : ℝ)) →L[ℝ] A.H (2 * ((k + 1 : ℕ) : ℝ)) :=
  A.lift (A.p i) (A.ψ i) (A.chart_ψ i) (A.smooth_ψ i) (k + 1) ∘L
    (sobolevAffineCutoff (A.χcoord i) (A.compact_χcoord i) (A.smooth_χcoord i)
      (-((A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) (A.p i)))
      (A.localInverse i).radius⁻¹ (k + 1)).restrictScalars ℝ ∘L
    (metricPatchRawInverse g (A.p i) k hs (A.localInverse i) α hα).restrictScalars ℝ ∘L
    A.localize (2 * (k : ℝ)) i

omit [T2Space M] in
lemma patchParametrix_representative (α : ℝ) (i : A.t)
    (hα : 1 ≤ α * (A.localInverse i).radius ^ 2)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)))
    (u : A.H (2 * (k : ℝ))) (x : M) :
    A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.patchParametrix α i hα u) x =
      A.χ i x * sobolevRepresentative ht
        (metricPatchRawInverse g (A.p i) k hs (A.localInverse i) α hα (u.val i))
        ((A.localInverse i).radius⁻¹ • ((chartAt E (A.p i)) x - (chartAt E (A.p i)) (A.p i))) := by
  simp only [patchParametrix, ContinuousLinearMap.comp_apply]
  rw [A.lift_representative _ _ _ _ (k + 1) ht]
  change A.ψ i x * sobolevRepresentative ht
    (sobolevAffineCutoff (A.χcoord i) (A.compact_χcoord i) (A.smooth_χcoord i)
      (-((A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) (A.p i)))
      (A.localInverse i).radius⁻¹ (k + 1)
      (metricPatchRawInverse g (A.p i) k hs (A.localInverse i) α hα (u.val i)))
    ((chartAt E (A.p i)) x) = _
  rw [sobolevAffineCutoff_representative _ _ _ _
    (inv_ne_zero (A.localInverse i).radius_pos.ne') (k + 1) ht]
  have he : -((A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) (A.p i)) +
      (A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) x =
      (A.localInverse i).radius⁻¹ • ((chartAt E (A.p i)) x - (chartAt E (A.p i)) (A.p i)) := by
    rw [smul_sub, sub_eq_add_neg, add_comm]
  rw [he]
  change A.ψ i x * (A.χcoord i ((chartAt E (A.p i)) x) * _) = _
  by_cases hx : x ∈ (chartAt E (A.p i)).source
  · rw [χcoord, chartLocalize_eq _ _ _ ((chartAt E (A.p i)).map_source hx),
      (chartAt E (A.p i)).left_inv hx, Pi.one_apply, mul_one, ← mul_assoc, A.ψ_mul_χ]
  · have hψ : A.ψ i x = 0 := notMem_support.mp (fun h => hx (A.chart_ψ i (subset_tsupport _ h)))
    have hχ : A.χ i x = 0 := notMem_support.mp (fun h => hx (A.chart_χ i (subset_tsupport _ h)))
    simp only [hψ, hχ, zero_mul]
end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma patchErrorTail_representative (i : A.t) (B : A.PatchCoefficients i)
    (ht : Module.finrank ℝ E < 2 * (2 * (k : ℝ) + 1))
    (u : FourierSobolevSpace E ℂ (2 * (k : ℝ) + 1)) (x : M) :
    A.representative (2 * (k : ℝ)) (A.patchErrorTail i B u) x =
      A.ψ i x * (A.ψcoord i ((chartAt E (A.p i)) x) *
        ellipticCommutator (Module.finBasis ℝ E) B.a B.c (A.χcoord i)
          (fun y => sobolevRepresentative ht u
            ((A.localInverse i).radius⁻¹ • (y - (chartAt E (A.p i)) (A.p i))))
          ((chartAt E (A.p i)) x)) := by
  simp only [patchErrorTail, ContinuousLinearMap.comp_apply]
  rw [A.lift_representative _ _ _ _ k hs]
  change A.ψ i x * sobolevRepresentative hs
    (sobolevAffineCutoff (A.ψcoord i) (A.compact_ψcoord i) (A.smooth_ψcoord i)
      (-((A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) (A.p i)))
      (A.localInverse i).radius⁻¹ k
      (rescaledCommutatorSobolev hs (Module.finBasis ℝ E) B.a B.c B.smooth_a B.smooth_c
        (A.χcoord i) (A.smooth_χcoord i) (A.compact_χcoord i)
        ((chartAt E (A.p i)) (A.p i)) (A.localInverse i).radius
        (A.localInverse i).radius_pos.ne' u)) ((chartAt E (A.p i)) x) = _
  rw [sobolevAffineCutoff_representative _ _ _ _
    (inv_ne_zero (A.localInverse i).radius_pos.ne') k hs]
  have he : -((A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) (A.p i)) +
      (A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) x =
      (A.localInverse i).radius⁻¹ • ((chartAt E (A.p i)) x - (chartAt E (A.p i)) (A.p i)) := by
    rw [smul_sub, sub_eq_add_neg, add_comm]
  rw [he, rescaledCommutatorSobolev_physical hs ht]

omit [T2Space M] in
lemma patchErrorTail_representative_inChart (i : A.t) (B : A.PatchCoefficients i)
    (ht : Module.finrank ℝ E < 2 * (2 * (k : ℝ) + 1))
    (u : FourierSobolevSpace E ℂ (2 * (k : ℝ) + 1)) {x : M}
    (hx : x ∈ (chartAt E (A.p i)).source) :
    A.representative (2 * (k : ℝ)) (A.patchErrorTail i B u) x =
      ellipticCommutator (Module.finBasis ℝ E)
        (fun j l y => (metricCoefficients g (A.p i) y)⁻¹ j l)
        (metricFirstCoefficient g (A.p i)) (A.χcoord i)
        (fun y => sobolevRepresentative ht u
          ((A.localInverse i).radius⁻¹ • (y - (chartAt E (A.p i)) (A.p i))))
        ((chartAt E (A.p i)) x) := by
  rw [A.patchErrorTail_representative i B ht, ψcoord,
    chartLocalize_eq _ _ _ ((chartAt E (A.p i)).map_source hx),
    (chartAt E (A.p i)).left_inv hx, Pi.one_apply, mul_one]
  rw [ellipticCommutator_congr_coeff _ B.a _ B.c _ _ _ B.eq_a B.eq_c]
  by_cases hh : (chartAt E (A.p i)) x ∈ tsupport (A.χcoord i)
  · rw [A.ψ_one_on_χcoord i hx hh, one_mul, one_mul]
  · have he := notMem_support.mp (mt (fun h => support_ellipticCommutator
      (Module.finBasis ℝ E) (fun j l y => (metricCoefficients g (A.p i) y)⁻¹ j l)
      (metricFirstCoefficient g (A.p i)) (A.χcoord i)
      (fun y => sobolevRepresentative ht u
        ((A.localInverse i).radius⁻¹ • (y - (chartAt E (A.p i)) (A.p i)))) h) hh)
    rw [he, mul_zero, mul_zero]

omit [T2Space M] in
lemma patchError_representative_inChart (α : ℝ) (i : A.t) (B : A.PatchCoefficients i)
    (hα : 1 ≤ α * (A.localInverse i).radius ^ 2)
    (ht : Module.finrank ℝ E < 2 * (2 * (k : ℝ) + 2))
    (u : A.H (2 * (k : ℝ))) {x : M} (hx : x ∈ (chartAt E (A.p i)).source) :
    A.representative (2 * (k : ℝ)) (A.patchError α i B hα u) x =
      ellipticCommutator (Module.finBasis ℝ E)
        (fun j l y => (metricCoefficients g (A.p i) y)⁻¹ j l)
        (metricFirstCoefficient g (A.p i)) (A.χcoord i)
        (fun y => sobolevRepresentative ht
          (metricPatchRawInverse g (A.p i) k hs (A.localInverse i) α hα (u.val i))
          ((A.localInverse i).radius⁻¹ • (y - (chartAt E (A.p i)) (A.p i))))
        ((chartAt E (A.p i)) x) := by
  have h1 : Module.finrank ℝ E < 2 * (2 * (k : ℝ) + 1) := by linarith
  simp only [patchError, ContinuousLinearMap.comp_apply]
  rw [A.patchErrorTail_representative_inChart i B h1 _ hx]
  congr 2
  funext y
  exact congrArg (fun f : E →ᵇ ℂ => f _) (sobolevInclusion_representative _ _
    (by linarith : 2 * (k : ℝ) + 1 ≤ 2 * (k : ℝ) + 2) ht h1 _)

lemma patchParametrix_equation (α : ℝ) (i : A.t) (B : A.PatchCoefficients i)
    (hα : 1 ≤ α * (A.localInverse i).radius ^ 2)
    (u : A.H (2 * (k : ℝ))) (x : M) :
    (α : ℂ) * A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.patchParametrix α i hα u) x -
      complexLaplaceBeltrami g
        (A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.patchParametrix α i hα u)) x =
      A.η i x * A.representative (2 * (k : ℝ)) u x -
        A.representative (2 * (k : ℝ)) (A.patchError α i B hα u) x := by
  have ht : Module.finrank ℝ E < 2 * (2 * (k : ℝ) + 2) := by linarith
  have ht' : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)) := by
    norm_num only [Nat.cast_add, Nat.cast_one]; linarith
  let w := metricPatchRawInverse g (A.p i) k hs (A.localInverse i) α hα (u.val i)
  let v : E → ℂ := fun y => sobolevRepresentative ht w
    ((A.localInverse i).radius⁻¹ • (y - (chartAt E (A.p i)) (A.p i)))
  have hv : ContDiff ℝ 2 v :=
    (contDiff_sobolevRepresentative 2 (by norm_num; linarith) ht w).comp (by fun_prop)
  have hQ : (A.representative (2 * ((k + 1 : ℕ) : ℝ))
      (A.patchParametrix α i hα u) : M → ℂ) = chartLift (E := E) (A.p i) (A.χ i) v := by
    funext y
    rw [A.patchParametrix_representative α i hα ht']
    rw [sobolevRepresentative_congr _ _ (by push_cast; ring) ht' ht]
    rfl
  rw [hQ]
  have hQm := contMDiff_chartLift_order (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) 2 hv
  by_cases hx : x ∈ (chartAt E (A.p i)).source
  · rw [complexLaplaceBeltrami_chartLift g (A.p i) (A.χ i) (A.chart_χ i)
      (A.smooth_χ i) hv hx, A.patchError_representative_inChart α i B hα ht u hx]
    have hcut := cutoff_parametrix_equation (Module.finBasis ℝ E)
      (fun j l y => (metricCoefficients g (A.p i) y)⁻¹ j l)
      (metricFirstCoefficient g (A.p i)) ((A.smooth_χcoord i).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hv α
      (sobolevRepresentative hs (u.val i))
      (fun y hy => metricPatchRawInverse_physical_equation g (A.p i) k hs
        (A.localInverse i) α hα ht (u.val i) y (A.χcoord_unit_support i (subset_tsupport _ hy)))
      ((chartAt E (A.p i)) x)
    have hc : A.χcoord i ((chartAt E (A.p i)) x) = A.χ i x := by
      rw [χcoord, chartLocalize_eq _ _ _ ((chartAt E (A.p i)).map_source hx),
        (chartAt E (A.p i)).left_inv hx, Pi.one_apply, mul_one]
    rw [hc, A.localize_representative u i,
      chartLocalize_eq _ _ _ ((chartAt E (A.p i)).map_source hx),
      (chartAt E (A.p i)).left_inv hx] at hcut
    have hprod := congrArg (fun z : ℂ => z * A.representative (2 * (k : ℝ)) u x) (A.χ_mul_η i x)
    rw [mul_assoc] at hprod
    rw [hprod] at hcut
    exact hcut
  · have hψ : A.ψ i x = 0 := notMem_support.mp (fun h => hx (A.chart_ψ i (subset_tsupport _ h)))
    have hχ : x ∉ tsupport (A.χ i) := fun h => hx (A.chart_χ i h)
    have hη : A.η i x = 0 := notMem_support.mp (fun h => hx (A.chart_η i (subset_tsupport _ h)))
    have he : A.representative (2 * (k : ℝ)) (A.patchError α i B hα u) x = 0 := by
      simp only [patchError, ContinuousLinearMap.comp_apply]
      rw [A.patchErrorTail_representative i B (by linarith), hψ, zero_mul]
    have hzero : chartLift (E := E) (A.p i) (A.χ i) v =ᶠ[𝓝 x] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hχ] with y hy
      simp only [chartLift, hy, Pi.zero_apply, zero_mul]
    have hzlap : complexLaplaceBeltrami g (chartLift (E := E) (A.p i) (A.χ i) v) x = 0 :=
      (complexLaplaceBeltrami_congr hQm (show ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 (0 : M → ℂ) from contMDiff_const) g hzero).trans (complexLaplaceBeltrami_zero g x)
    rw [hzlap, hzero.eq_of_nhds, Pi.zero_apply, mul_zero,
      sub_zero, hη, zero_mul, he, sub_zero]

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def parametrix (α : ℝ) (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) :
    A.H (2 * (k : ℝ)) →L[ℝ] A.H (2 * ((k + 1 : ℕ) : ℝ)) :=
  ∑ i, A.patchParametrix α i (hα i)

lemma parametrix_equation (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (u : A.H (2 * (k : ℝ))) (x : M) :
    (α : ℂ) * A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.parametrix α hα u) x -
      complexLaplaceBeltrami g
        (A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.parametrix α hα u)) x =
      A.representative (2 * (k : ℝ)) u x -
        A.representative (2 * (k : ℝ)) (A.error B α hα u) x := by
  have hq : (A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.parametrix α hα u) : M → ℂ) =
      fun y => ∑ i, A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.patchParametrix α i (hα i) u) y := by
    funext y
    simp only [parametrix, sum_apply, map_sum, BoundedContinuousFunction.sum_apply]
  rw [hq, complexLaplaceBeltrami_sum _ _
    (fun i _ => A.representative_C2 (A.patchParametrix α i (hα i) u)),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [A.patchParametrix_equation α _ (B _) (hα _) u x]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, A.sum_η, one_mul]
  simp only [error, sum_apply, map_sum, BoundedContinuousFunction.sum_apply]

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def patchOutput (i : A.t) : FourierSobolevSpace E ℂ (2 * (k : ℝ) + 2) →L[ℝ]
    A.H (2 * ((k + 1 : ℕ) : ℝ)) :=
  A.lift (A.p i) (A.ψ i) (A.chart_ψ i) (A.smooth_ψ i) (k + 1) ∘L
    (sobolevAffineCutoff (A.χcoord i) (A.compact_χcoord i) (A.smooth_χcoord i)
      (-((A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) (A.p i)))
      (A.localInverse i).radius⁻¹ (k + 1)).restrictScalars ℝ

def parametrixBound : ℝ := ∑ i,
  ‖A.patchOutput i‖ * ((A.localInverse i).bound *
    ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖)

def resolvent (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) :
    A.H (2 * (k : ℝ)) →L[ℝ] A.H (2 * ((k + 1 : ℕ) : ℝ)) :=
  A.parametrix α hα ∘L neumannCorrectedInverse
    (ContinuousLinearMap.id ℝ (A.H (2 * (k : ℝ)))) (A.error B α hα) (A.error_lt_one B α hα he)

lemma resolvent_equation (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (u : A.H (2 * (k : ℝ))) (x : M) :
    (α : ℂ) * A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.resolvent B α hα he u) x -
      complexLaplaceBeltrami g
        (A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.resolvent B α hα he u)) x =
      A.representative (2 * (k : ℝ)) u x := by
  rw [resolvent, ContinuousLinearMap.comp_apply, A.parametrix_equation]
  have hn := neumannCorrectedInverse_fixed
    (ContinuousLinearMap.id ℝ (A.H (2 * (k : ℝ)))) (A.error B α hα)
    (A.error_lt_one B α hα he) u
  have hh := congrArg (fun v : A.H (2 * (k : ℝ)) => A.representative (2 * (k : ℝ)) v x) hn
  simp only [ContinuousLinearMap.id_apply, map_add, BoundedContinuousFunction.add_apply] at hh
  exact sub_eq_iff_eq_add.mpr hh

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

def smoothMulLinear : ManifoldSmoothFunctions E M →ₗ[ℝ]
    ManifoldSmoothFunctions E M →ₗ[ℝ] ManifoldSmoothFunctions E M where
  toFun f :=
    { toFun := smoothMul f
      map_add' := fun h j => by ext x; exact mul_add (f x) (h x) (j x)
      map_smul' := fun c h => by ext x; exact mul_smul_comm c (f x) (h x) }
  map_add' f h := by ext j x; exact add_mul (f x) (h x) (j x)
  map_smul' c f := by ext h x; exact smul_mul_assoc c (f x) (h x)

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma smooth_product_bound (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : ManifoldSmoothFunctions E M,
      ‖A.ofSmooth (2 * (l : ℝ)) (smoothMul f h)‖ ≤
        C * ‖A.ofSmooth (2 * (l : ℝ)) f‖ * ‖A.ofSmooth (2 * (l : ℝ)) h‖ := by
  let D : A.t → ℝ := fun i => ‖A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) l‖
  have hD : ∀ i, 0 ≤ D i := fun i =>
    (A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) l).opNorm_nonneg
  let C := sobolevAlgebraConstant (E := E) (2 * (l : ℝ)) * ∑ i, D i
  have hC : 0 ≤ C := mul_nonneg (sobolevAlgebraConstant_nonneg _) (Finset.sum_nonneg (fun i _ => hD i))
  refine ⟨C, hC, fun f h => ?_⟩
  change ‖(A.ofSmooth (2 * (l : ℝ)) (smoothMul f h)).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hC (norm_nonneg _)) (norm_nonneg _))).mpr
  intro i
  let F := chartSchwartzLinear (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _) (A.chart_η i) (A.smooth_η i) f
  let H := chartSchwartzLinear (A.p i) (A.χ i) (HasCompactSupport.of_compactSpace _) (A.chart_χ i) (A.smooth_χ i) h
  have he : chartSchwartzLinear (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _)
      (A.chart_η i) (A.smooth_η i) (smoothMul f h) = SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) F H := by
    ext y
    change chartLocalize (E := E) (A.p i) (A.η i) (smoothMul f h) y =
      chartLocalize (E := E) (A.p i) (A.η i) f y * chartLocalize (E := E) (A.p i) (A.χ i) h y
    by_cases hy : y ∈ (chartAt E (A.p i)).target
    · simp only [chartLocalize_eq _ _ _ hy]
      change A.η i ((chartAt E (A.p i)).symm y) *
        (f ((chartAt E (A.p i)).symm y) * h ((chartAt E (A.p i)).symm y)) = _
      by_cases hx : A.η i ((chartAt E (A.p i)).symm y) = 0
      · simp only [hx, zero_mul]
      · rw [(A.one_χ i).self_of_nhdsSet (subset_tsupport _ hx), Pi.one_apply, one_mul]
        ring
    · simp only [chartLocalize, hy, ↓reduceIte, zero_mul]
  change ‖schwartzToSobolev (2 * (l : ℝ))
    (chartSchwartzLinear (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _) (A.chart_η i) (A.smooth_η i) (smoothMul f h))‖ ≤ _
  rw [he]
  apply (schwartz_sobolev_product_bound ht F H).trans
  have hF : ‖schwartzToSobolev (2 * (l : ℝ)) F‖ ≤ ‖A.ofSmooth (2 * (l : ℝ)) f‖ :=
    norm_le_pi_norm (A.ofSmooth (2 * (l : ℝ)) f).val i
  have hH : ‖schwartzToSobolev (2 * (l : ℝ)) H‖ ≤ D i * ‖A.ofSmooth (2 * (l : ℝ)) h‖ := by
    have hh := (A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) l).le_opNorm
      (A.ofSmooth (2 * (l : ℝ)) h)
    rw [A.cutoffLocalization_smooth] at hh
    exact hh
  have ha := sobolevAlgebraConstant_nonneg (E := E) (2 * (l : ℝ))
  calc
    _ ≤ sobolevAlgebraConstant (E := E) (2 * (l : ℝ)) *
        ‖A.ofSmooth (2 * (l : ℝ)) f‖ * (D i * ‖A.ofSmooth (2 * (l : ℝ)) h‖) := by gcongr
    _ ≤ sobolevAlgebraConstant (E := E) (2 * (l : ℝ)) *
        ‖A.ofSmooth (2 * (l : ℝ)) f‖ * ((∑ j, D j) * ‖A.ofSmooth (2 * (l : ℝ)) h‖) := by
      gcongr
      exact Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i)
    _ = _ := by dsimp [C]; ring

attribute [local instance] OAI.YauCounterexamples.CompactMetricAtlas.H_smulCommClass
attribute [local instance] OAI.YauCounterexamples.CompactMetricAtlas.H_isScalarTower
def smoothProduct (l : ℕ) : ManifoldSmoothFunctions E M →ₗ[ℝ]
    ManifoldSmoothFunctions E M →ₗ[ℝ] A.H (2 * (l : ℝ)) :=
  smoothMulLinear.compr₂ (smoothToManifoldSobolev A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η
    (2 * (l : ℝ)))

def productConstant (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))) : ℝ :=
  (A.smooth_product_bound l ht).choose

omit [T2Space M] in
lemma productConstant_nonneg (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))) :
    0 ≤ A.productConstant l ht := (A.smooth_product_bound l ht).choose_spec.1

omit [T2Space M] in
lemma smoothProduct_bound (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (f h : ManifoldSmoothFunctions E M) :
    ‖A.smoothProduct l f h‖ ≤ A.productConstant l ht *
      ‖A.ofSmooth (2 * (l : ℝ)) f‖ * ‖A.ofSmooth (2 * (l : ℝ)) h‖ :=
  (A.smooth_product_bound l ht).choose_spec.2 f h

def product (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))) :
    A.H (2 * (l : ℝ)) →L[ℝ] A.H (2 * (l : ℝ)) →L[ℝ] A.H (2 * (l : ℝ)) :=
  bilinearExtension (A.smoothProduct l)
    (smoothToManifoldSobolev A.p A.η (fun i => HasCompactSupport.of_compactSpace (A.η i))
      A.chart_η A.smooth_η (2 * (l : ℝ)))
    (denseRange_smoothToManifoldSobolev A.p A.η
      (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η _)
    (A.productConstant l ht) (A.smoothProduct_bound l ht)

omit [T2Space M] in
lemma product_smooth (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (f h : ManifoldSmoothFunctions E M) :
    A.product l ht (A.ofSmooth (2 * (l : ℝ)) f) (A.ofSmooth (2 * (l : ℝ)) h) =
      A.ofSmooth (2 * (l : ℝ)) (smoothMul f h) :=
  bilinearExtension_apply _ _ _ _ _ (A.productConstant_nonneg l ht) f h

omit [T2Space M] in
lemma product_representative (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (f h : A.H (2 * (l : ℝ))) (x : M) :
    A.representative (2 * (l : ℝ)) (A.product l ht f h) x =
      A.representative (2 * (l : ℝ)) f x * A.representative (2 * (l : ℝ)) h x := by
  have hd := denseRange_smoothToManifoldSobolev A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η (2 * (l : ℝ))
  refine hd.induction_on f ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · intro u
    refine hd.induction_on h ?_ ?_
    · apply isClosed_eq <;> fun_prop
    · intro v
      change A.representative (2 * (l : ℝ))
        (A.product l ht (A.ofSmooth (2 * (l : ℝ)) u) (A.ofSmooth (2 * (l : ℝ)) v)) x = _
      rw [A.product_smooth l ht]
      rw [A.ofSmooth_representative _ ht]
      change smoothMul u v x = A.representative (2 * (l : ℝ)) (A.ofSmooth (2 * (l : ℝ)) u) x *
        A.representative (2 * (l : ℝ)) (A.ofSmooth (2 * (l : ℝ)) v) x
      rw [A.ofSmooth_representative _ ht, A.ofSmooth_representative _ ht]
      rfl

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma laplacianPatch_representative (i : A.t) (B : A.PatchCoefficients i)
    (u : A.H (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.representative (2 * (k : ℝ))
      (A.laplacianPatch i B (A.cutoffLocalization (A.p i) (A.χ i)
        (A.chart_χ i) (A.smooth_χ i) (k + 1) u)) x =
      A.η i x * complexLaplaceBeltrami g (A.representative (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  have ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)) := by push_cast; linarith
  have ht' : Module.finrank ℝ E < 2 * (2 * (k : ℝ) + 2) := by linarith
  let w := A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) (k + 1) u
  let v : M → ℂ := A.representative (2 * ((k + 1 : ℕ) : ℝ)) u
  change A.representative _ (A.lift (A.p i) (A.η i) (A.chart_η i) (A.smooth_η i) k _) x = _
  rw [A.lift_representative _ _ _ _ k hs]
  by_cases hx : A.η i x = 0
  · simp only [hx, zero_mul]
  have hxs := A.chart_η i (subset_tsupport _ hx)
  have hys := (chartAt E (A.p i)).map_source hxs
  change A.η i x * sobolevRepresentative hs
    (coefficientPerturbation (Module.finBasis ℝ E) hs _ _ w) ((chartAt E (A.p i)) x) = _
  congr 1
  rw [coefficientPerturbation_representative (Module.finBasis ℝ E) hs ht']
  have hχ : A.χ i =ᶠ[𝓝 x] 1 := (A.one_χ i).filter_mono
    (nhds_le_nhdsSet (subset_tsupport _ hx))
  have hχx : A.χcoord i ((chartAt E (A.p i)) x) = 1 := by
    rw [χcoord, chartLocalize_eq _ _ _ hys, (chartAt E (A.p i)).left_inv hxs,
      Pi.one_apply, mul_one]
    exact hχ.eq_of_nhds
  have hc : (chartAt E (A.p i)) x ∈ tsupport (A.χcoord i) :=
    subset_tsupport _ (by change A.χcoord i ((chartAt E (A.p i)) x) ≠ 0; rw [hχx]; exact one_ne_zero)
  have hw : (sobolevRepresentative ht' w : E → ℂ) = chartLocalize (E := E) (A.p i) (A.χ i) v := by
    funext y
    rw [sobolevRepresentative_congr _ _ (by push_cast; ring) ht' ht]
    exact A.cutoffLocalization_representative _ _ _ _ (k + 1) ht u y
  simp only [sobolevRepresentative_schwartz, SchwartzMap.toBoundedContinuousFunction_apply]
  change (∑ j, ∑ l, (A.χcoord i ((chartAt E (A.p i)) x) *
      (B.a j l ((chartAt E (A.p i)) x) : ℂ)) * _) + ∑ j,
      (A.χcoord i ((chartAt E (A.p i)) x) * (B.c j ((chartAt E (A.p i)) x) : ℂ)) * _ = _
  simp only [hχx, one_mul, B.eq_a _ hc, B.eq_c _ hc]
  change euclideanElliptic (Module.finBasis ℝ E)
    (fun j l y => (metricCoefficients g (A.p i) y)⁻¹ j l)
    (metricFirstCoefficient g (A.p i)) (sobolevRepresentative ht' w) ((chartAt E (A.p i)) x) = _
  rw [hw, complexLaplaceBeltrami_inChart (A.representative_C2 u) g (A.p i) hxs]
  exact euclideanElliptic_congr _ _ _ (chartLocalize_eventually_eq _ _ _ hxs hχ)

omit [T2Space M] in
lemma laplacianCLM_representative (B : ∀ i, A.PatchCoefficients i)
    (u : A.H (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.representative (2 * (k : ℝ)) (A.laplacianCLM B u) x =
      complexLaplaceBeltrami g (A.representative (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  simp only [laplacianCLM, sum_apply, map_sum, BoundedContinuousFunction.sum_apply,
    ContinuousLinearMap.comp_apply, A.laplacianPatch_representative]
  rw [← Finset.sum_mul, A.sum_η, one_mul]

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

local instance realH_smulCommClass (s : ℝ) : SMulCommClass ℝ ℝ (A.realH s) :=
  ⟨fun a b c => by simp only [smul_smul, mul_comm]⟩

def realInclusion : A.realH (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.realH (2 * (k : ℝ)) :=
  A.inclusion.restrict fun u hu x => by rw [A.inclusion_representative]; exact hu x

omit [T2Space M] in
lemma product_mem_realH (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (u v : A.realH (2 * (l : ℝ))) : A.product l ht u v ∈ A.realH (2 * (l : ℝ)) := by
  intro x
  rw [A.product_representative l ht]
  simp only [Complex.mul_im, u.property x, v.property x, mul_zero, zero_mul, add_zero]

local instance realH_isScalarTower_r1b8d0d_1 (s : ℝ) : IsScalarTower ℝ ℝ (A.realH s) :=
  ⟨fun a b c => mul_smul a b c⟩
local instance H_real_smulCommClass_r1b8d0d_1 (s : ℝ) : SMulCommClass ℝ ℝ (A.H s) :=
  ⟨fun a b c => by simp only [smul_smul, mul_comm]⟩
local instance H_real_isScalarTower_r1b8d0d_1 (s : ℝ) : IsScalarTower ℝ ℝ (A.H s) :=
  ⟨fun a b c => mul_smul a b c⟩
def realProduct (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))) :
    A.realH (2 * (l : ℝ)) →L[ℝ] A.realH (2 * (l : ℝ)) →L[ℝ] A.realH (2 * (l : ℝ)) :=
  restrictBilinear (A.product l ht) (A.realH (2 * (l : ℝ))) (A.product_mem_realH l ht)

omit [T2Space M] in
lemma laplacian_mem_realH (B : ∀ i, A.PatchCoefficients i)
    (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) : A.laplacianCLM B u ∈ A.realH (2 * (k : ℝ)) := by
  intro x
  rw [A.laplacianCLM_representative]
  change laplaceBeltrami g (Complex.im ∘ A.representative (2 * ((k + 1 : ℕ) : ℝ)) u) x = 0
  have he : (Complex.im ∘ A.representative (2 * ((k + 1 : ℕ) : ℝ)) u) = fun _ => 0 :=
    funext u.property
  rw [he, laplaceBeltrami_zero]

def realLaplacian (B : ∀ i, A.PatchCoefficients i) :
    A.realH (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.realH (2 * (k : ℝ)) :=
  A.laplacianCLM B |>.restrict fun u hu => A.laplacian_mem_realH B ⟨u, hu⟩

lemma resolvent_mem_realH (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (u : A.realH (2 * (k : ℝ))) :
    A.resolvent B α hα he u ∈ A.realH (2 * ((k + 1 : ℕ) : ℝ)) := by
  let v := A.resolvent B α hα he u
  have hv := A.representative_C2 v
  have him : (Complex.im ∘ A.representative (2 * ((k + 1 : ℕ) : ℝ)) v : M → ℝ) = 0 := by
    apply positive_shift_kernel_eq_zero_C2 g hα0 (Complex.imCLM.contMDiff.comp hv)
    intro x
    change α * (A.representative (2 * ((k + 1 : ℕ) : ℝ)) v x).im -
      laplaceBeltrami g (Complex.im ∘ A.representative (2 * ((k + 1 : ℕ) : ℝ)) v) x = 0
    have h := congrArg Complex.im (A.resolvent_equation B α hα he u x)
    simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, u.property x, complexLaplaceBeltrami, Complex.add_im,
      Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, zero_add, Function.comp_apply] using h
  exact fun x => congrFun him x

def realResolvent (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) (he : A.errorBound B α ≤ 1 / 2) :
    A.realH (2 * (k : ℝ)) →L[ℝ] A.realH (2 * ((k + 1 : ℕ) : ℝ)) :=
  (A.resolvent B α hα he).restrict fun u hu => A.resolvent_mem_realH B α hα0 hα he ⟨u, hu⟩

end CompactMetricAtlas

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma realValue_add (s : ℝ) (u v : A.realH s) (x : M) :
    A.realValue s (u + v) x = A.realValue s u x + A.realValue s v x := by
  simp [realValue]

local instance realH_isScalarTower'_r1b8d0d_1 (s : ℝ) : IsScalarTower ℝ ℝ (A.realH s) :=
  ⟨fun a b c => mul_smul a b c⟩
omit [T2Space M] in
lemma realValue_smul (s : ℝ) (c : ℝ) (u : A.realH s) (x : M) :
    A.realValue s (c • u) x = c * A.realValue s u x := by
  simp [realValue]

def realDivergence (B : ∀ i, A.PatchCoefficients i)
    (b : A.realH (2 * ((k + 1 : ℕ) : ℝ))) :
    A.realH (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.realH (2 * (k : ℝ)) :=
  boundedDivergence (A.realProduct (k + 1) (by push_cast; linarith))
    (A.realProduct k hs) A.realInclusion (A.realLaplacian B) b

def realOfSmooth (s : ℝ) (ht : Module.finrank ℝ E < 2 * s)
    (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) : A.realH s :=
  ⟨A.ofSmooth s ⟨fun x => (f x : ℂ), Complex.ofRealCLM.contMDiff.comp hf⟩,
    fun x => by erw [congrFun (A.ofSmooth_representative s ht _) x]; rfl⟩

end CompactMetricAtlas

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

def localizedRealValue (i : A.t) (v : A.realH A.highIndex) (y : E) : ℝ :=
  (sobolevRepresentative A.highIndex_bound (A.cutoffLocalization (A.p i) (A.χ i)
    (A.chart_χ i) (A.smooth_χ i) (k+1) v) y).re

def localizedFirstJet (i : A.t) (v : A.realH A.highIndex) (y : E) : ℝ × (E →L[ℝ] ℝ) :=
  (A.localizedRealValue i v y,fderiv ℝ (A.localizedRealValue i v) y)

end CompactMetricAtlas

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_VaryingPatchCoefficients
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
namespace YauCounterexamples
open Set Filter Function
open scoped ContDiff Topology Manifold BoundedContinuousFunction SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

variable (q : SmoothMetric E M)

def varyingLaplacianPatch (i : A.t) (B : A.VaryingPatchCoefficients q i) :
    FourierSobolevSpace E ℂ (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  A.lift (A.p i) (A.η i) (A.chart_η i) (A.smooth_η i) k ∘L
    (coefficientPerturbation (Module.finBasis ℝ E) hs
      (fun j l => schwartzToSobolev (2 * (k : ℝ))
        (A.metricCoefficientSchwartz i (B.a j l) (B.smooth_a j l)))
      (fun j => schwartzToSobolev (2 * (k : ℝ))
        (A.metricCoefficientSchwartz i (B.c j) (B.smooth_c j)))).restrictScalars ℝ

def varyingLaplacianCLM (B : ∀ i, A.VaryingPatchCoefficients q i) :
    A.H (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  ∑ i, A.varyingLaplacianPatch q i (B i) ∘L
    A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) (k + 1)

omit [T2Space M] in
lemma varyingLaplacianPatch_representative (i : A.t) (B : A.VaryingPatchCoefficients q i)
    (u : A.H (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.representative (2 * (k : ℝ))
      (A.varyingLaplacianPatch q i B (A.cutoffLocalization (A.p i) (A.χ i)
        (A.chart_χ i) (A.smooth_χ i) (k + 1) u)) x =
      A.η i x * complexLaplaceBeltrami q (A.representative (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  have ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)) := by push_cast; linarith
  have ht' : Module.finrank ℝ E < 2 * (2 * (k : ℝ) + 2) := by linarith
  let w := A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) (k + 1) u
  let v : M → ℂ := A.representative (2 * ((k + 1 : ℕ) : ℝ)) u
  change A.representative _ (A.lift (A.p i) (A.η i) (A.chart_η i) (A.smooth_η i) k _) x = _
  rw [A.lift_representative _ _ _ _ k hs]
  by_cases hx : A.η i x = 0
  · simp only [hx, zero_mul]
  have hxs := A.chart_η i (subset_tsupport _ hx)
  have hys := (chartAt E (A.p i)).map_source hxs
  change A.η i x * sobolevRepresentative hs
    (coefficientPerturbation (Module.finBasis ℝ E) hs _ _ w) ((chartAt E (A.p i)) x) = _
  congr 1
  rw [coefficientPerturbation_representative (Module.finBasis ℝ E) hs ht']
  have hχ : A.χ i =ᶠ[𝓝 x] 1 := (A.one_χ i).filter_mono
    (nhds_le_nhdsSet (subset_tsupport _ hx))
  have hχx : A.χcoord i ((chartAt E (A.p i)) x) = 1 := by
    rw [χcoord, chartLocalize_eq _ _ _ hys, (chartAt E (A.p i)).left_inv hxs,
      Pi.one_apply, mul_one]
    exact hχ.eq_of_nhds
  have hc : (chartAt E (A.p i)) x ∈ tsupport (A.χcoord i) :=
    subset_tsupport _ (by change A.χcoord i ((chartAt E (A.p i)) x) ≠ 0; rw [hχx]; exact one_ne_zero)
  have hw : (sobolevRepresentative ht' w : E → ℂ) = chartLocalize (E := E) (A.p i) (A.χ i) v := by
    funext y
    rw [sobolevRepresentative_congr _ _ (by push_cast; ring) ht' ht]
    exact A.cutoffLocalization_representative _ _ _ _ (k + 1) ht u y
  simp only [sobolevRepresentative_schwartz, SchwartzMap.toBoundedContinuousFunction_apply]
  change (∑ j, ∑ l, (A.χcoord i ((chartAt E (A.p i)) x) *
      (B.a j l ((chartAt E (A.p i)) x) : ℂ)) * _) + ∑ j,
      (A.χcoord i ((chartAt E (A.p i)) x) * (B.c j ((chartAt E (A.p i)) x) : ℂ)) * _ = _
  simp only [hχx, one_mul, B.eq_a _ hc, B.eq_c _ hc]
  change euclideanElliptic (Module.finBasis ℝ E)
    (fun j l y => (metricCoefficients q (A.p i) y)⁻¹ j l)
    (metricFirstCoefficient q (A.p i)) (sobolevRepresentative ht' w) ((chartAt E (A.p i)) x) = _
  rw [hw, complexLaplaceBeltrami_inChart (A.representative_C2 u) q (A.p i) hxs]
  exact euclideanElliptic_congr _ _ _ (chartLocalize_eventually_eq _ _ _ hxs hχ)

omit [T2Space M] in
lemma varyingLaplacianCLM_representative (B : ∀ i, A.VaryingPatchCoefficients q i)
    (u : A.H (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.representative (2 * (k : ℝ)) (A.varyingLaplacianCLM q B u) x =
      complexLaplaceBeltrami q (A.representative (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  simp only [varyingLaplacianCLM, sum_apply, map_sum, BoundedContinuousFunction.sum_apply,
    ContinuousLinearMap.comp_apply, A.varyingLaplacianPatch_representative]
  rw [← Finset.sum_mul, A.sum_η, one_mul]

end CompactMetricAtlas
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_CoefficientPerturbationTendsto
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Function
open scoped Topology
open Set Filter Function
open scoped ContDiff Topology Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs) (q : SmoothMetric E M)

omit [T2Space M] in
lemma varyingLaplacian_mem_realH (B : ∀ i, A.VaryingPatchCoefficients q i)
    (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) :
    A.varyingLaplacianCLM q B u ∈ A.realH (2 * (k : ℝ)) := by
  intro x
  rw [A.varyingLaplacianCLM_representative]
  change laplaceBeltrami q (Complex.im ∘ A.representative (2 * ((k + 1 : ℕ) : ℝ)) u) x = 0
  have he : (Complex.im ∘ A.representative (2 * ((k + 1 : ℕ) : ℝ)) u : M → ℝ) = fun _ => 0 :=
    funext u.property
  rw [he, laplaceBeltrami_zero]

def varyingRealLaplacian (B : ∀ i, A.VaryingPatchCoefficients q i) :
    A.realH (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.realH (2 * (k : ℝ)) :=
  A.varyingLaplacianCLM q B |>.restrict fun u hu => A.varyingLaplacian_mem_realH q B ⟨u,hu⟩

def varyingShift (B : ∀ i, A.VaryingPatchCoefficients q i) (α : ℝ) :
    A.realH (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.realH (2 * (k : ℝ)) :=
  α • A.realInclusion - A.varyingRealLaplacian q B

end CompactMetricAtlas

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff Manifold BoundedContinuousFunction SchwartzMap


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_TransferAcross
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def power (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (u : A.H (2 * (l : ℝ))) : ℕ → A.H (2 * (l : ℝ))
  := Nat.rec (A.ofSmooth (2 * (l : ℝ)) ⟨fun _ => 1, contMDiff_const⟩)
    (fun _ v => A.product l ht u v)

def polynomial {N : ℕ} (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (a : Fin N → ManifoldSmoothFunctions E M) (u : A.H (2 * (l : ℝ))) : A.H (2 * (l : ℝ)) :=
  ∑ i, A.product l ht (A.ofSmooth (2 * (l : ℝ)) (a i)) (A.power l ht u i.val)

end CompactMetricAtlas
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_GlobalPrepDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def actualProfileSpeed (g : SmoothMetric E E) (u : E → ℝ) (x : E) : ℝ :=
  actualCoordinateNorm g x (coordinateMetricGradient g u x)

end
end YauCounterexamples

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
attribute [local instance] OAI.YauCounterexamples.tensorFormSpace
attribute [local instance] OAI.YauCounterexamples.tensorTangentDualAdd
attribute [local instance] OAI.YauCounterexamples.tensorTangentDualSmul
local instance tensorTangentFormAdd_r1b8d0d_1 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) :=
  inferInstance
local instance tensorTangentFormSmul_r1b8d0d_1 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance
instance chartFormTrivialization_mem (p : M) :
    MemTrivializationAtlas (chartFormTrivialization (E:=E) p) := inferInstanceAs
      (MemTrivializationAtlas (trivializationAt (MetricForm E) (TangentForm (E:=E)) p))

end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_FixedRadialChoice
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff

theorem fixedRadialChoice_nonempty : Nonempty FixedRadialChoice := by
  obtain ⟨β,hβ,hβc,hβs,hβv,hmid⟩ := exists_radial_derivative
    (show (1:ℝ)/1024 < 1/256 by norm_num)
  have hz₀ : β 0 = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h
    have hh := (hβs h).1
    norm_num at hh)
  have hz : ∀ t, (1:ℝ)/256 ≤ t → β t = 0 := by
    intro t ht
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact (not_lt_of_ge ht) (hβs h).2
  obtain ⟨Fmax,S,K,hM,hS,hK,hcoef⟩ := periodicRadial_coefficients_bounded hβ hβc hβv
    (show (0:ℝ) < 1/4 by norm_num)
  obtain ⟨q,ρ,c,hρ,hρ1,hc,hw⟩ := exists_radial_phase_window hβ
    (show (0:ℝ) < 1/1024 by norm_num) (show (1:ℝ)/1024 < 1/256 by norm_num)
    (show (1:ℝ)/256 < (1/4)^2 by norm_num) (show (0:ℝ) < 1/4 by norm_num)
    (show 2*(1/4:ℝ) < 1 by norm_num) hmid
  obtain ⟨δ,g₀,hδ,hg,hg1,hs,he⟩ := exists_fixed_radial_constants K S c hc
  exact ⟨⟨β,hβ,hz₀,hβv,hz,Fmax,S,K,hM,hS,hK,hcoef,q,ρ,c,δ,g₀,hρ,hρ1,hc,hδ,hg,hg1,he,hs,hw⟩⟩

noncomputable def fixedRadialChoice : FixedRadialChoice := Classical.choice fixedRadialChoice_nonempty

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SpectralResolvent
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def spectralResolvent (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) : A.H (2 * (k : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  manifoldSobolevInclusion A.p A.η (fun i => HasCompactSupport.of_compactSpace (A.η i))
    A.chart_η A.smooth_η (2 * ((k + 1 : ℕ) : ℝ)) (2 * (k : ℝ)) ∘L A.resolvent B α hα he

end CompactMetricAtlas
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ContinuousEigenpairLinearization
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def realSpectralResolvent (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) : A.realH (2 * (k : ℝ)) →L[ℝ] A.realH (2 * (k : ℝ)) :=
  A.realInclusion ∘L A.realResolvent B α hα0 hα he

end CompactMetricAtlas

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace MetricIntegralAtlas
variable (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)
omit [T2Space M] in
lemma mean_const_mul (c : ℝ) (f : M → ℝ) (hf : Continuous f) :
    I.mean g (fun x => c * f x) = c * I.mean g f := by
  let F := BoundedContinuousFunction.mkOfCompact ⟨f,hf⟩
  change I.integralCLM g (c • F) = c • I.integralCLM g F
  exact map_smul _ _ _
end MetricIntegralAtlas

end

open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology


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
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
open Set Filter Function
open scoped ContDiff Topology Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def varyingResolvent (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (q : SmoothMetric E M)
    (C : ∀ i, A.VaryingPatchCoefficients q i) :
    A.realH (2 * (k : ℝ)) →L[ℝ] A.realH (2 * ((k + 1 : ℕ) : ℝ)) :=
  preconditionedInverse (A.realResolvent B α hα0 hα he) (A.varyingShift q C α)

def varyingSpectralResolvent (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (q : SmoothMetric E M)
    (C : ∀ i, A.VaryingPatchCoefficients q i) :
    A.realH (2 * (k : ℝ)) →L[ℝ] A.realH (2 * (k : ℝ)) :=
  A.realInclusion ∘L A.varyingResolvent B α hα0 hα he q C

end CompactMetricAtlas

end


section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

def realSmoothRepresentativeLM (s : ℝ) (P : Submodule ℝ (A.realH s))
    (hf : ∀ w : P, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue s w)) :
    P →ₗ[ℝ] RealSmoothFunctions E M where
  toFun w := ⟨A.realValue s w,hf w⟩
  map_add' a b := by
    ext x
    exact A.realValue_add s a b x
  map_smul' r a := by
    ext x
    exact A.realValue_smul s r a x

end CompactMetricAtlas
end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RealValueCubic
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
namespace YauCounterexamples
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)
local instance realH_smulCommClass_pf (s : ℝ) : SMulCommClass ℝ ℝ (A.realH s) :=
  ⟨fun a b c => by simp only [smul_smul, mul_comm]⟩

end CompactMetricAtlas
end YauCounterexamples

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

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_ActualProfileSpeedNonneg
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace YauCounterexamples
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def actualProfileMass (g : SmoothMetric E E) (u : E → ℝ) (μ : Measure E) (Ω : Set E) : ℝ :=
  ∫ x in Ω, actualProfileSpeed g u x ∂μ

def actualProfileWeightedMeasure (g : SmoothMetric E E) (u : E → ℝ) (μ : Measure E) (Ω : Set E) : Measure E :=
  (μ.restrict Ω).withDensity (fun x => ENNReal.ofReal (actualProfileSpeed g u x))

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ActualProfileCycleGain
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set MeasureTheory Filter
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

def actualProfileCycleGain : ℝ := fixedRadialChoice.fraction*fixedRadialChoice.g₀/768



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_RestrictedPinningPencil
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
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace MetricIntegralAtlas
variable (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)
omit [T2Space M] in
lemma mean_add (f h : M → ℝ) (hf : Continuous f) (hh : Continuous h) :
    I.mean g (fun x => f x+h x) = I.mean g f+I.mean g h := by
  let F := BoundedContinuousFunction.mkOfCompact ⟨f,hf⟩
  let H := BoundedContinuousFunction.mkOfCompact ⟨h,hh⟩
  change I.integralCLM g (F+H) = I.integralCLM g F+I.integralCLM g H
  exact map_add _ _ _
end MetricIntegralAtlas
end


open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end


