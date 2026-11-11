-- Prove2me | Definitions.Def_Q243FI005
-- name    : Q243FI005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T01:42:31.932214+00:00
-- url     : https://prove2.me/theorems/be910ff8-d1c4-4adc-8be3-f86712343824
-- title:
--   Definitions bundle Q243FI005 of the split of OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 107 declarations of OpenAI's Lean: 51 definitions, 1 inductive type or structure, 3 instances and 52 theorems. The definitions and types are `OAI.Problem367.IsingContinuousCopyCoefficients.response`, `OAI.Problem367.IsingContinuousCopyDensity.continuousDensity`, `OAI.Problem367.IsingContinuousCopyDensity.response`, `OAI.Problem367.IsingCopyPathBounds.edgeLogDifference`, `OAI.Problem367.IsingCopyPathBounds.pathLogDifference`, `OAI.Problem367.IsingCopySpectral.averageOnDifferences`, `OAI.Problem367.IsingCopySpectral.cavityLogEdgeVector`, `OAI.Problem367.IsingCopySpectral.cavityLogVector`, `OAI.Problem367.IsingCopySpectral.differenceReflection`, `OAI.Problem367.IsingCopySpectral.differenceSpace`, `OAI.Problem367.IsingCopySpectral.observableDifference`, `OAI.Problem367.IsingCopySquareDensity.drift`, `OAI.Problem367.IsingCopySquareDensity.noise`, `OAI.Problem367.IsingCopyStationarity.sitePair`, `OAI.Problem367.IsingInnovation.uniformObservationFiltration`, `OAI.Problem367.IsingJoinedResponseIntegrals.IntegralSystem`, `OAI.Problem367.IsingObservationFactor.canonicalClippedWeight`, `OAI.Problem367.IsingObservationFactor.canonicalCovarianceCompensator`, `OAI.Problem367.IsingObservationFactor.canonicalCovarianceEnergy`, `OAI.Problem367.IsingObservationFactor.canonicalPosteriorExit`, `OAI.Problem367.IsingObservationFactor.canonicalResponseDrift`, `OAI.Problem367.IsingObservationFactor.commonPosteriorExit`, `OAI.Problem367.IsingObservationFactor.commonResponseCompensator`, `OAI.Problem367.IsingObservationFactor.continuousDifference`, `OAI.Problem367.IsingObservationFactor.continuousField`, `OAI.Problem367.IsingObservationFactor.continuousPosterior`, `OAI.Problem367.IsingObservationFactor.continuousRootCovariance`, `OAI.Problem367.IsingObservationFactor.continuousRootResponse`, `OAI.Problem367.IsingObservationFactor.copyContinuousField`, `OAI.Problem367.IsingObservationFactor.copyContinuousPosterior`, `OAI.Problem367.IsingObservationFactor.copyResponseDriftDifference`, `OAI.Problem367.IsingObservationFactor.copyResponseEnergy`, `OAI.Problem367.IsingObservationFactor.copyResponseNoiseEnergy`, `OAI.Problem367.IsingObservationFactor.siteRootResponse`, `OAI.Problem367.IsingOrientedPath.logSum`, `OAI.Problem367.IsingOrientedPath.terminalAttenuation`, `OAI.Problem367.IsingOrientedPath.weightedLogEnergy`, `OAI.Problem367.IsingRootGaussianCut.terminalAttenuation`, `OAI.Problem367.IsingRootGaussianCut.terminalExtensionAverage`, `OAI.Problem367.NormalizedInfiniteTimeEnergy.finiteRow` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `FreeIsing_Brownian_ArrayLaw`, `FreeIsing_Brownian_EntropyEnergy`, `FreeIsing_Energy_NormalizedInfiniteTimeEnergy`, `FreeIsing_Estimates_FiniteGibbsField`, `FreeIsing_Estimates_PairedFiniteField`, `FreeIsing_Gibbs_CovarianceCompensator`, `FreeIsing_Ising_CanonicalArtanh`, `FreeIsing_Ising_CanonicalClippedWeight`, `FreeIsing_Ising_CanonicalContinuousFields`, `FreeIsing_Ising_CanonicalMartingales`, `FreeIsing_Ising_CanonicalPosteriorStops`, `FreeIsing_Ising_CommonStopBounds`, `FreeIsing_Ising_ConditionalCopyBounds`, `FreeIsing_Ising_ContinuousCopyCoefficients`, `FreeIsing_Ising_ContinuousCopyDensity`, `FreeIsing_Ising_ContinuousRootResponse`, `FreeIsing_Ising_CopyEdgeCorrelations`, `FreeIsing_Ising_CopyGeodesicCorrelations`, `FreeIsing_Ising_CopyObservables`, `FreeIsing_Ising_CopyPathBounds`, `FreeIsing_Ising_CopySpectral`, `FreeIsing_Ising_CopySquareDensity`, `FreeIsing_Ising_CopyStationarity`, `FreeIsing_Ising_Innovation`, `FreeIsing_Ising_InnovationIndependence`, `FreeIsing_Ising_InnovationLaw`, `FreeIsing_Ising_JoinedResponseIntegrals`, `FreeIsing_Ising_ObservationFactor`, `FreeIsing_Ising_ObservationInnovation`, `FreeIsing_Ising_ObservationLaw`, `FreeIsing_Ising_OrientedGaussianTail`, `FreeIsing_Ising_OrientedNoiseSplit`, `FreeIsing_Ising_OrientedPath`, `FreeIsing_Ising_RootGaussianCut`, `FreeIsing_Ising_StoppedSquareAssembly`, `FreeIsing_Posterior_FieldMoments`, `FreeIsing_Posterior_InfinitePosteriorField`, `FreeIsing_Posterior_PlantedBridgeInfinite`, `FreeIsing_Posterior_PlantedStationarity`, `FreeIsing_Posterior_PlantedSufficiencyVector`, `FreeIsing_Posterior_ProgressiveIsingPosterior`, `FreeIsing_Posterior_Symmetry`, `FreeIsing_Stochastic_WienerSampler`, `FreeIsing_Trees_BroadcastOutsideCone`, `FreeIsing_Trees_CanonicalPathResponse`, `FreeIsing_Trees_ConnectedExhaustion`, `FreeIsing_Trees_CoordinateResponse`, `FreeIsing_Trees_GibbsField`, `FreeIsing_Trees_InnovationPathMap`, `FreeIsing_Trees_LawSpectral`.
--
--   **Imports.** It imports the published bundle `Def_FreeIsing`; the bundles `Q243FI003` and `Q243FI004` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Problem367.HasFreeIsingLaw.finiteGibbsCovarianceCompensator_tendsto_L1`, `OAI.Problem367.IsingContinuousCopyCoefficients.response_continuous_ae`, `OAI.Problem367.IsingContinuousCopyCoefficients.response_eq_raw_ae`, `OAI.Problem367.IsingContinuousCopyCoefficients.response_row_energy`, `OAI.Problem367.IsingCopySpectral.forwardOperator_pow_bound`, `OAI.Problem367.IsingCopySpectral.norm_cavityLogDifference_sq_le`, `OAI.Problem367.IsingCopySquareDensity.integral_integral_stopped_noise_add_drift_eq_actual`, `OAI.Problem367.IsingJoinedResponseIntegrals.exists_integrals`, `OAI.Problem367.IsingObservationFactor.actual_variance_analysis_of_common_local_square`, `OAI.Problem367.IsingObservationFactor.ae_horizon_stopped_continuousDifference_bound`, `OAI.Problem367.IsingObservationFactor.canonicalCovarianceEnergy_integrable`, `OAI.Problem367.IsingObservationFactor.canonicalPosteriorExit_localizing`, `OAI.Problem367.IsingObservationFactor.canonicalResponseDrift_primitive_continuous`, `OAI.Problem367.IsingObservationFactor.canonical_artanh_decomposition`, `OAI.Problem367.IsingObservationFactor.canonical_compensatedSquare_martingale`, `OAI.Problem367.IsingObservationFactor.canonical_field_eq_normalized_integral`, `OAI.Problem367.IsingObservationFactor.canonical_stopped_field_eq_of_integral_limits`, `OAI.Problem367.IsingObservationFactor.continuousPosterior_initial_zero`, `OAI.Problem367.IsingObservationFactor.continuousRootCovariance_uniformObservation_eq_covariance_ae`, `OAI.Problem367.IsingObservationFactor.continuousRootResponse_hasSum_timeEnergy`, `OAI.Problem367.IsingObservationFactor.continuousRootResponse_row_eq_ae`, `OAI.Problem367.IsingObservationFactor.copied_difference_decomposition`, `OAI.Problem367.IsingObservationFactor.exists_canonical_root_covariance_integral_representation`, `OAI.Problem367.IsingObservationFactor.isLocalizingSequence_commonPosteriorExit` and `OAI.Problem367.IsingObservationFactor.variance_analysis_of_joined_decomposition`; the proofs of `OAI.Problem367.FiniteIsingFiltering.exists_innovation_integral_representation`, `OAI.Problem367.FiniteIsingFiltering.mean_compensatedSquare_martingale`, `OAI.Problem367.FiniteIsingFiltering.tendsto_cross_uniformSum`, `OAI.Problem367.HasFreeIsingLaw.finiteGibbsCovarianceCompensator_tendsto_L1`, `OAI.Problem367.HasFreeIsingLaw.finiteGibbsCovariance_windowEnergy_eq`, `OAI.Problem367.HasFreeIsingLaw.gaussianComponentField_critical_base_moments`, `OAI.Problem367.HasFreeIsingLaw.gaussian_component_field_recursion`, `OAI.Problem367.HasFreeIsingLaw.gaussian_root_information_le_component`, `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq`, `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsCovariance_windowEnergy_eq`, `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_tendsto_zero`, `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_zero`, `OAI.Problem367.IsingContinuousCopyCoefficients.response_continuous_ae`, `OAI.Problem367.IsingContinuousCopyCoefficients.response_eq_raw_ae`, `OAI.Problem367.IsingContinuousCopyCoefficients.response_row_energy`, `OAI.Problem367.IsingCopyEnergy.copy_row_energy_integrable`, `OAI.Problem367.IsingCopyResponseRowPaths.copies_rows_summable_ae`, `OAI.Problem367.IsingCopyResponseRowPaths.critical_root_variance_zero_of_noise_bound`, `OAI.Problem367.IsingCopyResponseRowPaths.exists_actual_spatial_endpoint_constant`, `OAI.Problem367.IsingCopyResponseRowPaths.exists_noise_energy_long_constants`, `OAI.Problem367.IsingCopyResponseRowPaths.integral_actual_density_le_path_sums`, `OAI.Problem367.IsingCopySpectral.forwardOperator_pow_bound`, `OAI.Problem367.IsingCopySpectral.norm_cavityLogDifference_sq_le`, `OAI.Problem367.IsingCopySquareDensity.integral_integral_stopped_noise_add_drift_eq_actual`, `OAI.Problem367.IsingCriticalSmallLogLoss.exists_critical_small_log_bounds`, `OAI.Problem367.IsingInnovation.exists_continuous_covariance_integral`, `OAI.Problem367.IsingInnovation.exists_continuous_posterior`, `OAI.Problem367.IsingInnovation.exists_posterior_integral_representation`, `OAI.Problem367.IsingInnovation.finiteCovariance_fullTime_interval_energy_cauchy`, `OAI.Problem367.IsingInnovation.tendsto_trial_cross_uniformSum`, `OAI.Problem367.IsingJoinedResponseIntegrals.exists_integrals`, `OAI.Problem367.IsingObservationFactor.actual_variance_analysis`, `OAI.Problem367.IsingObservationFactor.actual_variance_analysis_of_common_local_square`, `OAI.Problem367.IsingObservationFactor.ae_horizon_stopped_continuousDifference_bound`, `OAI.Problem367.IsingObservationFactor.canonicalCovarianceEnergy_integrable`, `OAI.Problem367.IsingObservationFactor.canonicalPosteriorExit_localizing`, `OAI.Problem367.IsingObservationFactor.canonicalResponseDrift_primitive_continuous`, `OAI.Problem367.IsingObservationFactor.canonical_artanh_decomposition`, `OAI.Problem367.IsingObservationFactor.canonical_compensatedSquare_martingale`, `OAI.Problem367.IsingObservationFactor.canonical_field_eq_normalized_integral`, `OAI.Problem367.IsingObservationFactor.canonical_stopped_field_eq_of_integral_limits`, `OAI.Problem367.IsingObservationFactor.continuousPosterior_initial_zero`, `OAI.Problem367.IsingObservationFactor.continuousRootCovariance_uniformObservation_eq_covariance_ae`, `OAI.Problem367.IsingObservationFactor.continuousRootResponse_hasSum_timeEnergy`, `OAI.Problem367.IsingObservationFactor.continuousRootResponse_row_eq_ae`, `OAI.Problem367.IsingObservationFactor.copied_difference_decomposition`, `OAI.Problem367.IsingObservationFactor.exists_canonical_root_covariance_integral_representation`, `OAI.Problem367.IsingObservationFactor.isLocalizingSequence_commonPosteriorExit`, `OAI.Problem367.IsingObservationFactor.siteVariance_eq_zero_of_subcritical_actual_variance_identity`, `OAI.Problem367.IsingObservationFactor.variance_analysis_of_joined_decomposition`, `OAI.Problem367.IsingOrientedPath.measure_extensionAverage_gt_le_double_exp_common`, `OAI.Problem367.IsingRootDoubleExponential.integral_root_weight_mul_sq_le_double_exp`, `OAI.Problem367.exists_gaussianComponentField_critical_moment_tail`, `OAI.Problem367.free_ising_factor_below_threshold_of_actual_variance_identity`, `OAI.Problem367.integral_cutContinuationProduct_gaussianConeFactor_le`, `OAI.Problem367.measure_gaussian_inward_path_average_ge_le` and `OAI.Problem367.measure_gaussian_inward_restricted_path_average_ge_le_double_exp`.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI003
import Definitions.Def_Q243FI004

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ArrayLaw
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

section ContinuousPaths

variable {T : Type*} [TopologicalSpace T] [TopologicalSpace.SeparableSpace T]
  [Nonempty T] [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]
  [StandardBorelSpace C(T, ℝ)]

theorem measurable_continuousPath_of_evaluations
    {Ω : Type*} [MeasurableSpace Ω] {X : Ω → C(T, ℝ)}
    (hm : ∀ t, Measurable (fun ω => X ω t)) : Measurable X := by
  apply measurableEmbedding_continuousPath_denseSeq.measurable_comp_iff.mp
  exact Measurable.of_eval (fun index => hm (TopologicalSpace.denseSeq T index))

end ContinuousPaths

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_PairedFiniteField
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem finite_site_posterior_field_bound {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (energy : (V → IsingSpin) → ℝ) (x K : ℝ)
    (h : ∀ r : {w : V // w ≠ v} → IsingSpin,
      |energy ((Equiv.funSplitAt v IsingSpin).symm (.pos, r)) -
        energy ((Equiv.funSplitAt v IsingSpin).symm (.neg, r))| ≤ 2 * K) :
    |Real.artanh (FinitePosterior.mean energy (fun s => spinSign (s v))
      (fun s => spinSign (s v)) x) - x| ≤ K := by
  let : Nonempty IsingSpin := ⟨.neg⟩
  exact paired_posterior_field_bound_equiv (Equiv.funSplitAt v IsingSpin) energy x K h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteGibbsField
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem siteResidualEnergy_flip_bound (edges : Finset (V × V)) {beta : ℝ}
    (hbeta : 0 ≤ beta) (y : V → ℝ) (v : V)
    (r : {w : V // w ≠ v} → IsingSpin) :
    |siteResidualEnergy edges beta y v ((Equiv.funSplitAt v IsingSpin).symm (.pos, r)) -
      siteResidualEnergy edges beta y v ((Equiv.funSplitAt v IsingSpin).symm (.neg, r))| ≤
      2 * ((edges.filter (fun e => e.1 = v ∨ e.2 = v)).card : ℝ) * beta := by
  let sp := (Equiv.funSplitAt v IsingSpin).symm (.pos, r)
  let sm := (Equiv.funSplitAt v IsingSpin).symm (.neg, r)
  have hsame (w : V) (hw : w ≠ v) : sp w = sm w := by
    simp [sp, sm, Equiv.funSplitAt_symm_apply, hw]
  have hfield : (∑ w ∈ Finset.univ.erase v, y w * spinSign (sp w)) =
      ∑ w ∈ Finset.univ.erase v, y w * spinSign (sm w) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [hsame w (Finset.mem_erase.mp hw).1]
  have habs (a b : IsingSpin) : |spinSign a * spinSign b| = 1 := by
    cases a <;> cases b <;> norm_num [spinSign]
  have hterm (e : V × V) :
      |spinSign (sp e.1) * spinSign (sp e.2) - spinSign (sm e.1) * spinSign (sm e.2)| ≤
        if e.1 = v ∨ e.2 = v then 2 else 0 := by
    split_ifs with he
    · calc
        _ ≤ |spinSign (sp e.1) * spinSign (sp e.2)| +
            |spinSign (sm e.1) * spinSign (sm e.2)| := by
          simpa using abs_sub_le (spinSign (sp e.1) * spinSign (sp e.2)) 0
            (spinSign (sm e.1) * spinSign (sm e.2))
        _ = 2 := by rw [habs, habs]; norm_num
    · rw [hsame e.1 (not_or.mp he).1, hsame e.2 (not_or.mp he).2]
      simp
  have hsum : |∑ e ∈ edges, (spinSign (sp e.1) * spinSign (sp e.2) -
      spinSign (sm e.1) * spinSign (sm e.2))| ≤
      ((edges.filter (fun e => e.1 = v ∨ e.2 = v)).card : ℝ) * 2 := by
    calc
      _ ≤ ∑ e ∈ edges, |spinSign (sp e.1) * spinSign (sp e.2) -
          spinSign (sm e.1) * spinSign (sm e.2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ edges, if e.1 = v ∨ e.2 = v then (2 : ℝ) else 0 :=
        Finset.sum_le_sum (fun e _ => hterm e)
      _ = _ := by rw [← Finset.sum_filter]; simp
  change |siteResidualEnergy edges beta y v sp - siteResidualEnergy edges beta y v sm| ≤ _
  unfold siteResidualEnergy finiteInteractionEnergy
  rw [hfield, add_sub_add_right_eq_sub, ← mul_sub, ← Finset.sum_sub_distrib,
    abs_mul, abs_of_nonneg hbeta]
  nlinarith [mul_le_mul_of_nonneg_left hsum hbeta]

theorem finite_gibbs_site_field_bound (edges : Finset (V × V)) {beta : ℝ}
    (hbeta : 0 ≤ beta) (y : V → ℝ) (v : V) :
    |Real.artanh (FinitePosterior.mean (siteResidualEnergy edges beta y v)
      (fun s => spinSign (s v)) (fun s => spinSign (s v)) (y v)) - y v| ≤
      ((edges.filter (fun e => e.1 = v ∨ e.2 = v)).card : ℝ) * beta := by
  apply finite_site_posterior_field_bound
  intro r
  simpa only [mul_assoc] using siteResidualEnergy_flip_bound edges hbeta y v r

theorem finite_gibbs_posterior_field_bound (edges : Finset (V × V)) {beta : ℝ}
    (hbeta : 0 ≤ beta) (y : V → ℝ) (v : V) :
    |Real.artanh (FinitePosterior.fieldMean (finiteInteractionEnergy edges beta)
      (fun s w => spinSign (s w)) (fun s => spinSign (s v)) y) - y v| ≤
      ((edges.filter (fun e => e.1 = v ∨ e.2 = v)).card : ℝ) * beta := by
  rw [finite_gibbs_fieldMean_eq]
  exact finite_gibbs_site_field_bound edges hbeta y v

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_GibbsField
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem finite_tree_gibbs_field_bound {d : ℕ} (D : Finset (TreeVertex d))
    {beta : ℝ} (hbeta : 0 ≤ beta) (y : D → ℝ) (v : D) :
    |Real.artanh (FinitePosterior.fieldMean
      (fun eta : D → IsingSpin => beta * ∑ e ∈ inducedEdges D,
        spinSign (extendFiniteSpin D eta e.1) * spinSign (extendFiniteSpin D eta e.2))
      (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v)) y) - y v| ≤
      (((inducedEdges D).filter (fun e => e.1 = v.1 ∨ e.2 = v.1)).card : ℝ) * beta := by
  classical
  have h := finite_gibbs_posterior_field_bound (finiteTreeEdges D) hbeta y v
  have he : finiteInteractionEnergy (finiteTreeEdges D) beta =
      (fun eta : D → IsingSpin => beta * ∑ e ∈ inducedEdges D,
        spinSign (extendFiniteSpin D eta e.1) * spinSign (extendFiniteSpin D eta e.2)) :=
    funext (finiteInteractionEnergy_tree D beta)
  rw [he, finiteTreeEdges_incident_card] at h
  exact h

theorem finite_tree_gibbs_field_uniform_bound {d : ℕ} (D : Finset (TreeVertex d))
    {beta : ℝ} (hbeta : 0 ≤ beta) (y : D → ℝ) (v : D) :
    |Real.artanh (FinitePosterior.fieldMean
      (fun eta : D → IsingSpin => beta * ∑ e ∈ inducedEdges D,
        spinSign (extendFiniteSpin D eta e.1) * spinSign (extendFiniteSpin D eta e.2))
      (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v)) y) - y v| ≤
      (d : ℝ) * beta := by
  apply (finite_tree_gibbs_field_bound D hbeta y v).trans
  apply mul_le_mul_of_nonneg_right _ hbeta
  exact_mod_cast card_incident_inducedEdges_le D v.1

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_EntropyEnergy
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace Problem367

local instance finiteIsingBrownianEntropyNonemptySpin_rb8db83_1 : Nonempty IsingSpin := ⟨.neg⟩
def finiteIsingBrownianEntropy {d : ℕ} {Ω : Type*}
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : ℝ :=
  FinitePosterior.fieldEntropy (finiteIsingEnergy beta D)
    (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v))
    (finiteIsingBrownianObservation B D t p)

def finiteIsingBrownianNormalizedCovariance {d : ℕ} {Ω : Type*}
    (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : ℝ :=
  FinitePosterior.normalizedFieldCovariance (finiteIsingEnergy beta D)
    (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v))
    (finiteIsingBrownianObservation B D t p) u

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PlantedBridgeInfinite
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

lemma planted_infinite_bridges_indep_signal_terminal
    {ι S Omega : Type*} [MeasurableSpace S] [MeasurableSpace Omega]
    (nu : Measure S) (mu : ι → Measure Omega) [IsProbabilityMeasure nu]
    {B : ι → ℝ≥0 → Omega → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (mu i))
    (hmB : ∀ i t, Measurable (B i t))
    {sigma : S → ι → ℝ} (hsigma : Measurable sigma)
    {T : ℝ≥0} (hT : T ≠ 0) :
    IndepFun
      (fun q : S × (ι → Omega) =>
        (q.1, fun i => (T : ℝ) * sigma q.1 i + B i T (q.2 i)))
      (fun q i (s : Set.Iic T) => brownianBridge (B i) T s (q.2 i))
      (nu.prod (Measure.infinitePi mu)) := by
  have (index : ι) : IsProbabilityMeasure (mu index) :=
    (hB index).isGaussianProcess.isProbabilityMeasure
  have hmbridge (i : ι) :
      Measurable (fun w (s : Set.Iic T) => brownianBridge (B i) T s w) := by
    apply Measurable.of_eval
    intro s
    exact (hmB i s).sub ((hmB i T).const_mul _)
  have hi := indepFun_infinitePi_of_coordinate_indepFun mu (fun i => hmB i T) hmbridge
    (fun i => (preBrownian_bridge_indep_terminal (hB i) hT).symm)
  have hp := indepFun_prod_left_of_indepFun nu (Measure.infinitePi mu)
    (by fun_prop : Measurable (fun w : ι → Omega => fun i => B i T (w i)))
    (Measurable.of_eval (fun index => (hmbridge index).comp (measurable_pi_apply index))) hi
  have hm : Measurable (fun q : S × (ι → ℝ) =>
      (q.1, fun i => (T : ℝ) * sigma q.1 i + q.2 i)) := by fun_prop
  simpa only [Function.comp_def, id_eq] using hp.comp hm measurable_id

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_Symmetry
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace Problem367.PlantedSymmetry

theorem observationSigma_le (ι : Type*) (t : ℝ) :
    observationSigma ι t ≤ (inferInstance : MeasurableSpace ((ι → IsingSpin) × (ι → ℝ))) :=
  (measurable_observation t).comap_le

theorem measurable_posteriorMagnetization {ι : Type*}
    (rho : Measure ((ι → IsingSpin) × (ι → ℝ))) (t : ℝ) (v : ι) :
    Measurable (posteriorMagnetization rho t v) := by
  exact stronglyMeasurable_condExp.measurable.mono (observationSigma_le ι t) le_rfl

end Problem367.PlantedSymmetry

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ConnectedExhaustion
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem connectedExhaustion_connected {d : ℕ} (v : TreeVertex d) (n : ℕ) :
    ConnectedFinset (connectedExhaustion v n) :=
  ConnectedHull.connected_hull _

theorem connectedExhaustion_monotone {d : ℕ} (v : TreeVertex d) :
    Monotone (connectedExhaustion v) := by
  classical
  intro n m hnm
  exact ConnectedHull.hull_mono (Finset.insert_subset_insert v
    (monotone_treeBallFinset d hnm))

theorem exists_connected_exhaustion {d : ℕ} (v : TreeVertex d) :
    ∃ D : ℕ → Finset (TreeVertex d), Monotone D ∧
      (∀ n, ConnectedFinset (D n) ∧ v ∈ D n) ∧
      ∀ w, ∃ n, w ∈ D n := by
  refine ⟨connectedExhaustion v, connectedExhaustion_monotone v,
    fun n => ⟨connectedExhaustion_connected v n, mem_connectedExhaustion v n⟩, ?_⟩
  intro w
  exact (eventually_mem_connectedExhaustion v w).exists

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_InfinitePosteriorField
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace Problem367

open PlantedSymmetry

attribute [local instance] OAI.Problem367.infinitePosteriorFieldNonemptySpin
theorem finiteIsingPosterior_tanh_bounds {d : ℕ} {beta : ℝ}
    (hbeta : 0 ≤ beta) (D : Finset (TreeVertex d)) (y : D → ℝ) (v : D) :
    Real.tanh (y v - (d : ℝ) * beta) ≤
      FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) w => spinSign (eta w))
        (fun eta => spinSign (eta v)) y ∧
    FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) w => spinSign (eta w))
        (fun eta => spinSign (eta v)) y ≤ Real.tanh (y v + (d : ℝ) * beta) := by
  have hmem := FinitePosterior.fieldMean_spin_mem_Ioo (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta v)) y
    (fun eta => by cases eta v <;> simp [spinSign])
    ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩
  have hb := finite_tree_gibbs_field_uniform_bound D hbeta y v
  change |Real.artanh (FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta v)) y) - y v| ≤ (d : ℝ) * beta at hb
  have hmono : Monotone Real.tanh := by
    apply monotone_of_deriv_nonneg
    · intro x
      exact (hasDerivAt_tanh_response x).differentiableAt
    · intro x
      rw [(hasDerivAt_tanh_response x).deriv]
      exact (sub_pos.mpr (Real.tanh_sq_lt_one x)).le
  have hlo := hmono (show y v - (d : ℝ) * beta ≤
    Real.artanh (FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v)) y) by linarith [(abs_le.mp hb).1])
  have hhi := hmono (show Real.artanh (FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v)) y) ≤ y v + (d : ℝ) * beta by
        linarith [(abs_le.mp hb).2])
  rw [Real.tanh_artanh hmem] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem HasFreeIsingLaw.finiteObservation_spin_tanh_bounds {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0) (v : D) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Real.tanh (observation t p v.1 - (d : ℝ) * beta) ≤
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
          fun p => spinSign (p.1 v.1) |
          MeasurableSpace.comap (finiteObservation D t) inferInstance] p ∧
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
          fun p => spinSign (p.1 v.1) |
          MeasurableSpace.comap (finiteObservation D t) inferInstance] p ≤
        Real.tanh (observation t p v.1 + (d : ℝ) * beta) := by
  filter_upwards [hμ.finiteObservation_condExp D hD t (fun eta => spinSign (eta v))]
    with p hp
  change (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
    fun p => spinSign (p.1 v.1) |
    MeasurableSpace.comap (finiteObservation D t) inferInstance] p = _ at hp
  rw [hp]
  exact finiteIsingPosterior_tanh_bounds hbeta D (finiteObservation D t p) v

def finiteObservationFiltration {d : ℕ} (D : ℕ → Finset (TreeVertex d))
    (hD : Monotone D) (t : ℝ≥0) :
    Filtration ℕ (inferInstance : MeasurableSpace
      ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ))) where
  seq n := MeasurableSpace.comap (finiteObservation (D n) t) inferInstance
  mono' n m h := by
    change MeasurableSpace.comap (fun p (v : D n) => observation t p v.1) inferInstance ≤
      MeasurableSpace.comap (fun p (v : D m) => observation t p v.1) inferInstance
    rw [MeasurableSpace.comap_process_pi, MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro v
    exact le_iSup_of_le (⟨v.1, hD h v.2⟩ : D m) le_rfl
  le' n := (measurable_finiteObservation (D n) t).comap_le

theorem finiteObservationFiltration_iSup {d : ℕ}
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hex : ∀ v, ∃ n, v ∈ D n) (t : ℝ≥0) :
    (⨆ n, finiteObservationFiltration D hD t n) = observationSigma (TreeVertex d) t := by
  change (⨆ n, MeasurableSpace.comap
    (fun p (v : D n) => observation t p v.1) inferInstance) =
    MeasurableSpace.comap (fun p (v : TreeVertex d) => observation t p v) inferInstance
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def]
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro v
    exact le_iSup_of_le v.1 le_rfl
  · apply iSup_le
    intro v
    obtain ⟨n, hn⟩ := hex v
    exact le_iSup_of_le n (le_iSup_of_le (⟨v, hn⟩ : D n) le_rfl)

theorem HasFreeIsingLaw.posterior_field_bound_of_exhaustion {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (v : TreeVertex d) (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hv : ∀ n, v ∈ D n)
    (hex : ∀ w, ∃ n, w ∈ D n) (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p ∈
        Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (posteriorMagnetization
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p) - observation t p v| ≤
        (d : ℝ) * beta := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hb (n : ℕ) := hμ.finiteObservation_spin_tanh_bounds hbeta
    (D n) (hconn n) t ⟨v, hv n⟩
  have hlim := tendsto_posterior_fields_ae
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (finiteObservationFiltration D hD t)
    (fun p => spinSign (p.1 v)) (fun p => observation t p v) ((d : ℝ) * beta) hb
  rw [finiteObservationFiltration_iSup D hD hex t] at hlim
  filter_upwards [hlim] with p hp
  exact ⟨hp.1, hp.2.1⟩

theorem HasFreeIsingLaw.gaussian_posterior_field_bound {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p ∈
        Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (posteriorMagnetization
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p) - observation t p v| ≤
        (d : ℝ) * beta := by
  obtain ⟨D, hD, hconn, hex⟩ := exists_connected_exhaustion v
  exact hμ.posterior_field_bound_of_exhaustion hbeta v D hD
    (fun n => (hconn n).1) (fun n => (hconn n).2) hex t

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PlantedSufficiencyVector
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory NNReal

namespace Problem367.TerminalSufficiency

theorem condExp_planted_infinite_past_eq_terminal
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    (signal : S → ι → ℝ) (f : S → ℝ)
    (hSignal : Measurable signal) (hf : Measurable f) (hfint : Integrable f ν)
    (T : ℝ≥0) :
    (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (ι → Ω) => fun i (s : Set.Iic T) =>
          (s.1 : ℝ) * signal q.1 i + B i s.1 (q.2 i)) inferInstance]
        =ᵐ[ν.prod (Measure.infinitePi μ)]
    (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (ι → Ω) => fun i =>
          (T : ℝ) * signal q.1 i + B i T (q.2 i)) inferInstance] := by
  by_cases hT : T = 0
  · subst T
    rw [comap_array_past_zero
      (fun (q : S × (ι → Ω)) t i => (t : ℝ) * signal q.1 i + B i t (q.2 i))]
  have (index : ι) : IsProbabilityMeasure (μ index) :=
    (hB index).isGaussianProcess.isProbabilityMeasure
  exact condExp_planted_array_past_eq_terminal_of_indep ν (Measure.infinitePi μ)
    hmB signal f hSignal hf hfint hT
    (Problem367.planted_infinite_bridges_indep_signal_terminal ν μ hB hmB hSignal hT)

end Problem367.TerminalSufficiency

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ProgressiveIsingPosterior
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

open PlantedSymmetry

attribute [local instance] OAI.Problem367.progressiveIsingPosteriorNonemptyIsingSpin
theorem HasFreeIsingLaw.infiniteGibbsSpinMean_eq_posterior {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v : TreeVertex d) :
    (fun p => infiniteGibbsSpinMean beta v (observation t p)) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hce (n : ℕ) := hμ.finiteObservation_condExp (connectedExhaustion v n)
    (connectedExhaustion_connected v n) t
    (fun eta => spinSign (eta ⟨v, mem_connectedExhaustion v n⟩))
  have hlim := tendsto_ae_condExp (μ := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (ℱ := finiteObservationFiltration (connectedExhaustion v)
      (connectedExhaustion_monotone v) t) (fun p => spinSign (p.1 v))
  rw [finiteObservationFiltration_iSup (connectedExhaustion v)
    (connectedExhaustion_monotone v)
    (fun w => (eventually_mem_connectedExhaustion v w).exists) t] at hlim
  filter_upwards [ae_all_iff.mpr hce, hlim,
    posteriorMagnetization_abs_le_one (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v]
    with p hp hlim hb
  have hseq : Tendsto (fun n => finiteGibbsSpinMean beta v n (observation t p)) atTop
      (𝓝 (posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p)) := by
    convert hlim using 1
    · ext n
      exact (hp n).symm
    · rfl
  change max (-1) (min 1 (limUnder atTop _)) = _
  rw [hseq.limUnder_eq, min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_eq_brownian_past
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) =ᵐ[
        μ.prod (Measure.infinitePi ν)]
      (μ.prod (Measure.infinitePi ν))[fun p => spinSign (p.1 v) |
        MeasurableSpace.comap
          (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
            fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
          inferInstance] := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun omega i => B i t (omega i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hspin : Measurable (fun sigma : TreeVertex d → IsingSpin => spinSign (sigma v)) :=
    hsign.comp (measurable_pi_apply v)
  have hspini : Integrable (fun sigma : TreeVertex d → IsingSpin => spinSign (sigma v)) μ := by
    apply Integrable.of_bound hspin.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro sigma
    cases hs : sigma v <;> norm_num [spinSign, hs]
  have hpull := condExp_comp_measurePreserving_comap hT
    (hspin.comp measurable_fst).stronglyMeasurable
    (integrable_plantedSpin (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) v)
    (observationSigma_le (TreeVertex d) t)
  have hpast := TerminalSufficiency.condExp_planted_infinite_past_eq_terminal
    μ ν hB hmB (fun sigma i => spinSign (sigma i))
    (fun sigma => spinSign (sigma v))
    (Measurable.of_eval (fun i => hsign.comp (measurable_pi_apply i))) hspin hspini t
  have heq := hμ.infiniteGibbsSpinMean_eq_posterior t v
  rw [← hT.map_eq] at heq
  have heq' := ae_of_ae_map hT.measurable.aemeasurable heq
  rw [hT.map_eq] at heq'
  filter_upwards [hpast, hpull, heq'] with p hpast hpull heq
  change _ = posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v (T p)
    at hpull
  have hsame : (observationSigma (TreeVertex d) (t : ℝ)).comap T =
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) inferInstance := by
    rw [observationSigma, MeasurableSpace.comap_comp]
    rfl
  rw [hsame] at hpull
  simp only [Function.comp_def, T, Prod.map_fst, id_eq] at hpull
  rw [hpast, hpull]
  exact heq

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CoordinateResponse
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.TreePathResponse

def field {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) (u : TreeVertex d) : ℝ :=
  Real.artanh (mean beta h D u)

end Problem367.TreePathResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_NormalizedInfiniteTimeEnergy
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.NormalizedInfiniteTimeEnergy

open GaussianTreeResponse

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

def finiteRow (beta : ℝ) (D : Finset (TreeVertex d)) (v : TreeVertex d)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (w : TreeVertex d)
    (q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) : ℝ :=
  observedRow beta D v q.1 w (q.2.1, fun i => B i q.1.toNNReal (q.2.2 i))

end Problem367.NormalizedInfiniteTimeEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PlantedStationarity
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.PlantedStationarity

variable {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem map_coordinateMap_relabel {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu] (F : IsingSpin → A → B)
    (hF : Measurable (Function.uncurry F)) (g : TreeAut d) :
    ((mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))).map
      (coordinateMap F)).map (relabel g) =
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))).map
        (coordinateMap F) := by
  rw [Measure.map_map (measurable_relabel g) (measurable_coordinateMap hF)]
  change (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))).map
    (coordinateMap F ∘ Prod.map (relabel g) (relabel g)) = _
  rw [← Measure.map_map (measurable_coordinateMap hF)
    ((measurable_relabel g).prodMap (measurable_relabel g)),
    (measurePreserving_planted_relabel hmu nu g).map_eq]

theorem measurePreserving_coordinateMap_relabel {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu] (F : IsingSpin → A → B)
    (hF : Measurable (Function.uncurry F)) (g : TreeAut d) :
    MeasurePreserving (relabel g)
      ((mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))).map (coordinateMap F))
      ((mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))).map (coordinateMap F)) :=
  ⟨measurable_relabel g, map_coordinateMap_relabel hmu nu F hF g⟩

end Problem367.PlantedStationarity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_CovarianceCompensator
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367

def gibbsCovarianceEnergy {d : ℕ} {Ω : Type*} (beta : ℝ) (v : TreeVertex d)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) : ℝ :=
  ∑' w, infiniteGibbsCovariance beta v w (brownianIsingObservationR B p) ^ 2

def finiteGibbsCovarianceEnergy {d : ℕ} {Ω : Type*} (beta : ℝ)
    (v : TreeVertex d) (n : ℕ) (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) : ℝ :=
  ∑' w, finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2

def gibbsCovarianceCompensator {d : ℕ} {Ω : Type*} (beta : ℝ)
    (v : TreeVertex d) (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), gibbsCovarianceEnergy beta v B (s, p)

def finiteGibbsCovarianceCompensator {d : ℕ} {Ω : Type*} (beta : ℝ)
    (v : TreeVertex d) (n : ℕ) (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), finiteGibbsCovarianceEnergy beta v n B (s, p)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_WienerSampler
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.WienerSampler

theorem isBrownianReal_of_sampler {ξ : ℝ → Path} (hξ : Measurable ξ)
    (hξlaw : Measure.map ξ uniform01 = wienerMeasure) :
    IsBrownianReal (fun t u => ξ u t) uniform01 where
  hasLaw I := (coordinate_isBrownianReal.hasLaw I).comp ⟨hξ.aemeasurable, hξlaw⟩
  cont := Filter.Eventually.of_forall (fun u => (ξ u).continuous)

theorem sample_isBrownianReal : IsBrownianReal (fun t u => sample u t) uniform01 :=
  isBrownianReal_of_sampler measurable_sample map_sample

end Problem367.WienerSampler

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_InnovationPathMap
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

theorem measurable_innovationPath
    [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]
    [StandardBorelSpace C(ℝ≥0, ℝ)]
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {X : Ω → C(ℝ≥0, ℝ)}
    {m : ℝ≥0 → Ω → ℝ} (hm : IsStronglyProgressive F m)
    {K : ℝ≥0} (hbound : ∀ t ω, ‖m t ω‖ ≤ (K : ℝ)) (hX : Measurable X) :
    Measurable (innovationPath X m hm hbound) := by
  apply measurable_continuousPath_of_evaluations
  intro t
  exact ((continuous_eval_const t).measurable.comp hX).sub
    (measurable_nnrealTimePrimitive_of_progressive hm t)

theorem measurable_innovationPath_array
    [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]
    [StandardBorelSpace C(ℝ≥0, ℝ)]
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {X : Ω → ι → C(ℝ≥0, ℝ)}
    {m : ι → ℝ≥0 → Ω → ℝ} (hm : ∀ i, IsStronglyProgressive F (m i))
    {K : ℝ≥0} (hbound : ∀ i t ω, ‖m i t ω‖ ≤ (K : ℝ)) (hX : Measurable X) :
    Measurable (fun ω i => innovationPath (fun ω => X ω i) (m i) (hm i) (hbound i) ω) := by
  apply Measurable.of_eval
  intro i
  exact measurable_innovationPath (hm i) (hbound i) ((measurable_pi_apply i).comp hX)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_Innovation
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingInnovation

theorem posterior_progressive {d : ℕ} {A : Type*} [MeasurableSpace A]
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (hcB : ∀ a, Continuous (fun t => B t a)) (v : TreeVertex d) :
    IsStronglyProgressive (ArrayPosteriorStationarity.filtration B hmB)
      (posterior beta B v) := by
  apply isStronglyProgressive_infiniteGibbsSpinMean
  intro i
  apply (arrayNaturalFiltration_stronglyAdapted
    (plantedArrayObservation (fun _ : TreeVertex d => B) ArrayPosteriorStationarity.spinArray)
    (plantedArrayObservation_measurable (fun _ => hmB)
      ArrayPosteriorStationarity.measurable_spinArray) i).isStronglyProgressive_of_continuous
  intro q
  exact (hcB (q.2 i)).add (continuous_subtype_val.mul continuous_const)

theorem measurable_posterior_joint {d : ℕ} {A : Type*} [MeasurableSpace A]
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (hcB : ∀ a, Continuous (fun t => B t a)) (v : TreeVertex d) :
    Measurable (fun p : ℝ≥0 × State d A => posterior beta B v p.1 p.2) := by
  apply (measurable_infiniteGibbsSpinMean beta v).comp
  apply Measurable.of_eval
  intro i
  apply StronglyMeasurable.measurable
  change StronglyMeasurable (Function.uncurry
    (plantedArrayObservation (fun _ : TreeVertex d => B) ArrayPosteriorStationarity.spinArray i))
  apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
  · intro q
    exact (hcB (q.2 i)).add (continuous_subtype_val.mul continuous_const)
  · intro t
    exact (plantedArrayObservation_measurable (fun _ => hmB)
      ArrayPosteriorStationarity.measurable_spinArray i t).stronglyMeasurable

theorem posterior_eq_condExp {d : ℕ} {A : Type*} [MeasurableSpace A]
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (t : ℝ≥0) (v : TreeVertex d) :
    posterior beta B v t =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      ArrayPosteriorStationarity.posterior
        (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v := by
  have heq := hμ.infiniteGibbsSpinMean_eq_brownian_past
    (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB) t v
  have hF : ArrayPosteriorStationarity.filtration (d := d) B hmB t =
      MeasurableSpace.comap
        (fun q : State d A => fun i (s : Set.Iic t) =>
          (s.1 : ℝ) * spinSign (q.1 i) + B s.1 (q.2 i)) inferInstance := by
    change arrayNaturalFiltration
      (plantedArrayObservation (fun _ : TreeVertex d => B) ArrayPosteriorStationarity.spinArray)
      (plantedArrayObservation_measurable (fun _ => hmB)
        ArrayPosteriorStationarity.measurable_spinArray) t = _
    rw [arrayNaturalFiltration_eq_comap]
    congr 1
    funext q i s
    exact add_comm _ _
  have hp : posterior beta B v t =
      (fun q : State d A => infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (q.1 i) + B t (q.2 i))) := by
    funext q
    unfold posterior
    congr 1
    funext i
    exact add_comm _ _
  rw [hp]
  unfold ArrayPosteriorStationarity.posterior
  rw [hF]
  exact heq

theorem isBrownianReal_innovation {d : ℕ} {A : Type*} [MeasurableSpace A]
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) :
    IsBrownianReal (innovation beta B v)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  refine brownian_array_innovation_of_progressive_posterior
    μ (fun _ : TreeVertex d => ν)
    (fun _ => ⟨hB, Filter.Eventually.of_forall hcB⟩)
    (fun _ => hmB) ArrayPosteriorStationarity.measurable_spinArray v
    (C := 1) ?_ (posterior_progressive beta B hmB hcB v) ?_
  · apply Filter.Eventually.of_forall
    intro q
    cases hq : q v <;> norm_num [ArrayPosteriorStationarity.spinArray, spinSign, hq]
  · intro t
    exact posterior_eq_condExp hμ ν hB hmB t v

theorem measurable_innovation_array {d : ℕ} {A : Type*} [MeasurableSpace A]
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (hcB : ∀ a, Continuous (fun t => B t a)) :
    Measurable (fun q : State d A => fun v t => innovation beta B v t q) := by
  apply Measurable.of_eval
  intro v
  apply Measurable.of_eval
  intro t
  exact (plantedArrayObservation_measurable (fun _ => hmB)
    ArrayPosteriorStationarity.measurable_spinArray v t).sub
    (((stronglyAdapted_nnrealTimePrimitive (posterior_progressive beta B hmB hcB v) t).mono
      (ArrayPosteriorStationarity.filtration B hmB |>.le t)).measurable)

theorem innovation_array_relabel_ae {d : ℕ} {A : Type*} [MeasurableSpace A]
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (g : TreeAut d) :
    ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
      (fun v t => innovation beta B v t (ArrayPosteriorStationarity.plantedRelabel g q)) =
        relabel g (fun v t => innovation beta B v t q) := by
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  exact ArrayPosteriorStationarity.innovation_array_relabel_ae hμ ν B hmB
    (fun v => measurable_posterior_joint beta B hmB hcB v)
    (fun t v => posterior_eq_condExp hμ ν hB hmB t v) g

theorem uniformInnovation_properties {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) :
    Measurable (uniformInnovation (d := d) beta) ∧
    (∀ v : TreeVertex d,
      IsBrownianReal (fun t q => uniformInnovation beta q v t) (μ.prod (labelMeasure d))) ∧
    (∀ g : TreeAut d, ∀ᵐ q ∂μ.prod (labelMeasure d),
      uniformInnovation beta (Prod.map (relabel g) (relabel g) q) =
        relabel g (uniformInnovation beta q)) := by
  have hmB (t : ℝ≥0) : Measurable (fun u => WienerSampler.sample u t) :=
    WienerSampler.measurable_sample_eval.comp (measurable_const.prodMk measurable_id)
  have hcB (u : ℝ) : Continuous (fun t => WienerSampler.sample u t) :=
    (WienerSampler.sample u).continuous
  refine ⟨measurable_innovation_array beta _ hmB hcB, ?_, ?_⟩
  · intro v
    exact isBrownianReal_innovation hμ uniform01
      WienerSampler.sample_isBrownianReal.toIsPreBrownianReal hmB hcB v
  · intro g
    exact innovation_array_relabel_ae hμ uniform01
      WienerSampler.sample_isBrownianReal.toIsPreBrownianReal hmB hcB g

end Problem367.IsingInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_InnovationLaw
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingInnovation

theorem exists_continuous_innovation_array {d : ℕ} {A : Type*}
    [MeasurableSpace A] {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a)) :
    ∃ X : State d A → TreeVertex d → WienerSampler.Path,
      Measurable X ∧
      (∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
        ∀ v t, X q v t = innovation beta B v t q) ∧
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))).map X =
        Measure.infinitePi (fun _ : TreeVertex d => WienerSampler.wienerMeasure) ∧
      ∀ g : TreeAut d,
        ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
          X (ArrayPosteriorStationarity.plantedRelabel g q) = relabel g (X q) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Y, hYm, hYe, hYlaw⟩ :=
    ArrayInnovationLaw.exists_continuous_innovation_array_wiener_law
      μ (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB)
      ArrayPosteriorStationarity.measurable_spinArray (spinArray_bound μ)
      (posterior_progressive beta B hmB hcB)
      (fun v t => posterior_eq_condExp hμ ν hB hmB t v)
      (fun _ => Filter.Eventually.of_forall hcB)
  have heq : ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
      ∀ v t, Y v q t = innovation beta B v t q := ae_all_iff.mpr hYe
  refine ⟨fun q v => Y v q, Measurable.of_eval hYm, heq, hYlaw, ?_⟩
  intro g
  have htrans := (ArrayPosteriorStationarity.measurePreserving_plantedRelabel
    hμ ν g).quasiMeasurePreserving.ae heq
  filter_upwards [heq, htrans, innovation_array_relabel_ae hμ ν hB hmB hcB g]
    with q hq hqg hg
  funext v
  apply ContinuousMap.ext
  intro t
  calc
    Y v (ArrayPosteriorStationarity.plantedRelabel g q) t =
        innovation beta B v t (ArrayPosteriorStationarity.plantedRelabel g q) := hqg v t
    _ = innovation beta B (g.toEquiv.symm v) t q := congrFun (congrFun hg v) t
    _ = Y (g.toEquiv.symm v) q t := (hq (g.toEquiv.symm v) t).symm

theorem exists_continuous_uniformInnovation {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) :
    ∃ X : State d ℝ → TreeVertex d → WienerSampler.Path,
      Measurable X ∧
      (∀ᵐ q ∂μ.prod (labelMeasure d), ∀ v t, X q v t = uniformInnovation beta q v t) ∧
      (μ.prod (labelMeasure d)).map X =
        Measure.infinitePi (fun _ : TreeVertex d => WienerSampler.wienerMeasure) ∧
      ∀ g : TreeAut d, ∀ᵐ q ∂μ.prod (labelMeasure d),
        X (Prod.map (relabel g) (relabel g) q) = relabel g (X q) := by
  exact exists_continuous_innovation_array hμ uniform01
    WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
    (fun t => WienerSampler.measurable_sample_eval.comp
      (measurable_const.prodMk measurable_id))
    (fun u => (WienerSampler.sample u).continuous)

end Problem367.IsingInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_InnovationIndependence
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]
  {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
  (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
  (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
  (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))

include hμ hB hcB

omit hμ hB hcB in

def uniformObservationFiltration (d : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (State d ℝ)) :=
  ArrayPosteriorStationarity.filtration
    (fun t u => WienerSampler.sample u t)
    (fun _t => WienerSampler.measurable_sample_eval.comp
      (measurable_const.prodMk measurable_id))

end Problem367.IsingInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationInnovation
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationInnovation

theorem measurable_innovationMap {d : ℕ} (beta : ℝ) :
    Measurable (innovationMap (d := d) beta) :=
  measurable_innovationPath_array (posterior_progressive beta)
    (posterior_norm_le_one beta) measurable_id

theorem map_innovationMap_observationLaw {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) :
    (observationLaw μ).map (innovationMap beta) =
      Measure.infinitePi (fun _ : TreeVertex d => WienerSampler.wienerMeasure) := by
  obtain ⟨X, hXm, hXe, hXlaw, _⟩ := IsingInnovation.exists_continuous_uniformInnovation hμ
  rw [observationLaw, Measure.map_map (measurable_innovationMap beta)
    measurable_uniformObservation]
  apply (Measure.map_congr ?_).trans hXlaw
  filter_upwards [hXe] with q hq
  funext v
  apply ContinuousMap.ext
  intro t
  exact (hq v t).symm

theorem innovationMap_relabel_ae {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d) :
    ∀ᵐ x ∂observationLaw μ,
      innovationMap beta (relabel g x) = relabel g (innovationMap beta x) := by
  apply (ae_map_iff measurable_uniformObservation.aemeasurable
    (measurableSet_eq_fun
      ((measurable_innovationMap beta).comp (measurable_relabel g))
      ((measurable_relabel g).comp (measurable_innovationMap beta)))).mpr
  filter_upwards [(IsingInnovation.uniformInnovation_properties hμ).2.2 g] with q hq
  change innovationMap beta (relabel g (uniformObservation q)) =
    relabel g (innovationMap beta (uniformObservation q))
  rw [← uniformObservation_relabel]
  funext v
  apply ContinuousMap.ext
  intro t
  exact congrFun (congrFun hq v) t

end Problem367.IsingObservationInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FieldMoments
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

open PlantedSymmetry

theorem measurable_gaussianPosteriorField {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (v : TreeVertex d) :
    Measurable (gaussianPosteriorField μ t v) := by
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  exact ha.comp (measurable_posteriorMagnetization _ _ _)

theorem HasFreeIsingLaw.gaussian_posterior_field_noise_bound
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      |gaussianPosteriorField μ t v p - p.2 v| ≤ (d : ℝ) * beta + t := by
  filter_upwards [hμ.gaussian_posterior_field_bound hbeta t v] with p hp
  have hs : |(t : ℝ) * spinSign (p.1 v)| = t := by
    cases he : p.1 v <;> simp [spinSign, abs_of_nonneg t.coe_nonneg]
  calc
    |gaussianPosteriorField μ t v p - p.2 v| =
        |(gaussianPosteriorField μ t v p - observation t p v) +
          (t : ℝ) * spinSign (p.1 v)| := by
      congr 1
      simp only [observation]
      ring
    _ ≤ |gaussianPosteriorField μ t v p - observation t p v| +
        |(t : ℝ) * spinSign (p.1 v)| := abs_add_le _ _
    _ ≤ (d : ℝ) * beta + t := by rw [hs]; exact add_le_add hp.2 le_rfl

theorem HasFreeIsingLaw.integrable_gaussianPosteriorField_abs_pow
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) (p : ℕ) :
    Integrable (fun q => |gaussianPosteriorField μ t v q| ^ p)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  exact integrable_abs_pow_of_bounded_perturbation p (by positivity)
    (measurable_gaussianPosteriorField μ t v).aemeasurable
    (integrable_abs_pow_of_gaussianLaw (gaussianPlanted_noise_hasLaw μ t v) p)
    (hμ.gaussian_posterior_field_noise_bound hbeta t v)

theorem HasFreeIsingLaw.memLp_gaussianPosteriorField_two
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    MemLp (gaussianPosteriorField μ t v) 2
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  apply (memLp_two_iff_integrable_sq
    (measurable_gaussianPosteriorField μ t v).aestronglyMeasurable).mpr
  simpa only [sq_abs] using hμ.integrable_gaussianPosteriorField_abs_pow hbeta t v 2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ConditionalCopyBounds
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingConditionalCopyBounds

open PlantedSymmetry IsingObservationInnovation WienerSampler

instance graphLaw_isProbabilityMeasure {d : ℕ} (beta : ℝ)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (graphLaw beta μ) := by
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; (first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  unfold graphLaw observationLaw
  haveI : IsProbabilityMeasure (Measure.map uniformObservation (μ.prod (labelMeasure d))) :=
    Measure.isProbabilityMeasure_map measurable_uniformObservation.aemeasurable
  exact Measure.isProbabilityMeasure_map ((measurable_innovationMap beta).prodMk measurable_id).aemeasurable

theorem hasLaw_observationLaw_eval {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] (t : ℝ≥0) :
    HasLaw (fun x : Paths d => fun i => x i t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (observationLaw μ) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_observation <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hB (s : ℝ≥0) : Measurable (fun u : ℝ => sample u s) :=
    measurable_sample_eval.comp (measurable_const.prodMk measurable_id)
  let T : IsingInnovation.State d ℝ →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun u i => sample (u i) t)
  have hT : MeasurePreserving T (μ.prod (labelMeasure d))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod
      (brownian_array_eval_measurePreserving (fun _ => uniform01)
        (fun _ => sample_isBrownianReal.toIsPreBrownianReal) (fun _ => hB) t)
  have heval : Measurable (fun x : Paths d => fun i => x i t) :=
    Measurable.of_eval (fun i => (continuous_eval_const t).measurable.comp
      (measurable_pi_apply i))
  refine ⟨heval.aemeasurable, ?_⟩
  rw [observationLaw, Measure.map_map heval measurable_uniformObservation]
  have heq : (fun q : IsingInnovation.State d ℝ => fun i => uniformObservation q i t) =
      observation t ∘ T := by
    funext q i
    change sample (q.2 i) t + (t : ℝ) * spinSign (q.1 i) =
      (t : ℝ) * spinSign (q.1 i) + sample (q.2 i) t
    ring
  change (μ.prod (labelMeasure d)).map
    (fun q : IsingInnovation.State d ℝ => fun i => uniformObservation q i t) = _
  rw [heq, ← Measure.map_map (measurable_observation t) hT.measurable, hT.map_eq]

section Copies

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable {rho : Measure (Paths d)} [IsProbabilityMeasure rho]
variable {eta : Kernel (Paths d) (Paths d)} [IsMarkovKernel eta]

theorem measurePreserving_observation_copies
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    MeasurePreserving (fun q : CopySpace d => q.2.1)
      (rho ⊗ₘ (eta ×ₖ eta)) (observationLaw μ) ∧
    MeasurePreserving (fun q : CopySpace d => q.2.2)
      (rho ⊗ₘ (eta ×ₖ eta)) (observationLaw μ) := by
  have hsecond : MeasurePreserving (Prod.snd : Paths d × Paths d → Paths d)
      (rho ⊗ₘ eta) (observationLaw μ) := by
    refine ⟨measurable_snd, ?_⟩
    have hm : Measurable (fun x : Paths d => (innovationMap beta x, x)) :=
      (measurable_innovationMap beta).prodMk measurable_id
    rw [hjoint, graphLaw, Measure.map_map measurable_snd hm]
    exact Measure.map_id
  have hl := hsecond.comp (measurePreserving_conditionalCopy_fst rho eta)
  have hr := hsecond.comp (measurePreserving_conditionalCopy_snd rho eta)
  exact ⟨hl, hr⟩

end Copies

end Problem367.IsingConditionalCopyBounds

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationInnovation

instance innovationMap_observationLaw_probability {d : ℕ} (beta : ℝ)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
  Measure.isProbabilityMeasure_map (measurable_innovationMap beta).aemeasurable

theorem measurePreserving_observationLaw_relabel {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (g : TreeAut d) :
    MeasurePreserving (relabel g) (observationLaw μ) (observationLaw μ) := by
  refine ⟨measurable_relabel g, ?_⟩
  apply FactorTransport.map_invariant_of_ae_equivariant
    (PlantedStationarity.measurePreserving_planted_relabel hμ uniform01 g)
    (measurable_relabel g) measurable_uniformObservation
  exact Filter.Eventually.of_forall (uniformObservation_relabel g)

end Problem367.IsingObservationInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationFactor
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationFactor

open IsingObservationInnovation

variable {d : ℕ}

instance copies_probability (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (copies beta μ) := by
  unfold copies
  haveI : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    Measure.isProbabilityMeasure_map (measurable_innovationMap beta).aemeasurable
  infer_instance

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalContinuousFields
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

def continuousField {d : ℕ} (beta : ℝ) (v : TreeVertex d) : ℝ≥0 → Paths d → ℝ :=
  ProgressiveVersionPushforward.version (field beta v)

def continuousDifference {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (q : Paths d × (Paths d × Paths d)) : ℝ :=
  continuousField beta v t q.2.1 - continuousField beta v t q.2.2

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalPosteriorStops
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy PosteriorCompensatorStopping

def continuousPosterior {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : ℝ := Real.tanh (continuousField beta v t x)

def copyContinuousField {d : ℕ} (beta : ℝ) (v : TreeVertex d) (j : Bool)
    (t : ℝ≥0) (q : Joint d) : ℝ := continuousField beta v t (projection j q)

def copyContinuousPosterior {d : ℕ} (beta : ℝ) (v : TreeVertex d) (j : Bool)
    (t : ℝ≥0) (q : Joint d) : ℝ := continuousPosterior beta v t (projection j q)

def copyResponseEnergy {d : ℕ} (beta : ℝ) (v : TreeVertex d) (j : Bool)
    (t : ℝ≥0) (q : Joint d) : ℝ :=
  infiniteGibbsResponseRow beta v (fun i => projection j q i t)

def commonResponseCompensator {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    ℝ≥0 → Joint d → ℝ :=
  nnrealTimePrimitive (fun t q =>
    copyResponseEnergy beta v true t q + copyResponseEnergy beta v false t q)

def commonPosteriorExit {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (n : ℕ) (q : Joint d) : WithTop ℝ≥0 :=
  min (jointExit (copyContinuousPosterior beta v true) (commonResponseCompensator beta v) n q)
    (jointExit (copyContinuousPosterior beta v false) (commonResponseCompensator beta v) n q)

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalMartingales
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

def canonicalCovarianceEnergy {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : ℝ :=
  ∑' w, infiniteGibbsCovariance beta v w (fun i => x i t) ^ 2

def canonicalCovarianceCompensator {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    ℝ≥0 → Paths d → ℝ := nnrealTimePrimitive (canonicalCovarianceEnergy beta v)

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalArtanh
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.IsingObservationFactor
open IsingObservationInnovation PosteriorCompensatorStopping ArtanhMartingaleFormula

def canonicalResponseDrift {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : ℝ :=
  posterior beta v t x * infiniteGibbsResponseRow beta v (fun i => x i t)

def canonicalPosteriorExit {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    ℕ → Paths d → WithTop ℝ≥0 :=
  jointExit (continuousPosterior beta v) (canonicalCovarianceCompensator beta v)

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyStationarity
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyStationarity

open IsingObservationInnovation IsingObservationFactor

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem measurePreserving_copies_relabel
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d) :
    MeasurePreserving (copyRelabel g) (copies beta μ) (copies beta μ) := by
  let T := ObservationCopyStationarity.arrayRelabelEquiv (A := WienerSampler.Path) g
  have hT : MeasurePreserving T
      ((observationLaw μ).map (innovationMap beta))
      ((observationLaw μ).map (innovationMap beta)) := by
    refine ⟨measurable_relabel g, ?_⟩
    rw [map_innovationMap_observationLaw hμ]
    exact Measure.map_infinitePi_infinitePi_of_inj g.toEquiv.symm.injective
  refine ⟨measurable_copyRelabel g, ?_⟩
  exact conditionalCopies_invariant
    ((observationLaw μ).map (innovationMap beta)) (kernel beta μ) T
    (measurable_relabel g) hT
    (ObservableDisintegration.joint_kernel_invariant (observationLaw μ)
      (measurable_innovationMap beta) (measurable_relabel g)
      (measurePreserving_observationLaw_relabel hμ g) (innovationMap_relabel_ae hμ g))

theorem measurePreserving_observations :
    MeasurePreserving (fun q : Paths d × (Paths d × Paths d) => q.2.1)
      (copies beta μ) (observationLaw μ) ∧
    MeasurePreserving (fun q : Paths d × (Paths d × Paths d) => q.2.2)
      (copies beta μ) (observationLaw μ) := by
  haveI : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    Measure.isProbabilityMeasure_map (measurable_innovationMap beta).aemeasurable
  apply IsingConditionalCopyBounds.measurePreserving_observation_copies
  exact ObservableDisintegration.compProd_kernel (observationLaw μ)
    (measurable_innovationMap beta)

def sitePair (beta : ℝ) (t : ℝ≥0) (q : Paths d × (Paths d × Paths d)) :
    CavityArray.SitePair d :=
  (fun v => field beta v t q.2.1, fun v => field beta v t q.2.2)

end Problem367.IsingCopyStationarity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastOutsideCone
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

def outsideConeNoise {d : ℕ} (theta : ℝ) (b : TreeVertex d)
    (Y : OutsideConeNonroot b → ℝ) (v : TreeVertex d) : IsingSpin :=
  if hv : v.1 ≠ [] ∧ ¬ b.1 <+: v.1 then edgeNoise theta (Y ⟨v, hv⟩)
  else IsingSpin.pos

def outsideConeFactor {d : ℕ} (theta : ℝ) (b : TreeVertex d)
    (a : OutsideConeVertex b) (p : IsingSpin × (OutsideConeNonroot b → ℝ)) :
    OutsideConeVertex b → IsingSpin :=
  fun v => spinMul p.1
    (spinMul (ofNoise (outsideConeNoise theta b p.2) a.1)
      (ofNoise (outsideConeNoise theta b p.2) v.1))

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_LawSpectral
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.TreeLawKoopman

variable {d : ℕ} {A : Type*} [MeasurableSpace A]
variable (μ : Measure (TreeVertex d → A))
variable (hμ : ∀ g : TreeAut d, MeasurePreserving (relabel g) μ μ)

variable [IsFiniteMeasure μ]

def LocalCriticalDecay : Prop :=
  ∀ (s : Finset (TreeVertex d)) (f : Lp ℝ 2 μ) (F : (s → A) → ℝ),
    Measurable F → (f =ᵐ[μ] fun U => F (fun i => U i)) →
    (∫ U, f U ∂μ) = 0 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : TreeAut d,
      |inner ℝ f (koopmanL2 (relabel g) (hμ g) f)| ≤
        C * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ (g.toEquiv TreeEscape.root).1.length

end Problem367.TreeLawKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopySpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral

open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

abbrev differenceSpace (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] :=
  CopyDifference.rangeClosure (CopyDifference.operator
    (measurePreserving_observations (beta := beta) (μ := μ)).1
    (measurePreserving_observations (beta := beta) (μ := μ)).2)

def averageOnDifferences (hμ : HasFreeIsingLaw (Real.tanh beta) μ) :
    differenceSpace beta μ →L[ℝ] differenceSpace beta μ :=
  CopyDifference.averageOnDifferences
    (measurePreserving_observations (beta := beta) (μ := μ)).1
    (measurePreserving_observations (beta := beta) (μ := μ)).2
    (TreeLawKoopman.reflection (A := WienerSampler.Path))
    (fun c => copyRelabel (prefixTreeAut c))
    (fun c => measurePreserving_observationLaw_relabel hμ (prefixTreeAut c))
    (fun c => measurePreserving_copies_relabel hμ (prefixTreeAut c))
    (fun _ => rfl) (fun _ => rfl)

def differenceReflection (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (c : Fin d) :
    differenceSpace beta μ ≃ₗᵢ[ℝ] differenceSpace beta μ :=
  CopyDifference.differenceKoopmanEquiv
    (measurePreserving_observations (beta := beta) (μ := μ)).1
    (measurePreserving_observations (beta := beta) (μ := μ)).2
    (TreeLawKoopman.reflection c) (copyRelabel (prefixTreeAut c))
    (measurePreserving_observationLaw_relabel hμ (prefixTreeAut c))
    (measurePreserving_copies_relabel hμ (prefixTreeAut c))
    rfl rfl (copyReflection_involutive c)

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyObservables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity PlantedSymmetry

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem memLp_field_at
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) : MemLp (field beta v t) 2 (observationLaw μ) := by
  have hobs := (IsingConditionalCopyBounds.hasLaw_observationLaw_eval μ t).identDistrib
    (show HasLaw (observation t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) from
      ⟨(measurable_observation t).aemeasurable, rfl⟩)
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hfield := hobs.comp (ha.comp (measurable_infiniteGibbsSpinMean beta v))
  apply hfield.memLp_iff.mpr
  apply MemLp.ae_eq _ (hμ.memLp_gaussianPosteriorField_two hbeta t v)
  filter_upwards [hμ.infiniteGibbsSpinMean_eq_posterior t v] with p hp
  exact (congrArg Real.artanh hp).symm

theorem measurable_cavityObservable (hbeta : 0 ≤ beta) (t : ℝ≥0) (v w : TreeVertex d) :
    Measurable (cavityObservable hbeta t v w) :=
  (CavityArray.measurable_field_apply (tanh_nonneg_of_beta_nonneg hbeta)
    (Real.tanh_lt_one beta) v w).comp
    (Measurable.of_eval (fun vertex => measurable_field_at beta t vertex))

theorem memLp_cavityObservable
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    MemLp (cavityObservable hbeta t v w) 2 (observationLaw μ) := by
  have hd : MemLp (fun x => cavityObservable hbeta t v w x - field beta v t x) 2
      (observationLaw μ) :=
    MemLp.of_bound
      ((measurable_cavityObservable hbeta t v w).sub (measurable_field_at beta t v)).aestronglyMeasurable
      (Real.artanh (Real.tanh beta)) (Filter.Eventually.of_forall (fun x => by
        exact CavityArray.field_site_bound (tanh_nonneg_of_beta_nonneg hbeta)
          (Real.tanh_lt_one beta) (fun i => field beta i t x) v w))
  have hs := hd.add (memLp_field_at hμ hbeta t v)
  change MemLp (fun x => (cavityObservable hbeta t v w x - field beta v t x) +
    field beta v t x) 2 (observationLaw μ) at hs
  simpa only [sub_add_cancel] using hs

theorem memLp_cavityLogObservable
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    MemLp (cavityLogObservable hbeta t v w) 2 (observationLaw μ) := by
  apply memLp_log_responseAttenuation _ (memLp_cavityObservable hμ hbeta t v w)
  have h0 := tanh_nonneg_of_beta_nonneg hbeta
  have h1 := Real.tanh_lt_one beta
  nlinarith

def observableDifference {f : Paths d → ℝ} (hf : MemLp f 2 (observationLaw μ)) :
    differenceSpace beta μ :=
  CopyDifference.toRangeClosure (CopyDifference.operator
    (measurePreserving_observations (beta := beta) (μ := μ)).1
    (measurePreserving_observations (beta := beta) (μ := μ)).2) (hf.toLp f)

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CanonicalPathResponse
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem367.TreePathResponse

def orientedCavity {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (h : TreeVertex d → ℝ) (D : Finset (TreeVertex d))
    (u v : TreeVertex d) : ℝ :=
  (cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
    (field beta h D u, field beta h D v)).2

end Problem367.TreePathResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ContinuousRootResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ}

def siteRootResponse (hb : 0 ≤ beta) (v : TreeVertex d)
    (H : TreeVertex d → ℝ) : ℝ :=
  Real.tanh beta ^ v.1.length *
    ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
      (CavityArray.field (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_lt_one beta)
        H (ConnectedHull.takeVertex v (i + 1)) (ConnectedHull.takeVertex v i))

def continuousRootResponse (hb : 0 ≤ beta) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : ℝ :=
  siteRootResponse hb v (fun i => continuousField beta i t x)

def continuousRootCovariance (hb : 0 ≤ beta) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : ℝ :=
  (1 - Real.tanh (continuousField beta (ConnectedHull.root d) t x) ^ 2) *
    continuousRootResponse hb v t x

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalClippedWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation ArtanhMartingaleFormula
open PosteriorStoppingTimes PosteriorCompensatorStopping

def canonicalClippedWeight {d : ℕ} (beta : ℝ) (n : ℕ)
    (t : ℝ≥0) (x : Paths d) : ℝ :=
  ClippedArtanhWeight.weight (threshold n)
    (continuousPosterior beta (ConnectedHull.root d) t x)

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CommonStopBounds
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy PosteriorCompensatorStopping

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def copyResponseDriftDifference (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (q : Joint d) : ℝ :=
  posterior beta v t q.2.1 * copyResponseEnergy beta v true t q -
    posterior beta v t q.2.2 * copyResponseEnergy beta v false t q

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ContinuousCopyCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingContinuousCopyCoefficients
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy

variable {d : ℕ} {beta : ℝ}

def response (hb : 0 ≤ beta) (j : Bool) (v : TreeVertex d)
    (t : ℝ≥0) (q : Joint d) : ℝ :=
  continuousRootResponse hb v t (projection j q)

end Problem367.IsingContinuousCopyCoefficients

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ContinuousCopyDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingContinuousCopyDensity
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy

variable {d : ℕ} {beta : ℝ}

def response (hb : 0 ≤ beta) (v : TreeVertex d) (j : Bool)
    (t : ℝ≥0) (q : Joint d) : ℝ :=
  continuousRootResponse hb v t (projection j q)

def continuousDensity (hb : 0 ≤ beta) (t : ℝ≥0) : Joint d → ℝ :=
  DiscrepancyEnergy.density (fun v => response hb v true t)
    (fun v => response hb v false t) (continuousDifference beta (ConnectedHull.root d) t)
    (copyContinuousPosterior beta (ConnectedHull.root d) true t)
    (copyContinuousPosterior beta (ConnectedHull.root d) false t)

end Problem367.IsingContinuousCopyDensity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyEdgeCorrelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor ColoredEdgeLifts

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def cavityLogEdgeVector
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (t : ℝ≥0) :
    EdgeSpace d (differenceSpace beta μ) :=
  WithLp.toLp 2 (fun c => observableDifference (beta := beta)
    (memLp_cavityLogObservable hμ hbeta t TreeEscape.root (prefixFlip c TreeEscape.root)))

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyGeodesicCorrelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def cavityLogVector
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) : differenceSpace beta μ :=
  observableDifference (beta := beta) (memLp_cavityLogObservable hμ hbeta t v w)

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyPathBounds
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingCopyPathBounds

open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def edgeLogDifference (hbeta : 0 ≤ beta) (t : ℝ≥0) (v w : TreeVertex d)
    (q : IsingConditionalCopyBounds.CopySpace d) : ℝ :=
  Real.log (responseAttenuation (Real.tanh beta)
    (CavityArray.field (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (sitePair beta t q).1 v w)) -
  Real.log (responseAttenuation (Real.tanh beta)
    (CavityArray.field (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (sitePair beta t q).2 v w))

def pathLogDifference {ι : Type*} (hbeta : 0 ≤ beta) (t : ℝ≥0)
    (s : Finset ι) (e : ι → TreeVertex d × TreeVertex d)
    (q : IsingConditionalCopyBounds.CopySpace d) : ℝ :=
  ∑ i ∈ s, edgeLogDifference hbeta t (e i).1 (e i).2 q

end Problem367.IsingCopyPathBounds

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopySquareDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySquareDensity
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy
open IsingContinuousCopyDensity StoppedTimePrimitive

variable {d : ℕ} {beta : ℝ}

def noise (hb : 0 ≤ beta) (t : ℝ≥0) (q : Joint d) : ℝ :=
  ∑' v, (response hb v true t q - response hb v false t q) ^ 2

def drift (beta : ℝ) (t : ℝ≥0) (q : Joint d) : ℝ :=
  canonicalResponseDrift beta (ConnectedHull.root d) t (projection true q) -
    canonicalResponseDrift beta (ConnectedHull.root d) t (projection false q)

end Problem367.IsingCopySquareDensity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_JoinedResponseIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingJoinedResponseIntegrals
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy
open IsingContinuousCopyCoefficients BrownianArrayFiltration

variable {d : ℕ} {beta : ℝ}

structure IntegralSystem (hb : 0 ≤ beta)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] where
  channel : Bool → TreeVertex d → ℝ≥0 → Joint d → ℝ
  total : Bool → ℝ≥0 → Joint d → ℝ
  channel_memLp : ∀ j v t, MemLp (channel j v t) 2 (copies beta μ)
  total_memLp : ∀ j t, MemLp (total j t) 2 (copies beta μ)
  channel_predictable : ∀ j v, IsStronglyPredictable
    ContinuousCopyBrownian.joinedFiltration (channel j v)
  channel_martingale : ∀ j v, Martingale (channel j v)
    ContinuousCopyBrownian.joinedFiltration (copies beta μ)
  channel_continuous : ∀ j v, ∀ᵐ q ∂copies beta μ,
    Continuous (fun t => channel j v t q)
  channel_limit : ∀ j v (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
    Tendsto (fun n => ∫ q,
      (BrownianIntegralProcess.stoppedUniformSum
        (fun s (p : Joint d) => p.1 v s) (response hb j v) N n t q -
          channel j v t q) ^ 2 ∂copies beta μ) atTop (𝓝 0)
  total_predictable : ∀ j, IsStronglyPredictable
    ContinuousCopyBrownian.joinedFiltration (total j)
  total_martingale : ∀ j, Martingale (total j)
    ContinuousCopyBrownian.joinedFiltration (copies beta μ)
  total_continuous : ∀ j, ∀ᵐ q ∂copies beta μ, Continuous (fun t => total j t q)
  total_zero : ∀ j, total j 0 =ᵐ[copies beta μ] 0
  total_sum : ∀ j t, HasSum (fun v => (channel_memLp j v t).toLp (channel j v t))
    ((total_memLp j t).toLp (total j t))
  difference_compensatedSquare : Martingale (fun t q =>
    (total true t q - total false t q) ^ 2 -
      nnrealTimePrimitive (spatialSquareDensity
        (fun v s p => response hb true v s p - response hb false v s p)) t q)
    ContinuousCopyBrownian.joinedFiltration (copies beta μ)

end Problem367.IsingJoinedResponseIntegrals

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_OrientedPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyPathBounds ConnectedHull

def logSum {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta) (t : ℝ≥0)
    (inward : Bool) (v : TreeVertex d) (s : Finset ℕ) :
    IsingConditionalCopyBounds.CopySpace d → ℝ :=
  pathLogDifference hb t s (edge inward v)

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_RootGaussianCut
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem367.IsingRootGaussianCut

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds
open TreeOrbitAverage IsingCopyWeightedCut IsingRootAttenuation IsingRootWeightedCut
open PlantedSymmetry CavityFieldLimit PathSideBranches

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def terminalAttenuation (hbeta : 0 ≤ beta) (v : TreeVertex d)
    (y : TreeVertex d → ℝ) : ℝ :=
  ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
    (infiniteCavityField hbeta (ConnectedHull.takeVertex v (i + 1))
      (ConnectedHull.takeVertex v i) y)

def terminalExtensionAverage (hbeta : 0 ≤ beta) (stem : List (Fin d))
    (n k : ℕ) : (TreeVertex d → ℝ) → ℝ :=
  WeightedOrbitAverage.average (fun s : Extension stem n => fun y =>
    terminalAttenuation hbeta (endpoint s) y ^ k)

end Problem367.IsingRootGaussianCut

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_OrientedGaussianTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral IsingConditionalCopyBounds
open TreeOrbitAverage PlantedSymmetry CavityFieldLimit PathSideBranches

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def terminalAttenuation (hb : 0 ≤ beta) (inward : Bool) (v : TreeVertex d)
    (y : TreeVertex d → ℝ) : ℝ :=
  ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
    (infiniteCavityField hb (edge inward v i).1 (edge inward v i).2 y)

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_OrientedNoiseSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyPathBounds IsingCopyWeightedCut

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def weightedLogEnergy (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    (v : TreeVertex d) (s : Finset ℕ) (left : Bool) : ℝ :=
  ∫ q, logSum hb t inward v s q ^ 2 *
    attenuation hb t inward v (observationCopy left q) ^ 2 ∂copies beta μ

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_StoppedSquareAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy IsingContinuousCopyCoefficients

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def copyResponseNoiseEnergy (hb : 0 ≤ beta) (t : ℝ≥0) (z : Joint d) : ℝ :=
  ∑' v : TreeVertex d, (response hb true v t z - response hb false v t z) ^ 2

end Problem367.IsingObservationFactor

end

end OAI
end


