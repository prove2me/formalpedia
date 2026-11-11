-- Prove2me | Definitions.Def_Q243FI004
-- name    : Q243FI004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T01:40:13.197017+00:00
-- url     : https://prove2.me/theorems/6db7926b-949a-4e2b-9f49-97ca8119878d
-- title:
--   Definitions bundle Q243FI004 of the split of OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 202 declarations of OpenAI's Lean: 124 definitions, 4 instances and 74 theorems. The definitions and types are `OAI.Problem367.InhomogeneousChain.expectation`, `OAI.Problem367.InwardCutChannels.inwardContinuationAverage`, `OAI.Problem367.InwardCutChannels.inwardContinuationProduct`, `OAI.Problem367.InwardCutChannels.regionAverage`, `OAI.Problem367.InwardCutChannels.regionProduct`, `OAI.Problem367.IsingConditionalCopyBounds.graphLaw`, `OAI.Problem367.IsingCopyEnergy.projection`, `OAI.Problem367.IsingCopyEnergy.timeProjection`, `OAI.Problem367.IsingCopyOrbitAverage.copyAction`, `OAI.Problem367.IsingCopyResponseRowPaths.linearEnergy`, `OAI.Problem367.IsingCopyResponseRowPaths.linearShellEnergy`, `OAI.Problem367.IsingCopyResponseRowPaths.noiseEnergy`, `OAI.Problem367.IsingCopyResponseRowPaths.noiseShellEnergy`, `OAI.Problem367.IsingCopyResponseRowPaths.pathCavity`, `OAI.Problem367.IsingCopyResponseRowPaths.row`, `OAI.Problem367.IsingCopySmallLogLoss.logVariance`, `OAI.Problem367.IsingCopySpectral.cavityLogDifference`, `OAI.Problem367.IsingCopySpectral.cavityLogObservable`, `OAI.Problem367.IsingCopySpectral.pathCavityLogSum`, `OAI.Problem367.IsingCopySpectral.pathCavityProduct`, `OAI.Problem367.IsingCopyStationarity.copyRelabel`, `OAI.Problem367.IsingCopyWeightedCut.observationCopy`, `OAI.Problem367.IsingInnovation.covariance`, `OAI.Problem367.IsingInnovation.finiteCovariance`, `OAI.Problem367.IsingObservationInnovation.futureInnovation`, `OAI.Problem367.IsingObservationInnovation.past`, `OAI.Problem367.IsingObservationInnovation.uniformObservationChannel`, `OAI.Problem367.IsingObservationRecovery.decode`, `OAI.Problem367.IsingOrientedPath.extensionAverage`, `OAI.Problem367.IsingOrientedPath.orderedEdgeFactor`, `OAI.Problem367.IsingOrientedPath.orientedGaussianFactor`, `OAI.Problem367.IsingOrientedPath.restrictedAverage`, `OAI.Problem367.IsingRootWeightedCut.extensionAverage`, `OAI.Problem367.IsingWalk.treeEigenWeight`, `OAI.Problem367.LeafGibbs.energy`, `OAI.Problem367.NoisyLawSpectral.law`, `OAI.Problem367.NoisyLocalCovariance.averageBlock`, `OAI.Problem367.NoisyLocalCovariance.noiseLaw`, `OAI.Problem367.NoisyRootOtherData`, `OAI.Problem367.NormalizedInfiniteTimeEnergy.infiniteRow` and 84 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `FreeIsing_Brownian_PosteriorField`, `FreeIsing_Conditioning_BroadcastFamilyConditional`, `FreeIsing_Conditioning_ComponentConditionalRecursionInputs`, `FreeIsing_Conditioning_ObservationCopyStationarity`, `FreeIsing_Energy_Attenuation`, `FreeIsing_Energy_ComponentCovariance`, `FreeIsing_Energy_CoupledAttenuation`, `FreeIsing_Energy_CoupledResponseRows`, `FreeIsing_Energy_FiniteIsingEnergyLimit`, `FreeIsing_Energy_FiniteLeafCovariance`, `FreeIsing_Energy_NoisyLocalCovariance`, `FreeIsing_Energy_NormalizedInfiniteTimeEnergy`, `FreeIsing_Energy_ProgressiveIsingCovariance`, `FreeIsing_Energy_SelectedCriticalFieldMoments`, `FreeIsing_Estimates_ComponentFusionRecurrence`, `FreeIsing_Estimates_ComponentPairCount`, `FreeIsing_Estimates_FiniteComponentGeometry`, `FreeIsing_Estimates_FreeIsingMeasure`, `FreeIsing_Estimates_InhomogeneousSpinChain`, `FreeIsing_Estimates_ObservableDisintegration`, `FreeIsing_Estimates_ProgressiveVersionPushforward`, `FreeIsing_Estimates_RadialRepresentation`, `FreeIsing_Estimates_RadialSummability`, `FreeIsing_Estimates_RadialWalk`, `FreeIsing_Gaussian_CutChannels`, `FreeIsing_Gaussian_FiniteSignalInformation`, `FreeIsing_Gaussian_InwardGaussianCutChannels`, `FreeIsing_Gaussian_InwardProducts`, `FreeIsing_Gibbs_CovarianceL2Limit`, `FreeIsing_Gibbs_PosteriorSymmetry`, `FreeIsing_Ising_ConditionalCopyBounds`, `FreeIsing_Ising_CopyEnergyIntegrability`, `FreeIsing_Ising_CopyGeodesicCorrelations`, `FreeIsing_Ising_CopyObservables`, `FreeIsing_Ising_CopyOrbitAverage`, `FreeIsing_Ising_CopyProductPathBound`, `FreeIsing_Ising_CopyResponseRowPaths`, `FreeIsing_Ising_CopyShellEnergies`, `FreeIsing_Ising_CopySmallLogLoss`, `FreeIsing_Ising_CopySpectral`, `FreeIsing_Ising_CopyStationarity`, `FreeIsing_Ising_CopyWeightedCut`, `FreeIsing_Ising_InnovationLaw`, `FreeIsing_Ising_MixedFiltering`, `FreeIsing_Ising_ObservationFactor`, `FreeIsing_Ising_ObservationIndependence`, `FreeIsing_Ising_ObservationLaw`, `FreeIsing_Ising_ObservationPosteriorTransport`, `FreeIsing_Ising_ObservationRecovery`, `FreeIsing_Ising_OrientedGaussianTail`, `FreeIsing_Ising_OrientedPathWeights`, `FreeIsing_Ising_RootWeightedCut`, `FreeIsing_Ising_StemRerootAverage`, `FreeIsing_Ising_WalkObstruction`, `FreeIsing_Posterior_BranchObservationRegression`, `FreeIsing_Posterior_ComponentPosteriorStationarity`, `FreeIsing_Posterior_FieldMoments`, `FreeIsing_Posterior_NormalizedPosteriorLimit`, `FreeIsing_Posterior_ObservationLawSpectral`, `FreeIsing_Posterior_PathPosteriorResponse`, `FreeIsing_Posterior_PlantedBridgeVector`, `FreeIsing_Posterior_PlantedStationarity`, `FreeIsing_Posterior_PlantedSufficiencyVector`, `FreeIsing_Posterior_ProgressiveIsingPosterior`, `FreeIsing_Posterior_SelectedPosteriorLimit`, `FreeIsing_Posterior_SelectedPosteriorStationarity`, `FreeIsing_Posterior_SelectedPosteriorSymmetry`, `FreeIsing_Posterior_Symmetry`, `FreeIsing_Spectral_KoopmanInvolutions`, `FreeIsing_Spectral_NoisyLawSpectral`, `FreeIsing_Spins_Chain`, `FreeIsing_Spins_Flip`, `FreeIsing_Stochastic_WienerSampler`, `FreeIsing_Trees_BroadcastBranchLabels`, `FreeIsing_Trees_BroadcastConeLocality`, `FreeIsing_Trees_BroadcastConeMarkov`, `FreeIsing_Trees_BroadcastLocality`, `FreeIsing_Trees_ConnectedExhaustion`, `FreeIsing_Trees_CutContinuations`, `FreeIsing_Trees_CutLevelBranchIndependence`, `FreeIsing_Trees_InnovationPathMap`, `FreeIsing_Trees_InwardCutChannels`, `FreeIsing_Trees_InwardCutFields`, `FreeIsing_Trees_LawSpectral`, `FreeIsing_Trees_NoisyBranchSeparation`, `FreeIsing_Trees_NoisyConeSeparation`, `FreeIsing_Trees_NoisyCutLevelIndependence`, `FreeIsing_Trees_OrbitAverage`, `FreeIsing_Trees_PathGibbs`, `FreeIsing_Trees_PathRerooting`, `FreeIsing_Trees_PathSideBranches`, `FreeIsing_Trees_ResponseRowEnergy`, `FreeIsing_Trees_RootedBroadcast`, `FreeIsing_Trees_RootedBroadcastLaw`, `FreeIsing_Trees_SelectedInwardPathAttenuation`, `FreeIsing_Trees_SelectedPathAttenuation`, `FreeIsing_Trees_SelectedPathLocality`, `FreeIsing_Trees_Shells`, `FreeIsing_Trees_StemRerootAverage`, `FreeIsing_Trees_SubcriticalPathSums`, `FreeIsing_Trees_WordAction`.
--
--   **Imports.** It imports the published bundle `Def_FreeIsing`; the bundles `Q243FI000` and `Q243FI001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q243FI005`; the statements `OAI.Problem367.HasFreeIsingLaw.finiteGibbsCovariance_windowEnergy_eq`, `OAI.Problem367.HasFreeIsingLaw.gaussianComponentField_critical_base_moments`, `OAI.Problem367.HasFreeIsingLaw.gaussian_component_field_recursion`, `OAI.Problem367.HasFreeIsingLaw.gaussian_root_information_le_component`, `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq`, `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsCovariance_windowEnergy_eq`, `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_zero`, `OAI.Problem367.HasFreeIsingLaw.selectedPosterior_root_component`, `OAI.Problem367.HasFreeIsingLaw.selected_child_parent_abs_le`, `OAI.Problem367.HasFreeIsingLaw.selected_child_parent_secondMoment`, `OAI.Problem367.IsingCopyEnergy.copy_row_energy_integrable`, `OAI.Problem367.IsingCopyResponseRowPaths.copies_rows_summable_ae`, `OAI.Problem367.IsingCopyResponseRowPaths.critical_root_variance_zero_of_noise_bound`, `OAI.Problem367.IsingCopyResponseRowPaths.exists_actual_spatial_endpoint_constant`, `OAI.Problem367.IsingCopyResponseRowPaths.exists_noise_energy_long_constants`, `OAI.Problem367.IsingCopyResponseRowPaths.integral_actual_density_le_path_sums`, `OAI.Problem367.IsingCriticalSmallLogLoss.exists_critical_small_log_bounds`, `OAI.Problem367.IsingInnovation.exists_continuous_covariance_integral`, `OAI.Problem367.IsingInnovation.exists_posterior_integral_representation`, `OAI.Problem367.IsingInnovation.finiteCovariance_fullTime_interval_energy_cauchy`, `OAI.Problem367.IsingInnovation.tendsto_trial_cross_uniformSum`, `OAI.Problem367.IsingOrientedPath.measure_extensionAverage_gt_le_double_exp_common`, `OAI.Problem367.IsingRootDoubleExponential.integral_root_weight_mul_sq_le_double_exp`, `OAI.Problem367.exists_gaussianComponentField_critical_moment_tail`, `OAI.Problem367.free_ising_factor_below_threshold_of_actual_variance_identity`, `OAI.Problem367.integral_cutContinuationProduct_gaussianConeFactor_le`, `OAI.Problem367.measure_gaussian_inward_path_average_ge_le` and `OAI.Problem367.measure_gaussian_inward_restricted_path_average_ge_le_double_exp`; the proofs of `OAI.Problem367.ComponentSignalAttenuation.condDistrib_posteriorMean_root`, `OAI.Problem367.ComponentSignalAttenuation.condExp_attenuation_le_critical_of_condIndep`, `OAI.Problem367.HasFreeIsingLaw.selectedPosterior_root_component`, `OAI.Problem367.HasFreeIsingLaw.selected_child_parent_abs_le`, `OAI.Problem367.HasFreeIsingLaw.selected_child_parent_secondMoment`, `OAI.Problem367.condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss` and `OAI.Problem367.free_ising_factor_iff_threshold`.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI000
import Definitions.Def_Q243FI001

section
-- module Solutions.Q243_FreeIsing.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Flip
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem IsingSpin.measurable_flip : Measurable IsingSpin.flip := by
  intro s hs
  trivial

theorem measurable_flipConfig {ι : Type*} :
    Measurable (flipConfig : (ι → IsingSpin) → (ι → IsingSpin)) := by
  exact Measurable.of_eval (fun vertex =>
    IsingSpin.measurable_flip.comp (measurable_pi_apply vertex))

def flipConfigMeasurableEquiv (ι : Type*) : (ι → IsingSpin) ≃ᵐ (ι → IsingSpin) where
  toFun := flipConfig
  invFun := flipConfig
  left_inv := flipConfig_flipConfig
  right_inv := flipConfig_flipConfig
  measurable_toFun := measurable_flipConfig
  measurable_invFun := measurable_flipConfig

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_Symmetry
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace Problem367.PlantedSymmetry

def plantedFlipEquiv (ι : Type*) :
    ((ι → IsingSpin) × (ι → ℝ)) ≃ᵐ ((ι → IsingSpin) × (ι → ℝ)) where
  toFun := Prod.map flipConfig Neg.neg
  invFun := Prod.map flipConfig Neg.neg
  left_inv := by
    rintro ⟨sigma, noise⟩
    change (flipConfig (flipConfig sigma), - -noise) = (sigma, noise)
    simp
  right_inv := by
    rintro ⟨sigma, noise⟩
    change (flipConfig (flipConfig sigma), - -noise) = (sigma, noise)
    simp
  measurable_toFun := measurable_flipConfig.prodMap measurable_neg
  measurable_invFun := measurable_flipConfig.prodMap measurable_neg

theorem integrable_plantedSpin {ι : Type*}
    (rho : Measure ((ι → IsingSpin) × (ι → ℝ))) [IsFiniteMeasure rho] (v : ι) :
    Integrable (fun p => spinSign (p.1 v)) rho := by
  have hsign : Measurable spinSign := by intro s hs; trivial
  apply Integrable.of_bound
    ((hsign.comp ((measurable_pi_apply v).comp measurable_fst)).aestronglyMeasurable) 1
  apply Filter.Eventually.of_forall
  intro p
  cases hs : p.1 v <;> norm_num [spinSign, hs]

def posteriorMagnetization {ι : Type*}
    (rho : Measure ((ι → IsingSpin) × (ι → ℝ))) (t : ℝ) (v : ι) :
    ((ι → IsingSpin) × (ι → ℝ)) → ℝ :=
  rho[fun p => spinSign (p.1 v) | observationSigma ι t]

theorem posteriorMagnetization_abs_le_one {ι : Type*}
    (rho : Measure ((ι → IsingSpin) × (ι → ℝ))) (t : ℝ) (v : ι) :
    ∀ᵐ p ∂rho, |posteriorMagnetization rho t v p| ≤ 1 := by
  apply ae_bdd_abs_condExp_of_ae_bdd_abs
  apply Filter.Eventually.of_forall
  intro p
  cases hs : p.1 v <;> norm_num [spinSign, hs]

end Problem367.PlantedSymmetry

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Shells
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem monotone_treeBallFinset (d : ℕ) : Monotone (treeBallFinset d) := by
  intro n m hnm v hv
  exact (mem_treeBallFinset d m v).mpr (((mem_treeBallFinset d n v).mp hv).trans hnm)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ConnectedExhaustion
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem eventually_mem_connectedExhaustion {d : ℕ} (v w : TreeVertex d) :
    ∀ᶠ n in Filter.atTop, w ∈ connectedExhaustion v n := by
  classical
  filter_upwards [Filter.eventually_ge_atTop w.1.length] with n hn
  exact ConnectedHull.subset_hull _ (Finset.mem_insert_of_mem
    ((mem_treeBallFinset d n w).mpr hn))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_Attenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma abs_deriv_log_responseAttenuation_le {theta : ℝ}
    (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    |deriv (fun x => Real.log (responseAttenuation theta x)) z| ≤ 2 * |Real.tanh z| := by
  rw [(hasDerivAt_log_responseAttenuation hθ z).deriv]
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (attenuation_denominator_pos hθ z),
    abs_of_nonneg (sub_nonneg.mpr hθ)]
  norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [div_le_iff₀ (attenuation_denominator_pos hθ z)]
  have hp := mul_le_mul_of_nonneg_left (le_of_lt (Real.tanh_sq_lt_one z)) (sq_nonneg theta)
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (Real.tanh z))
  nlinarith

lemma abs_deriv_log_responseAttenuation_le_two {theta : ℝ}
    (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    |deriv (fun x => Real.log (responseAttenuation theta x)) z| ≤ 2 := by
  exact (abs_deriv_log_responseAttenuation_le hθ z).trans
    (by nlinarith [Real.abs_tanh_lt_one z])

lemma lipschitzWith_log_responseAttenuation {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    LipschitzWith 2 (fun x => Real.log (responseAttenuation theta x)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_log_responseAttenuation hθ x).differentiableAt
  · intro x
    exact_mod_cast abs_deriv_log_responseAttenuation_le_two hθ x

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PlantedBridgeVector
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

lemma comap_vector_past_eq_endpoint_bridges
    {ι Omega : Type*} (B : ι → ℝ≥0 → Omega → ℝ) (T : ℝ≥0) :
    MeasurableSpace.comap (fun w i (s : Set.Iic T) => B i s w) inferInstance =
      MeasurableSpace.comap
        (fun w => (fun i => B i T w,
          fun i (s : Set.Iic T) => brownianBridge (B i) T s w)) inferInstance := by
  apply le_antisymm
  · let : MeasurableSpace Omega := MeasurableSpace.comap
      (fun w => (fun i => B i T w,
        fun i (s : Set.Iic T) => brownianBridge (B i) T s w)) inferInstance
    apply Measurable.comap_le
    have hm : Measurable
        (fun w => (fun i => B i T w,
          fun i (s : Set.Iic T) => brownianBridge (B i) T s w)) := comap_measurable _
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro s
    have hb := (measurable_pi_apply s).comp
      ((measurable_pi_apply i).comp (measurable_snd.comp hm))
    have ht := (measurable_pi_apply i).comp (measurable_fst.comp hm)
    convert hb.add (ht.const_mul ((s : ℝ≥0) / (T : ℝ))) using 1
    all_goals try with_reducible_and_instances rfl
    funext w
    simp [brownianBridge]
  · let : MeasurableSpace Omega :=
      MeasurableSpace.comap (fun w i (s : Set.Iic T) => B i s w) inferInstance
    apply Measurable.comap_le
    have hm : Measurable (fun w i (s : Set.Iic T) => B i s w) := comap_measurable _
    have ht (i : ι) : Measurable (B i T) :=
      (measurable_pi_apply (⟨T, by simp⟩ : Set.Iic T)).comp
        ((measurable_pi_apply i).comp hm)
    apply (Measurable.of_eval ht).prodMk
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro s
    exact ((measurable_pi_apply s).comp ((measurable_pi_apply i).comp hm)).sub
      ((ht i).const_mul _)

lemma comap_planted_vector_past_eq_terminal_bridges
    {ι S Omega : Type*} (B : ι → ℝ≥0 → Omega → ℝ)
    (sigma : S → ι → ℝ) {T : ℝ≥0} (hT : T ≠ 0) :
    MeasurableSpace.comap
      (fun q : S × (ι → Omega) => fun i (s : Set.Iic T) =>
        (s : ℝ≥0) * sigma q.1 i + B i s (q.2 i)) inferInstance =
    MeasurableSpace.comap
      (fun q : S × (ι → Omega) =>
        (fun i => (T : ℝ) * sigma q.1 i + B i T (q.2 i),
          fun i (s : Set.Iic T) => brownianBridge (B i) T s (q.2 i))) inferInstance := by
  rw [comap_vector_past_eq_endpoint_bridges
    (fun i t (q : S × (ι → Omega)) => (t : ℝ) * sigma q.1 i + B i t (q.2 i)) T]
  congr 1
  funext q
  congr 1
  funext i s
  exact brownianBridge_add_drift
    (fun t (q : S × (ι → Omega)) => B i t (q.2 i))
    (fun q => sigma q.1 i) hT s q

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

theorem comap_array_past_zero {ι Ω E : Type*} [MeasurableSpace E]
    (X : Ω → ℝ≥0 → ι → E) :
    MeasurableSpace.comap
      (fun ω i (s : Set.Iic (0 : ℝ≥0)) => X ω s i) inferInstance =
    MeasurableSpace.comap (fun ω i => X ω 0 i) inferInstance := by
  apply le_antisymm
  · let : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun ω i => X ω 0 i) inferInstance
    apply Measurable.comap_le
    have h : Measurable (fun ω i => X ω 0 i) := comap_measurable _
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro s
    have hs : (s : ℝ≥0) = 0 := le_antisymm s.property bot_le
    simpa only [hs, Function.comp_def] using (measurable_pi_apply i).comp h
  · let : MeasurableSpace Ω := MeasurableSpace.comap
      (fun ω i (s : Set.Iic (0 : ℝ≥0)) => X ω s i) inferInstance
    apply Measurable.comap_le
    have h : Measurable (fun ω i (s : Set.Iic (0 : ℝ≥0)) => X ω s i) :=
      comap_measurable _
    apply Measurable.of_eval
    intro i
    exact (measurable_pi_apply (⟨0, by simp⟩ : Set.Iic (0 : ℝ≥0))).comp
      ((measurable_pi_apply i).comp h)

theorem condExp_planted_array_past_eq_terminal_of_indep
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (ξ : Measure (ι → Ω))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    {B : ι → ℝ≥0 → Ω → ℝ} (hmB : ∀ i t, Measurable (B i t))
    (signal : S → ι → ℝ) (f : S → ℝ)
    (hSignal : Measurable signal) (hf : Measurable f) (hfint : Integrable f ν)
    {T : ℝ≥0} (hT : T ≠ 0)
    (hindep : IndepFun
      (fun q : S × (ι → Ω) =>
        (q.1, fun i => (T : ℝ) * signal q.1 i + B i T (q.2 i)))
      (fun q i (s : Set.Iic T) => brownianBridge (B i) T s (q.2 i))
      (ν.prod ξ)) :
    (ν.prod ξ)[(fun q : S × (ι → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (ι → Ω) => fun i (s : Set.Iic T) =>
          (s.1 : ℝ) * signal q.1 i + B i s.1 (q.2 i)) inferInstance] =ᵐ[ν.prod ξ]
    (ν.prod ξ)[(fun q : S × (ι → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (ι → Ω) => fun i =>
          (T : ℝ) * signal q.1 i + B i T (q.2 i)) inferInstance] := by
  let Y : S × (ι → Ω) → ι → ℝ :=
    fun q i => (T : ℝ) * signal q.1 i + B i T (q.2 i)
  let R : S × (ι → Ω) → ι → Set.Iic T → ℝ :=
    fun q i s => brownianBridge (B i) T s (q.2 i)
  have hYm : Measurable Y := by
    apply Measurable.of_eval
    intro i
    exact ((((measurable_pi_apply i).comp hSignal).comp measurable_fst).const_mul _).add
      ((hmB i T).comp ((measurable_pi_apply i).comp measurable_snd))
  have hRm : Measurable R := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro s
    exact ((hmB i s).comp ((measurable_pi_apply i).comp measurable_snd)).sub
      (((hmB i T).comp ((measurable_pi_apply i).comp measurable_snd)).const_mul _)
  have hInd : IndepFun (fun q : S × (ι → Ω) => (f q.1, Y q)) R (ν.prod ξ) := by
    have hm : Measurable (fun q : S × (ι → ℝ) => (f q.1, q.2)) :=
      (hf.comp measurable_fst).prodMk measurable_snd
    simpa only [Function.comp_def, id_eq] using hindep.comp hm measurable_id
  apply condExp_observation_eq_statistic (ν.prod ξ) (fun q => f q.1) Y R _
    (hf.comp measurable_fst) hYm hRm (hfint.comp_fst ξ) hInd
  rw [Problem367.comap_planted_vector_past_eq_terminal_bridges B signal hT]
  exact MeasurableSpace.comap_prodMk Y R

end Problem367.TerminalSufficiency

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_PosteriorField
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367

open PlantedSymmetry

theorem brownian_array_eval_measurePreserving
    {ι Ω : Type*} [MeasurableSpace Ω] (ν : ι → Measure Ω)
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) :
    MeasurePreserving (fun ω i => B i t (ω i))
      (Measure.infinitePi ν) (gaussianNoiseLaw ι t) := by
  have (i : ι) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  refine ⟨Measurable.of_eval (fun i => (hmB i t).comp (measurable_pi_apply i)), ?_⟩
  rw [Measure.infinitePi_map_pi ν (fun i => hmB i t)]
  congr 1
  funext i
  exact (hB i).hasLaw_eval t |>.map_eq

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcast
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

attribute [local instance] OAI.Problem367.RootedBroadcast.rootedBroadcastMeasurableSingletonSpin
lemma measurable_spinMul : Measurable (fun p : IsingSpin × IsingSpin => spinMul p.1 p.2) :=
  measurable_of_finite _

def biasedSpin (p u : ℝ) : IsingSpin :=
  if u ≤ p then IsingSpin.pos else IsingSpin.neg

lemma measurable_biasedSpin (p : ℝ) : Measurable (biasedSpin p) := by
  exact measurable_const.ite measurableSet_Iic measurable_const

abbrev parent {d : ℕ} (v : TreeVertex d) : TreeVertex d := parentVertex v

def ofNoise {d : ℕ} (noise : TreeVertex d → IsingSpin) (v : TreeVertex d) : IsingSpin :=
  if _h : v.val = [] then noise v
  else spinMul (noise v) (ofNoise noise (parent v))
termination_by v.val.length
decreasing_by
  simp only [parent, parentVertex, List.length_dropLast]
  have : 0 < v.val.length := List.length_pos_iff.mpr _h
  omega

lemma ofNoise_nonroot {d : ℕ} (noise : TreeVertex d → IsingSpin) (v : TreeVertex d)
    (hv : v.val ≠ []) :
    ofNoise noise v = spinMul (noise v) (ofNoise noise (parent v)) := by
  rw [ofNoise, dite_eq_right hv]

lemma measurable_ofNoise_apply {d : ℕ} (v : TreeVertex d) :
    Measurable (fun noise : TreeVertex d → IsingSpin => ofNoise noise v) := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      Measurable (fun noise : TreeVertex d → IsingSpin => ofNoise noise v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · have heq : (fun noise : TreeVertex d → IsingSpin => ofNoise noise v) =
            (fun noise => noise v) := by
          funext noise
          rw [ofNoise]
          simp [hnil]
        rw [heq]
        exact measurable_pi_apply v
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        have hm := ih _ hlt (parent v) rfl
        have heq : (fun noise : TreeVertex d → IsingSpin => ofNoise noise v) =
            (fun noise => spinMul (noise v) (ofNoise noise (parent v))) := by
          funext noise
          exact ofNoise_nonroot noise v hnil
        rw [heq]
        exact measurable_spinMul.comp ((measurable_pi_apply v).prodMk hm)
  exact h _ v rfl

lemma measurable_ofNoise (d : ℕ) : Measurable (@ofNoise d) := by
  exact Measurable.of_eval measurable_ofNoise_apply

def noiseFromSpins {d : ℕ} (x : TreeVertex d → IsingSpin) (v : TreeVertex d) : IsingSpin :=
  if v.val = [] then x v else spinMul (x v) (x (parent v))

def edgeNoise (theta : ℝ) : ℝ → IsingSpin := biasedSpin ((1 + theta) / 2)

lemma measurable_edgeNoise (theta : ℝ) : Measurable (edgeNoise theta) :=
  measurable_biasedSpin _

def inputNoise {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ) (v : TreeVertex d) : IsingSpin :=
  if v.val = [] then fairSpin (U v) else edgeNoise theta (U v)

lemma measurable_inputNoise (d : ℕ) (theta : ℝ) : Measurable (@inputNoise d theta) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v.val = []
  · simpa only [inputNoise, ite_eq_left hv, Function.comp_def] using measurable_fairSpin.comp (measurable_pi_apply v)
  · simpa only [inputNoise, ite_eq_right hv, Function.comp_def] using (measurable_edgeNoise theta).comp (measurable_pi_apply v)

def factor {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ) : TreeVertex d → IsingSpin :=
  ofNoise (inputNoise theta U)

lemma measurable_factor (d : ℕ) (theta : ℝ) : Measurable (@factor d theta) :=
  (measurable_ofNoise d).comp (measurable_inputNoise d theta)

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcastLaw
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

local instance rootedBroadcastLawMeasurableSingletonSpin_r69a824_1 : MeasurableSingletonClass IsingSpin :=
  ⟨fun _ => trivial⟩
def eraseRootNoise {d : ℕ} (noise : TreeVertex d → IsingSpin) (v : TreeVertex d) : IsingSpin :=
  if v.val = [] then IsingSpin.pos else noise v

abbrev NonrootVertex (d : ℕ) := {v : TreeVertex d // v ≠ root d}

def nonrootNoise {d : ℕ} (theta : ℝ) (Y : NonrootVertex d → ℝ) (v : TreeVertex d) : IsingSpin :=
  if hv : v = root d then IsingSpin.pos else edgeNoise theta (Y ⟨v, hv⟩)

def rootlessFactor {d : ℕ} (theta : ℝ) (Y : NonrootVertex d → ℝ) : TreeVertex d → IsingSpin :=
  ofNoise (nonrootNoise theta Y)

def edgeVertex {d : ℕ} (D : Finset (TreeVertex d)) (e : inducedEdges D) : NonrootVertex d := by
  classical
  refine ⟨e.val.2, ?_⟩
  intro heq
  have hlt := (Finset.mem_filter.mp e.property).2.2
  rw [heq, root_val] at hlt
  simp only [List.length_nil] at hlt
  omega

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastLocality
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

def branchNoise {d : ℕ} (theta : ℝ) (c : Fin d)
    (s : IsingSpin) (Y : BranchVertex c → ℝ) (v : TreeVertex d) : IsingSpin :=
  if v.val = [] then s
  else if hv : [c] <+: v.val then edgeNoise theta (Y ⟨v, hv⟩)
  else IsingSpin.pos

def branchFactor {d : ℕ} (theta : ℝ) (c : Fin d)
    (p : IsingSpin × (BranchVertex c → ℝ)) : BranchVertex c → IsingSpin :=
  fun v => ofNoise (branchNoise theta c p.1 p.2) v.val

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastBranchLabels
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367

namespace RootedBroadcast

def branchEmbedding {d : ℕ} (c : Fin d) (v : BranchVertex c) : NonrootVertex d := by
  refine ⟨v.val, ?_⟩
  intro heq
  have hlen := v.property.length_le
  rw [heq, root_val] at hlen
  simp at hlen

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_BroadcastFamilyConditional
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance instIsProbabilityMeasureForallTreeVertexRealLabelMeasure (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FreeIsingMeasure
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

def freeIsingMeasure (d : ℕ) (theta : ℝ) : Measure (TreeVertex d → IsingSpin) :=
  (labelMeasure d).map (RootedBroadcast.factor theta)

instance freeIsingMeasure_probability (d : ℕ) (theta : ℝ) :
    IsProbabilityMeasure (freeIsingMeasure d theta) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply RootedBroadcast.measurable_factor <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  unfold freeIsingMeasure
  first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply RootedBroadcast.measurable_factor <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ComponentPairCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def componentPairSum {d : ℕ} (r : ℝ) (c : Fin d) (k l : ℕ) : ℝ :=
  ∑ u : ReducedTail c k, ∑ v : ReducedTail c l, componentPairWeight r u.1 v.1

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Chain
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def spinPathWeight (theta : ℝ) (n : ℕ) (x : Fin (n+1) → IsingSpin) : ℝ :=
  ∏ i : Fin n, transitionKernel theta (x i.castSucc) (x i.succ)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ComponentCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367

def componentIndexFinset {d : ℕ} (c : Fin d) (n : ℕ) :
    Finset (Σ k : ℕ, ReducedTail c k) :=
  (Finset.range (n + 1)).sigma (fun _ => Finset.univ)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PlantedStationarity
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
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

def coordinateMap (F : IsingSpin → A → B)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) : TreeVertex d → B :=
  fun v => F (p.1 v) (p.2 v)

theorem measurable_coordinateMap {F : IsingSpin → A → B}
    (hF : Measurable (Function.uncurry F)) : Measurable (coordinateMap (d := d) F) := by
  apply Measurable.of_eval
  intro v
  change Measurable ((Function.uncurry F) ∘
    (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) => (p.1 v, p.2 v)))
  exact hF.comp (by fun_prop)

end Problem367.PlantedStationarity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

def selectedPosterior {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (r : TreeVertex d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ :=
  rho[fun p => spinSign (p.1 r) | selectedObservationField F v]

theorem selectedObservationField_le {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) : selectedObservationField F v ≤
      (inferInstance : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A))) := by
  have hobs : Measurable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      fun i => F (p.1 (v i)) (p.2 (v i))) := by
    apply measurable_pi_iff.mpr
    intro i
    exact hF.comp (show Measurable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      (p.1 (v i), p.2 (v i))) by fun_prop)
  exact hobs.comap_le

theorem selectedObservationField_le_of_range_subset {d : ℕ} {A B ι κ : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) {v : ι → TreeVertex d} {w : κ → TreeVertex d}
    (hv : Set.range v ⊆ Set.range w) :
    selectedObservationField F v ≤ selectedObservationField F w := by
  let : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) :=
    selectedObservationField F w
  have hobs : Measurable
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun i => F (p.1 (v i)) (p.2 (v i))) := by
    apply measurable_pi_iff.mpr
    intro i
    obtain ⟨j, hj⟩ := hv ⟨i, rfl⟩
    have hm : Measurable
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          F (p.1 (w j)) (p.2 (w j))) :=
      (measurable_pi_apply j).comp (comap_measurable
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun k => F (p.1 (w k)) (p.2 (w k))))
    simpa only [hj] using hm
  exact hobs.comap_le

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ComponentPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

def childComponentIndexVertex {d : ℕ} (c a : Fin d) (u : ComponentIndex a) : TreeVertex d :=
  prefixFlip c (componentIndexVertex u)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ComponentConditionalRecursionInputs
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

def componentOwnChildFields {d : ℕ} {A : Type*} [MeasurableSpace A]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → ℝ) (c : Fin d) :
    Option {a : Fin d // c ≠ a} → ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ
  | none => fun p => F (p.1 (RootedBroadcast.branchRoot c))
      (p.2 (RootedBroadcast.branchRoot c))
  | some a => fun p => Real.artanh (selectedPosterior ρ F
      (childComponentIndexVertex c a.1)
      (prefixFlip c (RootedBroadcast.branchRoot a.1)) p)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ObservationCopyStationarity
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.ObservationCopyStationarity

def arrayRelabelEquiv {d : ℕ} {A : Type*} [MeasurableSpace A]
    (g : TreeAut d) : (TreeVertex d → A) ≃ᵐ (TreeVertex d → A) where
  toFun := relabel g
  invFun := fun x v => x (g.toEquiv v)
  left_inv := by intro x; funext v; simp [relabel]
  right_inv := by intro x; funext v; simp [relabel]
  measurable_toFun := measurable_relabel g
  measurable_invFun := Measurable.of_eval (fun _ => measurable_pi_apply _)

end Problem367.ObservationCopyStationarity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_CoupledAttenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {theta : ℝ} {X Y X' Y' H K H' K' : Ω → ℝ}

theorem memLp_log_responseAttenuation {p : ENNReal}
    (hθ : theta ^ 2 ≤ 1) (hX : MemLp X p μ) :
    MemLp (fun ω => Real.log (responseAttenuation theta (X ω))) p μ := by
  simpa only [Function.comp_def] using
    (lipschitzWith_log_responseAttenuation hθ).comp_memLp
      (by simp only [responseAttenuation_zero, Real.log_one]) hX

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RadialSummability
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def treeShellSigmaEquiv (d : ℕ) : (Σ n : ℕ, TreeShell d n) ≃ TreeVertex d :=
  Equiv.sigmaFiberEquiv (fun v : TreeVertex d => v.1.length)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SubcriticalPathSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set

namespace Problem367

def regularPathWeight (d : ℕ) (theta : ℝ) (n : ℕ) : ℝ :=
  (Fintype.card (TreeShell d (n + 1)) : ℝ) * theta ^ (2 * (n + 1))

def subcriticalPathConstant (d : ℕ) (theta C : ℝ) : ℝ :=
  2 + (3 * C + 6) * ∑' n : ℕ, regularPathWeight d theta n * ((n + 1 : ℕ) : ℝ) ^ 2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_CoupledResponseRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem367

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace ResponseRows

def pathProduct {ι : Type*} (theta : ℝ) (s : Finset ι) (X : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  ∏ i ∈ s, responseAttenuation theta (X i ω)

def pathLogDiff {ι : Type*} (theta : ℝ) (s : Finset ι)
    (X Y : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
    Real.log (responseAttenuation theta (Y i ω)))

def pathNoiseEnergy {ι : Type*} (μ : Measure Ω) (theta : ℝ) (s : Finset ι)
    (X Y : ι → Ω → ℝ) : ℝ :=
  ∫ ω, (pathProduct theta s X ω ^ 2 + pathProduct theta s Y ω ^ 2) *
    pathLogDiff theta s X Y ω ^ 2 ∂μ

def pathLinearEnergy {ι : Type*} (μ : Measure Ω) (theta : ℝ) (s : Finset ι)
    (X : ι → Ω → ℝ) (U : Ω → ℝ) : ℝ :=
  ∫ ω, U ω ^ 2 * pathProduct theta s X ω ^ 2 ∂μ

def coefficient {J ι : Type*} (theta : ℝ) (a : J → ℝ) (s : J → Finset ι)
    (X : J → ι → Ω → ℝ) (j : J) (ω : Ω) : ℝ :=
  a j * pathProduct theta (s j) (X j) ω

end ResponseRows

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ProgressiveIsingPosterior
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
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
theorem measurable_spinSign_array {ι : Type*} :
    Measurable (fun sigma : ι → IsingSpin => fun i => spinSign (sigma i)) := by
  have hsign : Measurable spinSign := by intro s hs; trivial
  exact Measurable.of_eval (fun i => hsign.comp (measurable_pi_apply i))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ProgressiveIsingCovariance
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
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

def infiniteGibbsResponseRow {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (y : TreeVertex d → ℝ) : ℝ :=
  ∑' w, infiniteGibbsResponse beta v w y ^ 2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_CovarianceL2Limit
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem367

open PlantedSymmetry

local instance covarianceL2LimitNonemptyIsingSpin_r69a824_1 : Nonempty IsingSpin := ⟨.neg⟩
def finiteGibbsCovarianceOn {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d))
    (v w : D) (y : D → ℝ) : ℝ :=
  FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta v) * spinSign (eta w)) y -
  FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta v)) y *
  FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta w)) y

def finiteGibbsCovariance {d : ℕ} (beta : ℝ) (v w : TreeVertex d) (n : ℕ)
    (y : TreeVertex d → ℝ) : ℝ := by
  classical
  exact if hw : w ∈ connectedExhaustion v n then
    finiteGibbsCovarianceOn beta (connectedExhaustion v n)
      ⟨v, mem_connectedExhaustion v n⟩ ⟨w, hw⟩ ((connectedExhaustion v n).restrict y)
    else 0

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_FiniteIsingEnergyLimit
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace Problem367

def brownianIsingObservationR {d : ℕ} {Ω : Type*}
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) : TreeVertex d → ℝ :=
  fun i => p.1 * spinSign (p.2.1 i) + B i p.1.toNNReal (p.2.2 i)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_FiniteLeafCovariance
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.LeafGibbs

def energy {A : Type*} (E : A → ℝ) (parent : A → IsingSpin)
    (beta y : ℝ) (s : A × IsingSpin) : ℝ :=
  E s.1 + y * spinSign s.2 + beta * spinSign s.2 * spinSign (parent s.1)

end Problem367.LeafGibbs

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastConeLocality
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

abbrev StrictDescendantVertex {d : ℕ} (c : TreeVertex d) :=
  {v : TreeVertex d // c.1 <+: v.1 ∧ v ≠ c}

def coneNoise {d : ℕ} (theta : ℝ) (c : TreeVertex d)
    (s : IsingSpin) (Y : StrictDescendantVertex c → ℝ) (v : TreeVertex d) : IsingSpin :=
  if v.1 = [] then s
  else if hv : c.1 <+: v.1 ∧ v ≠ c then edgeNoise theta (Y ⟨v, hv⟩)
  else IsingSpin.pos

def coneFactor {d : ℕ} (theta : ℝ) (c : TreeVertex d)
    (p : IsingSpin × (StrictDescendantVertex c → ℝ)) : DescendantVertex c → IsingSpin :=
  fun v => ofNoise (coneNoise theta c p.1 p.2) v.1

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastConeMarkov
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance instIsProbabilityMeasureForallTreeVertexRealLabelMeasure_1 (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_KoopmanInvolutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section Centered

variable [IsFiniteMeasure μ]

instance centeredL2Complete : CompleteSpace (centeredL2 μ) :=
  (innerSL ℝ (Lp.const 2 μ (1 : ℝ))).isComplete_ker.completeSpace_coe

end Centered

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RadialWalk
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace RadialWalk

variable {V : Type*} {d : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def treeWeight (d : ℕ) (v : TreeVertex d) : ℝ := weight d v.1.length

end RadialWalk
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RadialRepresentation
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem367
namespace RadialWalk

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def wordOperator (S : Fin d → H →L[ℝ] H) (v : TreeVertex d) : H →L[ℝ] H :=
  (v.1.map S).prod

end RadialWalk
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_WordAction
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeKoopman

theorem wordRelabel_measurePreserving {d : ℕ} (w : List (Fin d)) :
    MeasurePreserving (wordRelabel w) (labelMeasure d) (labelMeasure d) :=
  measurePreserving_relabel (wordAut w).symm

end Problem367.TreeKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_LawSpectral
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability
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

def wordRelabel (w : List (Fin d)) :
    (TreeVertex d → A) → (TreeVertex d → A) :=
  relabel (TreeKoopman.wordAut w).symm

end Problem367.TreeLawKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_NoisyLocalCovariance
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367.NoisyLocalCovariance
open PlantedStationarity

variable {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

abbrev noiseLaw (ν : Measure A) : Measure (TreeVertex d → A) :=
  Measure.infinitePi (fun _ : TreeVertex d => ν)

def averageBlock (ν : Measure A) (O : IsingSpin → A → B)
    (s : Finset (TreeVertex d)) (F : (s → B) → ℝ) (z : s → IsingSpin) : ℝ :=
  ∫ W : TreeVertex d → A, F (fun i => O (z i) (W i)) ∂noiseLaw ν

end Problem367.NoisyLocalCovariance

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InhomogeneousSpinChain
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.InhomogeneousChain

variable {A : Type*}

variable [Fintype A]

def expectation (K : ℕ → A → A → ℝ) (n : ℕ) (f : A → ℝ) (a : A) : ℝ :=
  ∑ x : Fin n → A, weight K n a x * f (FiniteChain.endpoint n a x)

@[simp] theorem expectation_zero (K : ℕ → A → A → ℝ) (f : A → ℝ) (a : A) :
    expectation K 0 f a = f a := by
  simp [expectation]

end Problem367.InhomogeneousChain

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PathPosteriorResponse
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.PathPosterior

def interaction (beta : ℝ) (n : ℕ) (s : Fin (n + 1) → IsingSpin) : ℝ :=
  beta * ∑ i : Fin n, spinSign (s i.castSucc) * spinSign (s i.succ)

def spin (n : ℕ) (s : Fin (n + 1) → IsingSpin) (v : Fin (n + 1)) : ℝ :=
  spinSign (s v)

@[simp] theorem childFields_fin {n : ℕ} (y : Fin (n + 1) → ℝ) (i : Fin n) :
    childFields y i = y i.succ := by
  simp only [childFields, dite_eq_left i.isLt]
  rfl

end Problem367.PathPosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathGibbs
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.TreePathGibbs

def assignmentEquiv {d : ℕ} (v : TreeVertex d) :
    (ConnectedHull.vertices v → IsingSpin) ≃ (Fin (v.1.length + 1) → IsingSpin) where
  toFun eta i := eta (vertexEquiv v i)
  invFun s u := s ((vertexEquiv v).symm u)
  left_inv eta := by
    funext u
    simp
  right_inv s := by
    funext i
    simp

end Problem367.TreePathGibbs

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_NormalizedPosteriorLimit
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

section Gaussian

open PlantedSymmetry

def gaussianPosteriorResponse {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    (v w : TreeVertex d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ :=
  posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (observationSigma (TreeVertex d) t)
    (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w))

end Gaussian

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_NormalizedInfiniteTimeEnergy
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.NormalizedInfiniteTimeEnergy

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

def observation (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : TreeVertex d → ℝ :=
  fun i => t * spinSign (p.1 i) + B i t.toNNReal (p.2 i)

def infiniteRow (beta : ℝ) (v : TreeVertex d)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (w : TreeVertex d)
    (q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) : ℝ :=
  infiniteGibbsResponse beta v w
    (fun i => q.1 * spinSign (q.2.1 i) + B i q.1.toNNReal (q.2.2 i))

end Problem367.NormalizedInfiniteTimeEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorSymmetry
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

def plantedMarkFlipEquiv (d : ℕ) (A : Type*) [AddGroup A]
    [MeasurableSpace A] [MeasurableNeg A] :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) ≃ᵐ
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) where
  toFun := Prod.map flipConfig Neg.neg
  invFun := Prod.map flipConfig Neg.neg
  left_inv := by rintro ⟨σ, z⟩; change (flipConfig (flipConfig σ), - -z) = (σ, z); simp
  right_inv := by rintro ⟨σ, z⟩; change (flipConfig (flipConfig σ), - -z) = (σ, z); simp
  measurable_toFun := measurable_flipConfig.prodMap measurable_neg
  measurable_invFun := measurable_flipConfig.prodMap measurable_neg

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_FiniteSignalInformation
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem367

def spinInformation {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (rho : Measure Ω) (S : Ω → IsingSpin) (m : MeasurableSpace Ω) : ℝ :=
  ∫ x, (rho[fun y => spinSign (S y) | m] x) ^ 2 ∂rho

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyBranchSeparation
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

def noisyBranchArray {d : ℕ} {A : Type*} (c : Fin d)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    (RootedBroadcast.BranchVertex c → IsingSpin) × (RootedBroadcast.BranchVertex c → A) :=
  ((fun v => z.1 v.val), fun v => z.2 v.val)

def noisyRootOtherArray {d : ℕ} {A : Type*} (c : Fin d)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    (IsingSpin × A) × (∀ b : {b : Fin d // b ≠ c},
      (RootedBroadcast.BranchVertex b.val → IsingSpin) ×
        (RootedBroadcast.BranchVertex b.val → A)) :=
  ((z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d)),
    fun b => noisyBranchArray b.val z)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_BranchObservationRegression
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

abbrev NoisyRootOtherData {d : ℕ} (A : Type*) (c : Fin d) :=
  (IsingSpin × A) × (∀ b : {b : Fin d // b ≠ c},
    (RootedBroadcast.BranchVertex b.val → IsingSpin) ×
      (RootedBroadcast.BranchVertex b.val → A))

theorem exists_otherBranch_of_nonroot {d : ℕ} (c : Fin d)
    (w : {w : TreeVertex d // ¬ [c] <+: w.val}) (hw : w.val.val ≠ []) :
    ∃ b : {b : Fin d // b ≠ c}, [b.val] <+: w.val.val := by
  rcases w with ⟨⟨w, hwred⟩, hwc⟩
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons b t =>
    have hbc : b ≠ c := by
      intro h
      subst b
      exact hwc (by simp)
    exact ⟨⟨b, hbc⟩, by simp⟩

def noisyRootOtherDecode {d : ℕ} {A : Type*} (c : Fin d)
    (p : NoisyRootOtherData A c)
    (w : {w : TreeVertex d // ¬ [c] <+: w.val}) : IsingSpin × A :=
  if hw : w.val.val = [] then p.1 else
    let b := Classical.choose (exists_otherBranch_of_nonroot c w hw)
    let v : RootedBroadcast.BranchVertex b.val :=
      ⟨w.val, Classical.choose_spec (exists_otherBranch_of_nonroot c w hw)⟩
    ((p.2 b).1 v, (p.2 b).2 v)

def decodeFlippedBranch {d : ℕ} {A : Type*} (c : Fin d)
    (p : NoisyRootOtherData A c) :
    (RootedBroadcast.BranchVertex c → IsingSpin) × (RootedBroadcast.BranchVertex c → A) :=
  ((fun v => (noisyRootOtherDecode c p (RootedBroadcast.flipBranchToComplement c v)).1),
    fun v => (noisyRootOtherDecode c p (RootedBroadcast.flipBranchToComplement c v)).2)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ComponentFusionRecurrence
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem367

def gaussianComponentInformation {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (c : Fin d) : ℝ :=
  ∫ z, (selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
    (fun s x => (t : ℝ) * spinSign s + x) (componentIndexVertex (c := c))
    (RootedBroadcast.branchRoot c) z) ^ 2
    ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FieldMoments
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
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

def gaussianPosteriorField {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (v : TreeVertex d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ :=
  fun p => Real.artanh
    (posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p)

theorem gaussianPlanted_noise_hasLaw {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (t : ℝ≥0) (v : TreeVertex d) :
    HasLaw (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) => p.2 v)
      (gaussianReal 0 t) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  have h := (measurePreserving_eval_infinitePi
    (fun _ : TreeVertex d => gaussianReal 0 t) v).comp
      (measurePreserving_snd (μ := μ) (ν := gaussianNoiseLaw (TreeVertex d) t))
  exact ⟨h.measurable.aemeasurable, h.map_eq⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_SelectedCriticalFieldMoments
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

open PlantedSymmetry

def selectedGaussianField {d : ℕ} {ι : Type*}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    (v : ι → TreeVertex d) (r : TreeVertex d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ :=
  fun p => Real.artanh (selectedPosterior
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (fun s z => (t : ℝ) * spinSign s + z) v r p)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteComponentGeometry
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem rootComponentFinset_root_mem {d : ℕ} {D : Finset (TreeVertex d)} (c : Fin d)
    (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D) :
    (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ rootComponentFinset D c :=
  mem_rootComponentFinset.mpr ⟨hc, List.prefix_refl _⟩

theorem rootComplementFinset_root_mem {d : ℕ} {D : Finset (TreeVertex d)} (c : Fin d)
    (hroot : ConnectedHull.root d ∈ D) :
    ConnectedHull.root d ∈ rootComplementFinset D c := by
  apply mem_rootComplementFinset.mpr
  refine ⟨hroot, ?_⟩
  intro h
  have hlen := h.length_le
  change 1 ≤ 0 at hlen
  omega

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ObservableDisintegration
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.ObservableDisintegration

variable {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [StandardBorelSpace X] [Nonempty X]

instance kernel_isMarkov (P : Measure X) [IsFiniteMeasure P] (Z : X → W) :
    IsMarkovKernel (kernel P Z) := by
  unfold kernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

omit [StandardBorelSpace X] [Nonempty X] in
theorem fst_graphLaw (P : Measure X) {Z : X → W} (hZ : Measurable Z) :
    (graphLaw P Z).fst = P.map Z := by
  change (P.map (fun x => (Z x, x))).map Prod.fst = P.map Z
  rw [Measure.map_map measurable_fst (measurable_graphMap hZ)]
  rfl

theorem compProd_kernel (P : Measure X) [IsFiniteMeasure P]
    {Z : X → W} (hZ : Measurable Z) :
    (P.map Z) ⊗ₘ kernel P Z = graphLaw P Z := by
  rw [← fst_graphLaw P hZ]
  exact Measure.disintegrate (graphLaw P Z) (graphLaw P Z).condKernel

omit [StandardBorelSpace X] [Nonempty X] in

theorem graphLaw_invariant (P : Measure X)
    {Z : X → W} (hZ : Measurable Z)
    {T : W → W} {S : X → X} (hT : Measurable T)
    (hS : MeasurePreserving S P P)
    (heq : ∀ᵐ x ∂P, Z (S x) = T (Z x)) :
    (graphLaw P Z).map (Prod.map T S) = graphLaw P Z := by
  apply FactorTransport.map_invariant_of_ae_equivariant hS
    (hT.prodMap hS.measurable) (hZ.prodMk measurable_id)
  filter_upwards [heq] with x hx
  exact Prod.ext hx rfl

theorem joint_kernel_invariant (P : Measure X) [IsFiniteMeasure P]
    {Z : X → W} (hZ : Measurable Z)
    {T : W → W} {S : X → X} (hT : Measurable T)
    (hS : MeasurePreserving S P P)
    (heq : ∀ᵐ x ∂P, Z (S x) = T (Z x)) :
    ((P.map Z) ⊗ₘ kernel P Z).map (Prod.map T S) =
      (P.map Z) ⊗ₘ kernel P Z := by
  rw [compProd_kernel P hZ]
  exact graphLaw_invariant P hZ hT hS heq

end Problem367.ObservableDisintegration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressiveVersionPushforward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.ProgressiveVersionPushforward
open ContinuousModification

def leftTime (t : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  (dyadicLeft (t : ℝ) n).toNNReal

def version {Ω : Type*} (M : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  sampledLimit leftTime M t ω

end Problem367.ProgressiveVersionPushforward

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CutContinuations
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def cutContinuationEquiv (d k L : ℕ) :
    (Σ v : TreeShell d (k + 1), ReducedTail (cutLastColor v) L) ≃
      TreeShell d (k + 1 + L) :=
  Equiv.ofBijective (fun p => appendCutContinuation p.1 p.2) (by
    constructor
    · rintro ⟨v, w⟩ ⟨v', w'⟩ heq
      have hv : v = v' := by
        have := congrArg (@cutPrefix d k L) heq
        simpa only [cutPrefix_appendCutContinuation] using this
      subst v'
      have hw : w = w' := by
        apply Subtype.ext
        have hlist := congrArg (fun x : TreeShell d (k + 1 + L) => x.1.1) heq
        exact List.append_cancel_left hlist
      subst w'
      rfl
    · intro v
      exact ⟨⟨cutPrefix v, cutSuffix v⟩, appendCutContinuation_prefix_suffix v⟩)

def rootPathProduct {d : ℕ} (a : TreeVertex d → ℝ) (v : TreeVertex d) : ℝ :=
  ∏ i ∈ Finset.range v.1.length, a (rootPathVertex v (i + 1))

theorem shell_head_eq_first {d k : ℕ} (p : TreeShell d (k + 1)) :
    p.1.1.head? = some (treeShellSuccEquiv d k p).1 := by
  rcases p with ⟨⟨p, hp⟩, hlen⟩
  cases p with
  | nil => simp at hlen
  | cons a p => rfl

theorem mem_descendants_avoidingTreeCut {d k L : ℕ}
    (forbidden : Finset (Fin d)) (v : TreeShell d (k + 1 + L)) :
    v ∈ cutDescendants (avoidingTreeCut forbidden k) L ↔
      ∀ c ∈ v.1.1.head?, c ∉ forbidden := by
  classical
  rw [mem_cutDescendants, mem_avoidingTreeCut]
  have hhead : v.1.1.head? = (cutPrefix v).1.1.head? := by
    change v.1.1.head? = (v.1.1.take (k + 1)).head?
    cases v.1.1 <;> rfl
  rw [hhead, shell_head_eq_first]
  simp

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CutLevelBranchIndependence
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

def cutUpperExtension {d n : ℕ} (U : TreeBall d n → ℝ) : TreeVertex d → ℝ :=
  fun v => if hv : v.1.length ≤ n then U ⟨v, hv⟩ else 0

def cutSpins {d : ℕ} (theta : ℝ) (n : ℕ)
    (U : TreeVertex d → ℝ) : TreeShell d n → IsingSpin :=
  fun c => factor theta U c.1

theorem measurable_cutSpins (d : ℕ) (theta : ℝ) (n : ℕ) :
    Measurable (@cutSpins d theta n) := by
  exact Measurable.of_eval (fun vertex =>
    (measurable_pi_apply vertex.1).comp (measurable_factor d theta))

def cutLabels {d n : ℕ} (U : TreeVertex d → ℝ) :
    (c : TreeShell d n) → StrictDescendantVertex c.1 → ℝ :=
  fun _ v => U v.1

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyCutLevelIndependence
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance noisyCutLevelIsProbabilityLabelMeasure (d : ℕ) :
    IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathSideBranches
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.PathSideBranches

def cone {d : ℕ} (r : TreeVertex d) : Set (TreeVertex d) :=
  {v | r.1 <+: v.1}

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyConeSeparation
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.PathSideBranches

def decodeCone {d : ℕ} {A : Type*} (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1)
    (p : (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A)) :
    (cone r → IsingSpin) × (cone r → A) :=
  ((fun u => p.1 ⟨g.toEquiv u.1, (hgeo u.1).mp u.2⟩),
    fun u => p.2 ⟨g.toEquiv u.1, (hgeo u.1).mp u.2⟩)

def decodeConeComplement {d : ℕ} {A : Type*}
    (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1)
    (p : NoisyRootOtherData A c) :
    ({u : TreeVertex d // u ∉ cone r} → IsingSpin) ×
      ({u : TreeVertex d // u ∉ cone r} → A) :=
  ((fun u => (noisyRootOtherDecode c p
      ⟨g.toEquiv u.1, fun h => u.2 ((hgeo u.1).mpr h)⟩).1),
    fun u => (noisyRootOtherDecode c p
      ⟨g.toEquiv u.1, fun h => u.2 ((hgeo u.1).mpr h)⟩).2)

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SelectedPathLocality
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

open PathSideBranches

namespace PathSideBranches

def reducedForward {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d) (i : Fin v.1.length) :
    Set (TreeVertex d) :=
  cone (ConnectedHull.takeVertex v (i.1 + 1)) \ cone (sideVertex hd v i)

end PathSideBranches

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SelectedPathAttenuation
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.PathSideBranches

def forwardGaussianField {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (t : ℝ≥0) (v : TreeVertex d) (k : ℕ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) : ℝ :=
  Real.artanh (selectedPosterior
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
    (fun s z => (t : ℝ) * spinSign s + z)
    (Subtype.val : cone (ConnectedHull.takeVertex v (k + 1)) → TreeVertex d)
    (ConnectedHull.takeVertex v (k + 1)) p)

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_CutChannels
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367
open PathSideBranches CutContinuationChannels

def gaussianConeFactor {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (t : ℝ≥0) (theta : ℝ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) (v : TreeVertex d) : ℝ :=
  responseAttenuation theta (Real.artanh (selectedPosterior
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
    (fun s x => (t : ℝ) * spinSign s + x)
    (Subtype.val : cone v → TreeVertex d) v z)) ^ 2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_InwardCutChannels
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.InwardCutChannels

open RootedBroadcast CutContinuationChannels

variable {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

def regionProduct
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → B) (theta : ℝ)
    (R : ℕ → Set (TreeVertex d)) (r : ℕ → TreeVertex d) (s : Finset ℕ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) : ℝ :=
  ∏ i ∈ s, responseAttenuation theta
    (Real.artanh (selectedPosterior rho F
      (Subtype.val : R i → TreeVertex d) (r i) z)) ^ 2

def regionAverage {W : Type*} [Fintype W]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → B) (theta : ℝ)
    (R : W → ℕ → Set (TreeVertex d)) (r : W → ℕ → TreeVertex d)
    (s : W → Finset ℕ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) : ℝ :=
  (∑ w : W, regionProduct rho F theta (R w) (r w) (s w) z) /
    (Fintype.card W : ℝ)

end Problem367.InwardCutChannels

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_InwardCutFields
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal
namespace Problem367.PathSideBranches
open ConnectedHull

def regionGaussianField {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (t : ℝ≥0) (S : Set (TreeVertex d)) (r : TreeVertex d)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) : ℝ :=
  Real.artanh (selectedPosterior
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
    (fun s x => (t : ℝ) * spinSign s + x)
    (Subtype.val : S → TreeVertex d) r z)

def inwardGaussianField {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (t : ℝ≥0) (v : TreeVertex d) (i : ℕ) :=
  regionGaussianField μ t (cone (takeVertex v (i + 1)))ᶜ (takeVertex v i)

def cutInwardGaussianField {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (t : ℝ≥0) (v : TreeVertex d) (k i : ℕ) :=
  regionGaussianField μ t
    (cone (takeVertex v k) \ cone (takeVertex v (i + 1))) (takeVertex v i)

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_InwardGaussianCutChannels
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.InwardCutChannels

open PathSideBranches CutContinuationChannels ConnectedHull

def inwardContinuationProduct {d k L : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (theta : ℝ)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) (s : Finset ℕ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) : ℝ :=
  ∏ i ∈ s, responseAttenuation theta
    (cutInwardGaussianField μ t (appendCutContinuation p w).1 (k + 1) i z) ^ 2

def inwardContinuationAverage {d k : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (theta : ℝ)
    (p : TreeShell d (k + 1)) (L : ℕ) (s : Finset ℕ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) : ℝ :=
  (∑ w : ReducedTail (cutLastColor p) L, inwardContinuationProduct μ t theta p w s z) /
    (Fintype.card (ReducedTail (cutLastColor p) L) : ℝ)

end Problem367.InwardCutChannels

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_InwardProducts
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367
open PathSideBranches

def gaussianInwardConeFactor {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (t : ℝ≥0) (theta : ℝ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) (v : TreeVertex d) : ℝ :=
  responseAttenuation theta
    (regionGaussianField μ t (cone v)ᶜ (parentVertex v) z) ^ 2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_PosteriorSymmetry
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem367

@[simp] theorem spinSign_flip (s : IsingSpin) : spinSign s.flip = -spinSign s := by
  cases s <;> norm_num [spinSign, IsingSpin.flip]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_WienerSampler
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.WienerSampler

theorem map_sample : Measure.map sample uniform01 = wienerMeasure :=
  (Classical.choose_spec exists_uniform01_wiener_sampler).2

theorem measurable_sample_eval :
    Measurable (fun p : ℝ≥0 × ℝ => sample p.2 p.1) := by
  exact continuous_eval.measurable.comp
    ((measurable_sample.comp measurable_snd).prodMk measurable_fst)

end Problem367.WienerSampler

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_InnovationLaw
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingInnovation

theorem spinArray_bound {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (v : TreeVertex d) :
    ∀ᵐ sigma ∂μ, |ArrayPosteriorStationarity.spinArray sigma v| ≤ (1 : ℝ≥0) := by
  apply Filter.Eventually.of_forall
  intro sigma
  cases hs : sigma v <;> norm_num [ArrayPosteriorStationarity.spinArray, spinSign, hs]

end Problem367.IsingInnovation

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

theorem measurable_nnrealTimePrimitive_of_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) (t : ℝ≥0) :
    Measurable (nnrealTimePrimitive m t) := by
  have hj : StronglyMeasurable (fun p : ℝ × Ω => m p.1.toNNReal p.2) :=
    (stronglyMeasurable_joint_of_isStronglyProgressive hm).comp_measurable
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  change Measurable (fun ω => ∫ r in (0 : ℝ)..(t : ℝ), m r.toNNReal ω)
  simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using
    (hj.integral_prod_left' (μ := volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ)))).measurable

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ConditionalCopyBounds
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
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

def graphLaw {d : ℕ} (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin)) :
    Measure (Paths d × Paths d) :=
  (observationLaw μ).map (fun x => (innovationMap beta x, x))

end Problem367.IsingConditionalCopyBounds

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationLaw
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationInnovation

def past {d : ℕ} (t : ℝ≥0) (x : Paths d) : TreeVertex d → Set.Iic t → ℝ :=
  fun v s => x v s

end Problem367.IsingObservationInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationRecovery
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationRecovery

open IsingObservationInnovation

def decode {d : ℕ} (x : Paths d) : TreeVertex d → IsingSpin :=
  SpinRecovery.decodeArray (fun v (n : ℕ) => x v n)

end Problem367.IsingObservationRecovery

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationFactor
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
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

instance kernel_markov (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] : IsMarkovKernel (kernel beta μ) := by
  unfold kernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationPosteriorTransport
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingObservationInnovation

theorem measurable_posterior {d : ℕ} (beta : ℝ) (v : TreeVertex d) (t : ℝ≥0) :
    Measurable (posterior beta v t) :=
  (((posterior_progressive beta v).stronglyAdapted t).mono
    ((filtration d).le t)).measurable

theorem posterior_memLp {d : ℕ} (beta : ℝ)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (v : TreeVertex d) (t : ℝ≥0) (p : ℝ≥0∞) :
    MemLp (posterior beta v t) p (observationLaw μ) :=
  MemLp.of_bound (measurable_posterior beta v t).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun x => posterior_norm_le_one beta v t x))

end Problem367.IsingObservationInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyEnergyIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.IsingCopyEnergy
open IsingObservationInnovation IsingObservationFactor

def projection {d : ℕ} (j : Bool) (q : Joint d) : Paths d :=
  if j then q.2.1 else q.2.2

def timeProjection {d : ℕ} (j : Bool) (p : ℝ × Joint d) : ℝ × Paths d :=
  (p.1, projection j p.2)

end Problem367.IsingCopyEnergy

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

def copyRelabel (g : TreeAut d) : Paths d × (Paths d × Paths d) →
    Paths d × (Paths d × Paths d) :=
  Prod.map (relabel g) (Prod.map (relabel g) (relabel g))

theorem measurable_copyRelabel (g : TreeAut d) : Measurable (copyRelabel g) :=
  (measurable_relabel g).prodMap ((measurable_relabel g).prodMap (measurable_relabel g))

end Problem367.IsingCopyStationarity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_NoisyLawSpectral
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.NoisyLawSpectral
open PlantedStationarity NoisyLocalCovariance

variable {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

abbrev law (μ : Measure (TreeVertex d → IsingSpin)) (ν : Measure A)
    (O : IsingSpin → A → B) : Measure (TreeVertex d → B) :=
  (μ.prod (noiseLaw ν)).map (coordinateMap O)

end Problem367.NoisyLawSpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ObservationLawSpectral
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.IsingObservationInnovation
open PlantedStationarity CopyDifference ColoredEdgeLifts

def uniformObservationChannel (s : IsingSpin) (u : ℝ) : WienerSampler.Path :=
  ⟨fun t => WienerSampler.sample u t + (t : ℝ) * spinSign s,
    (WienerSampler.sample u).continuous.add
      (NNReal.continuous_coe.mul continuous_const)⟩

end Problem367.IsingObservationInnovation

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

theorem copyReflection_involutive (c : Fin d) :
    Function.Involutive (copyRelabel (prefixTreeAut c)) := by
  intro p
  exact Prod.ext (TreeLawKoopman.reflection_involutive c p.1)
    (Prod.ext (TreeLawKoopman.reflection_involutive c p.2.1)
      (TreeLawKoopman.reflection_involutive c p.2.2))

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

theorem measurable_field_at (beta : ℝ) (t : ℝ≥0) (v : TreeVertex d) :
    Measurable (field beta v t) := by
  have hm : Measurable (posterior beta v t) :=
    (measurable_infiniteGibbsSpinMean beta v).comp
      (Measurable.of_eval (fun vertex => measurable_evaluation vertex t))
  unfold field Real.artanh
  exact ((measurable_const.add hm).div (measurable_const.sub hm)).sqrt.log

def cavityLogObservable (hbeta : 0 ≤ beta) (t : ℝ≥0) (v w : TreeVertex d)
    (x : Paths d) : ℝ :=
  Real.log (responseAttenuation (Real.tanh beta) (cavityObservable hbeta t v w x))

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

def cavityLogDifference (hbeta : 0 ≤ beta) (t : ℝ≥0) (v w : TreeVertex d)
    (q : Paths d × (Paths d × Paths d)) : ℝ :=
  cavityLogObservable hbeta t v w q.2.1 - cavityLogObservable hbeta t v w q.2.2

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_OrbitAverage
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem367.TreeOrbitAverage

def FixesStemBall {d : ℕ} (stem : List (Fin d)) (g : TreeAut d) : Prop :=
  ∀ u : TreeVertex d, u.1.length ≤ stem.length → g.toEquiv u = u

end Problem367.TreeOrbitAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyOrbitAverage
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.IsingCopyOrbitAverage

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds
open TreeOrbitAverage

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def copyAction (g : TreeAut d) : CopySpace d ≃ᵐ CopySpace d :=
  let e := ObservationCopyStationarity.arrayRelabelEquiv (A := WienerSampler.Path) g.symm
  e.prodCongr (e.prodCongr e)

end Problem367.IsingCopyOrbitAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathRerooting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def stripPrefixAut {d : ℕ} : List (Fin d) → TreeAut d
  | [] => TreeAut.refl d
  | a :: w => (prefixTreeAut a).trans (stripPrefixAut w)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyProductPathBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def pathCavityProduct (hbeta : 0 ≤ beta) (t : ℝ≥0) (g : TreeAut d)
    (v : TreeVertex d) (reverse : Bool) (x : Paths d) : ℝ :=
  ∏ i : Fin v.1.length, responseAttenuation (Real.tanh beta)
    (cavityObservable hbeta t
      (g.toEquiv (takeVertex v (if reverse then i.1 + 1 else i.1)))
      (g.toEquiv (takeVertex v (if reverse then i.1 else i.1 + 1))) x)

def pathCavityLogSum (hbeta : 0 ≤ beta) (t : ℝ≥0) (g : TreeAut d)
    (v : TreeVertex d) (reverse : Bool) (q : Paths d × (Paths d × Paths d)) : ℝ :=
  ∑ i : Fin v.1.length, cavityLogDifference hbeta t
    (g.toEquiv (takeVertex v (if reverse then i.1 + 1 else i.1)))
    (g.toEquiv (takeVertex v (if reverse then i.1 else i.1 + 1))) q

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ResponseRowEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.ResponseRows

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

@[simp] theorem pathNoiseEnergy_empty {ι : Type*} (theta : ℝ) (X Y : ι → Ω → ℝ) :
    pathNoiseEnergy μ theta ∅ X Y = 0 := by
  simp [pathNoiseEnergy, pathProduct, pathLogDiff]

@[simp] theorem pathLinearEnergy_empty {ι : Type*} (theta : ℝ) (X : ι → Ω → ℝ)
    (U : Ω → ℝ) : pathLinearEnergy μ theta ∅ X U = ∫ ω, U ω ^ 2 ∂μ := by
  simp [pathLinearEnergy, pathProduct]

end Probability

end Problem367.ResponseRows

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyResponseRowPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyStationarity ResponseRows PlantedSymmetry

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def pathCavity (hb : 0 ≤ beta) (t : ℝ≥0) (v : TreeVertex d) (i : ℕ)
    (x : Paths d) : ℝ :=
  cavityObservable hb t (ConnectedHull.takeVertex v (i + 1))
    (ConnectedHull.takeVertex v i) x

def row (beta : ℝ) (t : ℝ≥0) (v : TreeVertex d) (x : Paths d) : ℝ :=
  infiniteGibbsResponse beta (ConnectedHull.root d) v (fun i => x i t)

def noiseEnergy (hb : 0 ≤ beta) (t : ℝ≥0) (v : TreeVertex d) : ℝ :=
  pathNoiseEnergy (copies beta μ) (Real.tanh beta) (Finset.range v.1.length)
    (fun i q => pathCavity hb t v i q.2.1) (fun i q => pathCavity hb t v i q.2.2)

def linearEnergy (hb : 0 ≤ beta) (t : ℝ≥0) (v : TreeVertex d) : ℝ :=
  pathLinearEnergy (copies beta μ) (Real.tanh beta) (Finset.range v.1.length)
    (fun i q => pathCavity hb t v i q.2.1)
    (IsingConditionalCopyBounds.fieldDifference beta (ConnectedHull.root d) t)

end Problem367.IsingCopyResponseRowPaths

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyShellEnergies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367

def nonnegativeShellSup {d : ℕ} (F : TreeVertex d → ℝ) (n : ℕ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun v : Option (TreeShell d n) => v.elim 0 (fun v => F v))

namespace IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingConditionalCopyBounds ConnectedHull ResponseRows IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def noiseShellEnergy (hb : 0 ≤ beta) (t : ℝ≥0) (n : ℕ) : ℝ :=
  nonnegativeShellSup (noiseEnergy (μ := μ) hb t) n

def linearShellEnergy (hb : 0 ≤ beta) (t : ℝ≥0) (n : ℕ) : ℝ :=
  nonnegativeShellSup (linearEnergy (μ := μ) hb t) n

end IsingCopyResponseRowPaths
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopySmallLogLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySmallLogLoss

open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity
open IsingCopySpectral

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def logVariance (hbeta : 0 ≤ beta) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (v w : TreeVertex d) (t : ℝ≥0) : ℝ :=
  ∫ q, (cavityLogObservable hbeta t v w q.2.1 -
    cavityLogObservable hbeta t v w q.2.2) ^ 2 ∂copies beta μ

end Problem367.IsingCopySmallLogLoss

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyWeightedCut
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyWeightedCut

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds

def observationCopy {d : ℕ} (left : Bool) (q : CopySpace d) : Paths d :=
  if left then q.2.1 else q.2.2

end Problem367.IsingCopyWeightedCut

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_MixedFiltering
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

def covariance (beta : ℝ) (B : ℝ≥0 → A → ℝ)
    (v u : TreeVertex d) (t : ℝ≥0) (q : State d A) : ℝ :=
  infiniteGibbsCovariance beta v u
    (fun i => plantedArrayObservation (fun _ : TreeVertex d => B)
      ArrayPosteriorStationarity.spinArray i t q)

def finiteCovariance (beta : ℝ) (B : ℝ≥0 → A → ℝ)
    (v u : TreeVertex d) (n : ℕ) (t : ℝ≥0) (q : State d A) : ℝ :=
  finiteGibbsCovariance beta v u n
    (fun i => plantedArrayObservation (fun _ : TreeVertex d => B)
      ArrayPosteriorStationarity.spinArray i t q)

end Problem367.IsingInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationIndependence
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationInnovation

def futureInnovation {d : ℕ} (beta : ℝ) (s : ℝ≥0) (x : Paths d) :
    Set.Ici s → TreeVertex d → ℝ := fun t v =>
  innovationMap beta x v t.val - innovationMap beta x v s

end Problem367.IsingObservationInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SelectedInwardPathAttenuation
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367

namespace PathSideBranches

abbrev inwardCutGaussianField {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (t : ℝ≥0) (v : TreeVertex d) (cut i : ℕ) :=
  cutInwardGaussianField μ t v cut (i + 1)

end PathSideBranches
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_RootWeightedCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal BigOperators

namespace Problem367.IsingRootWeightedCut

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds
open TreeOrbitAverage IsingCopyWeightedCut IsingRootAttenuation

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def extensionAverage (hbeta : 0 ≤ beta) (t : ℝ≥0)
    (stem : List (Fin d)) (n k : ℕ) : Paths d → ℝ :=
  WeightedOrbitAverage.average (fun s : Extension stem n => fun x =>
    rootAttenuation hbeta t (endpoint s) x ^ k)

end Problem367.IsingRootWeightedCut

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_OrientedPathWeights
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
open IsingCopyStationarity IsingCopyPathBounds IsingCopyWeightedCut
open IsingCopyOrbitAverage TreeOrbitAverage

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def extensionAverage (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    (stem : List (Fin d)) (n : ℕ) : Paths d → ℝ :=
  WeightedOrbitAverage.average (fun s : Extension stem n => fun x =>
    attenuation hb t inward (endpoint s) x ^ 2)

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorLimit
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

def selectedObservationExhaustion {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (D : ℕ → Finset ι) (hD : Monotone D) :
    Filtration ℕ (inferInstance : MeasurableSpace
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A))) where
  seq n := selectedObservationField F (fun i : D n => v i.1)
  mono' n m hnm := selectedObservationField_le_of_range_subset F (by
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i.1, hD hnm i.2⟩, rfl⟩)
  le' n := selectedObservationField_le hF _

end Problem367

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
open TreeOrbitAverage PlantedSymmetry PathSideBranches

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def orientedGaussianFactor (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    (theta : ℝ) (inward : Bool)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) : TreeVertex d → ℝ :=
  if inward then gaussianInwardConeFactor μ t theta z else gaussianConeFactor μ t theta z

def restrictedAverage (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    {n : ℕ} (I : Finset (TreeShell d n)) (x : Paths d) : ℝ :=
  (∑ v ∈ I, attenuation hb t inward v.1 x ^ 2) / (I.card : ℝ)

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_StemRerootAverage
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem367.TreeOrbitAverage
open ConnectedHull

def suffixVertex {d n : ℕ} {stem : List (Fin d)} (s : Extension stem n) : TreeVertex d :=
  ⟨s.1, s.2.2.right_of_append⟩

@[simp] theorem suffixVertex_length {d n : ℕ} {stem : List (Fin d)}
    (s : Extension stem n) : (suffixVertex s).1.length = n := s.2.1

def extensionEquivCutDescendants {d : ℕ} (stem : List (Fin d))
    (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ) :
    Extension stem (k + 1 + L) ≃
      {v // v ∈ cutDescendants (avoidingTreeCut (stemForbidden stem) k) L} where
  toFun s := ⟨⟨suffixVertex s, s.2.1⟩, by
    rw [mem_descendants_avoidingTreeCut]
    intro c hc hbad
    have hc' : c ∈ stem.getLast? := by simpa only [stemForbidden, Option.mem_toFinset] using hbad
    exact (List.isChain_append.mp s.2.2).2.2 c hc' c hc rfl⟩
  invFun v := ⟨v.1.1.1, v.1.2, by
    apply hstem.append v.1.1.2
    intro c hc a ha heq
    subst a
    exact (mem_descendants_avoidingTreeCut (stemForbidden stem) v.1).mp v.2 c ha
      (by simpa only [stemForbidden, Option.mem_toFinset] using hc)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rootEdgeProduct {d : ℕ} (a : TreeVertex d → TreeVertex d → ℝ)
    (v : TreeVertex d) : ℝ :=
  ∏ i ∈ Finset.range v.1.length, a (takeVertex v i) (takeVertex v (i + 1))

end Problem367.TreeOrbitAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_StemRerootAverage
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
open TreeOrbitAverage ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def orderedEdgeFactor (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    (u v : TreeVertex d) (x : Paths d) : ℝ :=
  responseAttenuation (Real.tanh beta)
    (cavityObservable hb t (if inward then u else v) (if inward then v else u) x) ^ 2

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_WalkObstruction
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace IsingWalk

def treeEigenWeight (d : ℕ) (theta : ℝ) (v : TreeVertex d) : ℝ :=
  eigenWeight ((d : ℝ) - 1) theta v.1.length

end IsingWalk
end Problem367

end

end OAI
end


