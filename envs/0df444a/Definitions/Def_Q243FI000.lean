-- Prove2me | Definitions.Def_Q243FI000
-- name    : Q243FI000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T01:37:49.795277+00:00
-- url     : https://prove2.me/theorems/6f275e5f-0625-485b-a8df-e90501183c2c
-- title:
--   Definitions bundle Q243FI000 of the split of OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 566 declarations of OpenAI's Lean: 186 definitions, 15 instances and 365 theorems. The definitions and types are `OAI.Problem367.ActualRootVarianceIdentity`, `OAI.Problem367.ArrayPosteriorStationarity.spinArray`, `OAI.Problem367.ArtanhMartingaleFormula.secondWeight`, `OAI.Problem367.BrownianContinuousExistence.version`, `OAI.Problem367.BrownianDyadicMoments.time`, `OAI.Problem367.BrownianExistence.preWienerMeasure`, `OAI.Problem367.CavityArray.field`, `OAI.Problem367.CavityPair.solve`, `OAI.Problem367.CavityPair.step`, `OAI.Problem367.ComponentIndex`, `OAI.Problem367.ConditionalCharacteristic.character`, `OAI.Problem367.ConnectedHull.hull`, `OAI.Problem367.ConnectedHull.path`, `OAI.Problem367.ConnectedHull.pathAssignment`, `OAI.Problem367.ConnectedHull.root`, `OAI.Problem367.ConnectedHull.takeVertex`, `OAI.Problem367.ConnectedHull.vertices`, `OAI.Problem367.ContinuousCopyBrownian.Joint`, `OAI.Problem367.ContinuousModification.dyadicLeft`, `OAI.Problem367.ContinuousNoiseSplit.futurePath`, `OAI.Problem367.ContinuousObservationHistory.stoppedPath`, `OAI.Problem367.CountableProjective.pullFamily`, `OAI.Problem367.CountableProjective.pullFinite`, `OAI.Problem367.CountableProjective.split`, `OAI.Problem367.CutContinuationChannels.ConeSample`, `OAI.Problem367.CutContinuationChannels.averageChannel`, `OAI.Problem367.CutContinuationChannels.continuationChannel`, `OAI.Problem367.CutContinuationChannels.globalCone`, `OAI.Problem367.CutContinuationChannels.globalFactors`, `OAI.Problem367.CutContinuationChannels.restrictCone`, `OAI.Problem367.DiscrepancyEnergy.density`, `OAI.Problem367.FactorObservable.centeredSpinLp`, `OAI.Problem367.FactorObservable.field`, `OAI.Problem367.FactorObservable.spinLp`, `OAI.Problem367.FiniteIsingSplit.splitEquiv`, `OAI.Problem367.FinitePathGibbs.rawKernel`, `OAI.Problem367.FinitePathGibbs.tailPartition`, `OAI.Problem367.FinitePosterior.fieldEnergy`, `OAI.Problem367.FinitePosterior.fieldMean`, `OAI.Problem367.InhomogeneousChain.weight` and 146 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `FreeIsing_Brownian_ArrayObservation`, `FreeIsing_Brownian_Characterization`, `FreeIsing_Brownian_ContinuousExistence`, `FreeIsing_Brownian_DenseModification`, `FreeIsing_Brownian_DriftMoments`, `FreeIsing_Brownian_DyadicMoments`, `FreeIsing_Brownian_Existence`, `FreeIsing_Brownian_FourthMoment`, `FreeIsing_Brownian_Martingale`, `FreeIsing_Cavity_Array`, `FreeIsing_Cavity_BaseMoments`, `FreeIsing_Cavity_Homeomorph`, `FreeIsing_Cavity_Pair`, `FreeIsing_Conditioning_Characteristic`, `FreeIsing_Conditioning_ComponentInformation`, `FreeIsing_Conditioning_GaussianVector`, `FreeIsing_Conditioning_InnovationConditionalMoments`, `FreeIsing_Conditioning_PlantedInformation`, `FreeIsing_Energy_Attenuation`, `FreeIsing_Energy_ComponentCovariance`, `FreeIsing_Energy_DiscrepancyRowEnergy`, `FreeIsing_Energy_ProgressiveIsingCovariance`, `FreeIsing_Estimates_BoundedInnovationDrift`, `FreeIsing_Estimates_CenteredWordAction`, `FreeIsing_Estimates_CharacteristicRecurrence`, `FreeIsing_Estimates_ColorAutomorphisms`, `FreeIsing_Estimates_ComponentGibbsLimit`, `FreeIsing_Estimates_ContinuousModification`, `FreeIsing_Estimates_CountableProjective`, `FreeIsing_Estimates_CylinderBasics`, `FreeIsing_Estimates_DyadicContinuity`, `FreeIsing_Estimates_DyadicIncrementControl`, `FreeIsing_Estimates_FiniteComponentGeometry`, `FreeIsing_Estimates_FiniteIsingSplit`, `FreeIsing_Estimates_FiniteMarginals`, `FreeIsing_Estimates_FiniteWeightNormalization`, `FreeIsing_Estimates_InhomogeneousSpinChain`, `FreeIsing_Estimates_InnovationCharacteristic`, `FreeIsing_Estimates_LeafDeletion`, `FreeIsing_Estimates_LeafWeights`, `FreeIsing_Estimates_LocalColorAutomorphisms`, `FreeIsing_Estimates_MessageFunction`, `FreeIsing_Estimates_ObservableDisintegration`, `FreeIsing_Estimates_ProjectiveExtension`, `FreeIsing_Estimates_RadialSummability`, `FreeIsing_Estimates_RelabelMeasure`, `FreeIsing_Estimates_SeparatedLocalSupports`, `FreeIsing_Estimates_ThresholdArithmetic`, `FreeIsing_Estimates_UniformSampler`, `FreeIsing_Factors_Observable`, `FreeIsing_Factors_Transfer`, `FreeIsing_Gaussian_ContinuousNoiseSplit`, `FreeIsing_Gaussian_Moments`, `FreeIsing_Ising_ConditionalCopyBounds`, `FreeIsing_Ising_CopyEnergyIntegrability`, `FreeIsing_Ising_CopyObservables`, `FreeIsing_Ising_CopySmallLogLoss`, `FreeIsing_Ising_GaussianPosterior`, `FreeIsing_Ising_Innovation`, `FreeIsing_Ising_ObservationFactor`, `FreeIsing_Ising_ObservationInnovation`, `FreeIsing_Ising_ObservationLaw`, `FreeIsing_Ising_OrientedPath`, `FreeIsing_Ising_OrientedPrefixWeights`, `FreeIsing_Ising_RootAttenuation`, `FreeIsing_Ising_SharpVarianceRecovery`, `FreeIsing_Martingales_ArtanhMartingaleFormula`, `FreeIsing_Martingales_InnovationMartingale`, `FreeIsing_Posterior_ArrayPosteriorStationarity`, `FreeIsing_Posterior_ContinuousObservationHistory`, `FreeIsing_Posterior_Fields`, `FreeIsing_Posterior_PlantedSymmetry`, `FreeIsing_Posterior_ProgressiveIsingPosterior`, `FreeIsing_Posterior_SelectedPosteriorStationarity`, `FreeIsing_Posterior_Symmetry`, `FreeIsing_Spectral_KoopmanInvolutions`, `FreeIsing_Spins_Flip`, `FreeIsing_Spins_Kernel`, `FreeIsing_Spins_Moments`, `FreeIsing_Stochastic_ContinuousCopyBrownian`, `FreeIsing_Stochastic_WienerSampler`, `FreeIsing_Trees_BranchFlipGeometry`, `FreeIsing_Trees_BroadcastConeLocality`, `FreeIsing_Trees_BroadcastLocality`, `FreeIsing_Trees_ConeCoding`, `FreeIsing_Trees_ConnectedExhaustion`, `FreeIsing_Trees_ConnectedHull`, `FreeIsing_Trees_CutContinuationChannels`, `FreeIsing_Trees_CutContinuations`, `FreeIsing_Trees_FinitePathGibbs`, `FreeIsing_Trees_GibbsAutomorphism`, `FreeIsing_Trees_InnovationPathMap`, `FreeIsing_Trees_Koopman`, `FreeIsing_Trees_LawSpectral`, `FreeIsing_Trees_NoisyConeSeparation`, `FreeIsing_Trees_NoisyPathLocality`, `FreeIsing_Trees_OrbitAverage`, `FreeIsing_Trees_Parents`, `FreeIsing_Trees_PathCylinders`, `FreeIsing_Trees_PathGibbs`, `FreeIsing_Trees_PathRerooting`, `FreeIsing_Trees_PathSideBranches`, `FreeIsing_Trees_Regularity`, `FreeIsing_Trees_RestrictedCutCardinality`, `FreeIsing_Trees_RootedBroadcast`, `FreeIsing_Trees_RootedBroadcastLaw`, `FreeIsing_Trees_Shells`, `FreeIsing_Trees_SpinEncoding`, `FreeIsing_Trees_Transitivity`, `FreeIsing_Trees_WordAction`, `FreeIsing_Trees_WordCancellation`.
--
--   **Imports.** It imports the published bundle `Def_FreeIsing`.
--
--   **Imported by** (directly, in this split): the bundles `Q243FI003` and `Q243FI004`; the statements `OAI.Problem367.BrownianArrayFiltration.compensatedSquare_of_spatial_integral_limits`, `OAI.Problem367.ConstructedArtanhFormula.exists_artanh_decomposition`, `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_tendsto_zero`, `OAI.Problem367.IsingObservationFactor.actual_variance_analysis`, `OAI.Problem367.IsingObservationFactor.siteVariance_eq_zero_of_subcritical_actual_variance_identity`, `OAI.Problem367.LocalizedArtanhFormula.exists_jointExit_artanh_decomposition` and `OAI.Problem367.condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss`; the proofs of `OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral`, `OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral_compensatedSquare`, `OAI.Problem367.BrownianIntegralProcess.exists_global_continuous_uniform_integral` and `OAI.Problem367.StoppedRowNormalization.stopped_channel_normalization`.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing

section
-- module Solutions.Q243_FreeIsing.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_Martingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem preBrownian_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) : (∫ ω, (B t ω)^2 ∂P) = (t : ℝ) := by
  have h := hB.covariance_eval t t
  simpa [covariance, hB.integral_eval, pow_two] using h

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_InnovationMartingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

noncomputable def nnrealTimePrimitive {Ω : Type*} (m : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ := ∫ u in (0 : ℝ)..(t : ℝ), m u.toNNReal ω

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ArrayObservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

def arrayNaturalFiltration {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    (X : ι → ℝ≥0 → Ω → ℝ) (hm : ∀ i t, Measurable (X i t)) :
    Filtration ℝ≥0 mΩ where
  seq t := ⨆ i, Filtration.natural (X i) (fun t => (hm i t).stronglyMeasurable) t
  mono' _ _ hst := iSup_mono fun i => (Filtration.natural (X i)
    (fun t => (hm i t).stronglyMeasurable)).mono hst
  le' t := iSup_le fun i => (Filtration.natural (X i)
    (fun t => (hm i t).stronglyMeasurable)).le t

lemma arrayNaturalFiltration_stronglyAdapted {ι Ω : Type*} [MeasurableSpace Ω]
    (X : ι → ℝ≥0 → Ω → ℝ) (hm : ∀ i t, Measurable (X i t)) (i : ι) :
    StronglyAdapted (arrayNaturalFiltration X hm) (X i) := by
  intro t
  exact (Filtration.stronglyAdapted_natural
    (fun t => (hm i t).stronglyMeasurable) t).mono (show
      Filtration.natural (X i) (fun t => (hm i t).stronglyMeasurable) t ≤
        ⨆ j, Filtration.natural (X j) (fun t => (hm j t).stronglyMeasurable) t from
      le_iSup (fun j : ι => Filtration.natural (X j)
        (fun t => (hm j t).stronglyMeasurable) t) i)

def plantedArrayObservation {ι S Ω : Type*}
    (B : ι → ℝ≥0 → Ω → ℝ) (σ : S → ι → ℝ)
    (i : ι) (t : ℝ≥0) (q : S × (ι → Ω)) : ℝ :=
  B i t (q.2 i) + (t : ℝ) * σ q.1 i

lemma plantedArrayObservation_measurable {ι S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω]
    {B : ι → ℝ≥0 → Ω → ℝ} (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ) (i : ι) (t : ℝ≥0) :
    Measurable (plantedArrayObservation B σ i t) :=
  ((hmB i t).comp ((measurable_pi_apply i).comp measurable_snd)).add
    ((((measurable_pi_apply i).comp hσ).comp measurable_fst).const_mul _)

def arrayObservationFiltration {ι S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (σ : S → ι → ℝ) (hσ : Measurable σ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (S × (ι → Ω))) :=
  arrayNaturalFiltration (plantedArrayObservation B σ)
    (plantedArrayObservation_measurable hmB hσ)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ConditionalCharacteristic

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

def character (X : Ω → ℝ) (t : ℝ) (ω : Ω) : ℂ :=
  Complex.exp (t * X ω * Complex.I)

theorem measurable_character {X : Ω → ℝ} (hX : Measurable[mΩ] X) (t : ℝ) :
    Measurable (character X t) := by
  unfold character
  fun_prop

theorem integrable_character {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : Measurable[mΩ] X) (t : ℝ) :
    Integrable (character X t) P := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_character hX t).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  simp [character, ← Complex.ofReal_mul]

end Problem367.ConditionalCharacteristic

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_Characterization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Problem367.ConditionalCharacteristic

namespace Problem367.BrownianCharacterization

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem condExp_character_of_setIntegral
    (hm : m ≤ mΩ) {X : Ω → ℝ} (hX : Measurable X) (c : ℂ) (u : ℝ)
    (hchar : ∀ A : Set Ω, MeasurableSet[m] A →
      (∫ ω in A, character X u ω ∂μ) = μ.real A * c) :
    μ[character X u | m] =ᵐ[μ] fun _ => c := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm (integrable_character hX u)
  · intro A _ _
    exact (integrable_const c).integrableOn
  · intro A hA _
    rw [hchar A hA]
    simp
  · exact stronglyMeasurable_const.aestronglyMeasurable

end Problem367.BrownianCharacterization

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_DenseModification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367

theorem preBrownian_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {s : ℕ → ℝ≥0} {t : ℝ≥0} (hs : Tendsto s atTop (𝓝 t)) :
    TendstoInMeasure P (fun n => B (s n)) atTop (B t) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hmean (n : ℕ) : (∫ ω, B (s n) ω - B t ω ∂P) = 0 := by
    rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _),
      hB.integral_eval, hB.integral_eval, sub_self]
  have hvar (n : ℕ) : variance (B (s n) - B t) P = dist (s n) t := by
    rw [(hB.hasLaw_sub (s n) t).variance_eq, variance_id_gaussianReal]
    rfl
  have hbound (n : ℕ) : P {ω | ε ≤ ‖B (s n) ω - B t ω‖} ≤
      ENNReal.ofReal (dist (s n) t / ε ^ 2) := by
    simpa only [hvar, Pi.sub_apply, hmean, sub_zero, Real.norm_eq_abs] using
      meas_ge_le_variance_div_sq (hB.hasLaw_sub (s n) t).hasGaussianLaw.memLp_two hε
  have hlim : Tendsto (fun n => ENNReal.ofReal (dist (s n) t / ε ^ 2))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((hs.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t))).div_const
        (ε ^ 2))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hbound

theorem preBrownian_ae_eq_of_approximating_sequence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B Y : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    {s : ℕ → ℝ≥0} {t : ℝ≥0} (hs : Tendsto s atTop (𝓝 t))
    (hseq : ∀ n, B (s n) =ᵐ[P] Y (s n)) : B t =ᵐ[P] Y t := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => B (s n) ω) atTop (𝓝 (Y t ω)) := by
    filter_upwards [hY, ae_all_iff.mpr hseq] with ω hcont heq
    have ht := (hcont.tendsto t).comp hs
    simpa only [Function.comp_def, fun n => heq n] using ht
  exact tendstoInMeasure_ae_unique (preBrownian_tendstoInMeasure hB hs)
    (tendstoInMeasure_of_tendsto_ae
      (fun n => (hB.aemeasurable (s n)).aestronglyMeasurable) hlim)

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_FourthMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367

def standardGaussianFourthMoment : ℝ :=
  ∫ x : ℝ, ‖x‖ ^ 4 ∂gaussianReal 0 1

theorem gaussian_norm_fourth_eq (v : ℝ≥0) :
    (∫ x : ℝ, ‖x‖ ^ 4 ∂gaussianReal 0 v) =
      standardGaussianFourthMoment * (v : ℝ) ^ 2 := by
  have hm : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (v : ℝ) * x) =
      gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    apply Subtype.ext
    exact Real.sq_sqrt v.property
  rw [← hm, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [norm_mul, mul_pow]
  rw [integral_const_mul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hpow : Real.sqrt (v : ℝ) ^ 4 = (v : ℝ) ^ 2 := by
    calc
      Real.sqrt (v : ℝ) ^ 4 = (Real.sqrt (v : ℝ) ^ 2) ^ 2 := by ring
      _ = (v : ℝ) ^ 2 := congrArg (fun r : ℝ => r ^ 2) (Real.sq_sqrt v.property)
  rw [hpow]
  exact mul_comm _ _

theorem preBrownian_increment_fourth_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    (∫ ω, ‖B t ω - B s ω‖ ^ 4 ∂P) =
      standardGaussianFourthMoment * |(t : ℝ) - (s : ℝ)| ^ 2 := by
  have hL := hB.hasLaw_sub t s
  have hi := hL.integral_comp (f := fun x : ℝ => ‖x‖ ^ 4) (by fun_prop)
  simpa only [Function.comp_def, Pi.sub_apply, coe_nndist, Real.dist_eq] using
    hi.trans (gaussian_norm_fourth_eq (nndist (t : ℝ) (s : ℝ)))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_DyadicIncrementControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Problem367.DyadicIncrementControl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem measureReal_abs_gt_le_fourth {X : Ω → ℝ} {a : ℝ} (ha : 0 < a)
    (hX : Integrable (fun ω => |X ω| ^ 4) μ) :
    μ.real {ω | a < |X ω|} ≤ (∫ ω, |X ω| ^ 4 ∂μ) / a ^ 4 := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg (X ω)) 4)) hX (a ^ 4)
  apply (le_div_iff₀ (pow_pos ha 4)).2
  calc
    μ.real {ω | a < |X ω|} * a ^ 4 ≤
        μ.real {ω | a ^ 4 ≤ |X ω| ^ 4} * a ^ 4 := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg ha.le 4)
      exact measureReal_mono (fun ω hω => pow_le_pow_left₀ ha.le hω.le 4)
    _ ≤ ∫ ω, |X ω| ^ 4 ∂μ := by simpa only [mul_comm] using hm

theorem ae_eventually_of_measureReal_le {E : ℕ → Set Ω} {b : ℕ → ℝ}
    (hb : Summable b) (hE : ∀ n, μ.real (E n) ≤ b n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ E n := by
  apply ae_eventually_notMem
  apply ne_top_of_le_ne_top hb.tsum_ofReal_ne_top
  apply ENNReal.tsum_le_tsum
  intro n
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ (E n))]
  exact ENNReal.ofReal_le_ofReal (hE n)

theorem ae_eventually_grid_bound {m : ℕ → ℕ}
    (X : ∀ n, Fin (m n) → Ω → ℝ) {C q b : ℝ}
    (hq : 0 ≤ q) (hb : 0 < b) (hqb : q < b ^ 4)
    (hInt : ∀ n i, Integrable (fun ω => |X n i ω| ^ 4) μ)
    (hMoment : ∀ n, (∑ i : Fin (m n), ∫ ω, |X n i ω| ^ 4 ∂μ) ≤ C * q ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ i : Fin (m n), |X n i ω| ≤ b ^ n := by
  classical
  let E : ℕ → Set Ω := fun n => {ω | ∃ i : Fin (m n), b ^ n < |X n i ω|}
  have hratio0 : 0 ≤ q / b ^ 4 := div_nonneg hq (pow_nonneg hb.le _)
  have hratio1 : q / b ^ 4 < 1 := (div_lt_one (pow_pos hb 4)).2 hqb
  have hsum : Summable (fun n : ℕ => C * (q / b ^ 4) ^ n) :=
    (summable_geometric_of_lt_one hratio0 hratio1).mul_left C
  have hbound (n : ℕ) : μ.real (E n) ≤ C * (q / b ^ 4) ^ n := by
    calc
      μ.real (E n) = μ.real (⋃ i : Fin (m n), {ω | b ^ n < |X n i ω|}) := by
        congr 1
        ext ω
        simp [E]
      _ ≤ ∑ i : Fin (m n), μ.real {ω | b ^ n < |X n i ω|} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ i : Fin (m n), (∫ ω, |X n i ω| ^ 4 ∂μ) / (b ^ n) ^ 4 :=
        Finset.sum_le_sum (fun i _ => measureReal_abs_gt_le_fourth (pow_pos hb n) (hInt n i))
      _ = (∑ i : Fin (m n), ∫ ω, |X n i ω| ^ 4 ∂μ) / (b ^ n) ^ 4 := by
        rw [Finset.sum_div]
      _ ≤ (C * q ^ n) / (b ^ n) ^ 4 :=
        div_le_div_of_nonneg_right (hMoment n) (pow_nonneg (pow_nonneg hb.le n) 4)
      _ = C * (q / b ^ 4) ^ n := by
        rw [div_pow, ← pow_mul, ← pow_mul]
        rw [Nat.mul_comm n 4]
        ring
  filter_upwards [ae_eventually_of_measureReal_le hsum hbound] with ω hω
  filter_upwards [hω] with n hn i
  exact le_of_not_gt (fun hi => hn ⟨i, hi⟩)

theorem ae_eventually_dyadic_grid_bound (K : ℕ)
    (X : ∀ n, Fin (K * 2 ^ n) → Ω → ℝ) {C b : ℝ}
    (hb : 0 < b) (hdecay : (1 / 2 : ℝ) < b ^ 4)
    (hInt : ∀ n i, Integrable (fun ω => |X n i ω| ^ 4) μ)
    (hMoment : ∀ n i, (∫ ω, |X n i ω| ^ 4 ∂μ) ≤ C * (1 / 4 : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ i : Fin (K * 2 ^ n), |X n i ω| ≤ b ^ n := by
  apply ae_eventually_grid_bound X (C := (K : ℝ) * C) (q := 1 / 2)
    (by norm_num) hb hdecay hInt
  intro n
  calc
    (∑ i : Fin (K * 2 ^ n), ∫ ω, |X n i ω| ^ 4 ∂μ) ≤
        ∑ _i : Fin (K * 2 ^ n), C * (1 / 4 : ℝ) ^ n :=
      Finset.sum_le_sum (fun i _ => hMoment n i)
    _ = ((K : ℝ) * C) * (1 / 2 : ℝ) ^ n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      calc
        ((K : ℝ) * 2 ^ n) * (C * (1 / 4 : ℝ) ^ n) =
            ((K : ℝ) * C) * ((2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n) := by ring
        _ = ((K : ℝ) * C) * (1 / 2 : ℝ) ^ n := by
          rw [← mul_pow]
          norm_num

theorem ae_eventually_dyadic_grid_nine_tenths (K : ℕ)
    (X : ∀ n, Fin (K * 2 ^ n) → Ω → ℝ) {C : ℝ}
    (hInt : ∀ n i, Integrable (fun ω => |X n i ω| ^ 4) μ)
    (hMoment : ∀ n i, (∫ ω, |X n i ω| ^ 4 ∂μ) ≤ C * (1 / 4 : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ i : Fin (K * 2 ^ n),
      |X n i ω| ≤ (9 / 10 : ℝ) ^ n :=
  ae_eventually_dyadic_grid_bound K X (by norm_num) (by norm_num) hInt hMoment

end Problem367.DyadicIncrementControl

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_DyadicMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367.BrownianDyadicMoments

def time (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (2 : ℝ≥0) ^ n

lemma time_succ (n k : ℕ) : time n (k + 1) = time n k + (1 / 2 : ℝ≥0) ^ n := by
  simp only [time, Nat.cast_add, Nat.cast_one, add_div, div_pow, one_pow]

lemma nndist_time_succ (n k : ℕ) :
    nndist (time n (k + 1)) (time n k) = (1 / 2 : ℝ≥0) ^ n := by
  rw [time_succ, NNReal.nndist_eq, add_tsub_cancel_left,
    tsub_eq_zero_of_le le_self_add, max_eq_left (by positivity)]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ}

theorem ae_eventually_increments_of_fourth
    (hB : IsPreBrownianReal B μ) {C : ℝ}
    (hfourth : ∀ s t : ℝ≥0,
      (∫ ω, |B t ω - B s ω| ^ 4 ∂μ) ≤ C * (nndist t s : ℝ) ^ 2) :
    ∀ᵐ ω ∂μ, ∀ K : ℕ, ∀ᶠ n in atTop, ∀ k < K * 2 ^ n,
      |B (time n (k + 1)) ω - B (time n k) ω| ≤ (9 / 10 : ℝ) ^ n := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply ae_all_iff.2
  intro K
  let X : ∀ n, Fin (K * 2 ^ n) → Ω → ℝ :=
    fun n k ω => B (time n (k.val + 1)) ω - B (time n k.val) ω
  have hInt (n : ℕ) (k : Fin (K * 2 ^ n)) : Integrable (fun ω => |X n k ω| ^ 4) μ := by
    have hg := (hB.hasLaw_sub (time n (k.val + 1)) (time n k.val)).hasGaussianLaw
    simpa only [Real.norm_eq_abs, Pi.sub_apply, X] using
      (hg.memLp (p := (4 : ENNReal)) (by norm_num)).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have hMoment (n : ℕ) (k : Fin (K * 2 ^ n)) :
      (∫ ω, |X n k ω| ^ 4 ∂μ) ≤ C * (1 / 4 : ℝ) ^ n := by
    have h := hfourth (time n k.val) (time n (k.val + 1))
    rw [nndist_time_succ] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    norm_num only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  filter_upwards [DyadicIncrementControl.ae_eventually_dyadic_grid_nine_tenths K X hInt hMoment]
    with ω hω
  filter_upwards [hω] with n hn
  intro k hk
  exact hn ⟨k, hk⟩

theorem ae_eventually_increments (hB : IsPreBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ K : ℕ, ∀ᶠ n in atTop, ∀ k < K * 2 ^ n,
      |B (time n (k + 1)) ω - B (time n k) ω| ≤ (9 / 10 : ℝ) ^ n := by
  apply ae_eventually_increments_of_fourth hB (C := standardGaussianFourthMoment)
  intro s t
  simpa only [Real.norm_eq_abs, coe_nndist, NNReal.dist_eq] using
    (preBrownian_increment_fourth_moment hB s t).le

end Problem367.BrownianDyadicMoments

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_CountableProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Function Preorder
open scoped ENNReal
namespace Problem367.CountableProjective

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

def split (n : ℕ) (x : ∀ i : Iic (n+1), X i) :
    (∀ i : Iic n, X i) × X (n+1) :=
  (frestrictLe₂ (Nat.le_succ n) x, x ⟨n+1, mem_Iic.mpr le_rfl⟩)

lemma split_measurable (n : ℕ) : Measurable (split (X := X) n) := by
  exact (measurable_frestrictLe₂ _).prodMk (measurable_pi_apply _)

omit [∀ n, MeasurableSpace (X n)] in
lemma split_injective (n : ℕ) : Injective (split (X := X) n) := by
  intro x y h
  funext i
  by_cases hi : i.val ≤ n
  · exact congrFun (congrArg Prod.fst h) ⟨i.val, mem_Iic.mpr hi⟩
  · have hi' : i.val = n+1 := by have := mem_Iic.mp i.property; omega
    have he : i = ⟨n+1, mem_Iic.mpr le_rfl⟩ := Subtype.ext hi'
    subst i
    exact congrArg Prod.snd h

omit [∀ n, MeasurableSpace (X n)] in
lemma split_comp_restrict (n : ℕ) :
    split (X := X) n ∘ frestrictLe (n+1) =
      fun x : ∀ n, X n => (frestrictLe n x, x (n+1)) := rfl

variable [∀ n, StandardBorelSpace (X n)] [∀ n, Nonempty (X n)]

theorem exists_nat_marginals
    (μ : (n : ℕ) → Measure (∀ i : Iic n, X i))
    [∀ n, IsProbabilityMeasure (μ n)]
    (hμ : ∀ n, (μ (n+1)).map (frestrictLe₂ (Nat.le_succ n)) = μ n) :
    ∃ ν : Measure (∀ n, X n), IsProbabilityMeasure ν ∧
      ∀ n, ν.map (frestrictLe n) = μ n := by
  let κ : (n : ℕ) → Kernel (∀ i : Iic n, X i) (X (n+1)) :=
    fun n => condDistrib (fun x : ∀ i : Iic (n+1), X i =>
      x ⟨n+1, mem_Iic.mpr le_rfl⟩) (frestrictLe₂ (Nat.le_succ n)) (μ (n+1))
  let (n : ℕ) : IsMarkovKernel (κ n) := by dsimp [κ]; infer_instance
  let ν : Measure (∀ n, X n) := (Kernel.traj κ 0) ∘ₘ μ 0
  have hν : IsProbabilityMeasure ν := by dsimp [ν]; (first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  refine ⟨ν, hν, ?_⟩
  have hstep (n : ℕ) :
      (ν.map (frestrictLe n)) ⊗ₘ κ n =
        ν.map (fun x => (frestrictLe n x, x (n+1))) := by
    rw [Measure.compProd_eq_comp_prod]
    dsimp [ν]
    rw [Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
      Measure.comp_assoc, Measure.map_comp _ _ (by fun_prop)]
    congr with x₀ : 1
    rw [Kernel.comp_apply, ← Measure.compProd_eq_comp_prod,
      Kernel.map_apply _ (by fun_prop), Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le n)]
  intro n
  induction n with
  | zero =>
    dsimp [ν]
    rw [Measure.map_comp _ _ (measurable_frestrictLe 0),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  | succ n ih =>
    apply (split_measurable (X := X) n).measurableEmbedding (split_injective n) |>.map_injective
    rw [Measure.map_map (split_measurable n) (measurable_frestrictLe _)]
    rw [split_comp_restrict, ← hstep, ih]
    have hc := compProd_map_condDistrib (mβ := inferInstance)
      (μ := μ (n+1)) (X := frestrictLe₂ (Nat.le_succ n))
      (Y := fun x : ∀ i : Iic (n+1), X i => x ⟨n+1, mem_Iic.mpr le_rfl⟩)
      (measurable_pi_apply _).aemeasurable
    rw [hμ n] at hc
    exact hc

theorem exists_nat_projective_limit
    (μ : (I : Finset ℕ) → Measure (∀ i : I, X i))
    [∀ I, IsProbabilityMeasure (μ I)] (hμ : IsProjectiveMeasureFamily μ) :
    ∃ ν : Measure (∀ n, X n), IsProbabilityMeasure ν ∧ IsProjectiveLimit ν μ := by
  obtain ⟨ν, hν, hmarg⟩ := exists_nat_marginals (fun n => μ (Iic n))
    (fun n => (hμ (Iic (n+1)) (Iic n) (Iic_subset_Iic.mpr (Nat.le_succ n))).symm)
  exact ⟨ν, hν, (isProjectiveLimit_nat_iff hμ ν).mpr hmarg⟩

end Problem367.CountableProjective

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProjectiveExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Function
namespace Problem367.CountableProjective

variable {ι κ A : Type*} [MeasurableSpace A]

def pullFinite (e : ι ↪ κ) (I : Finset ι) (x : I.map e → A) (i : I) : A :=
  x ⟨e i, mem_map.mpr ⟨i, i.property, rfl⟩⟩

lemma measurable_pullFinite (e : ι ↪ κ) (I : Finset ι) :
    Measurable (pullFinite (A := A) e I) := by
  exact Measurable.of_eval fun _ => measurable_pi_apply _

omit [MeasurableSpace A] in
lemma injective_pullFinite (e : ι ↪ κ) (I : Finset ι) :
    Injective (pullFinite (A := A) e I) := by
  intro x y h
  funext j
  obtain ⟨i, hi, hij⟩ := mem_map.mp j.property
  have he : j = ⟨e i, mem_map.mpr ⟨i, hi, rfl⟩⟩ := Subtype.ext hij.symm
  subst j
  exact congrFun h ⟨i, hi⟩

def pullFamily (e : ι ↪ κ)
    (μ : (I : Finset κ) → Measure (I → A)) (I : Finset ι) : Measure (I → A) :=
  (μ (I.map e)).map (pullFinite e I)

lemma projective_pullFamily (e : ι ↪ κ)
    (μ : (I : Finset κ) → Measure (I → A)) (hμ : IsProjectiveMeasureFamily (α := fun _ => A) μ) :
    IsProjectiveMeasureFamily (α := fun _ => A) (pullFamily e μ) := by
  intro I J hJI
  dsimp [pullFamily]
  rw [hμ (I.map e) (J.map e) (map_subset_map.mpr hJI)]
  rw [Measure.map_map (measurable_pullFinite _ _) (Finset.measurable_restrict₂ _),
    Measure.map_map (Finset.measurable_restrict₂ (X := fun _ => A) hJI) (measurable_pullFinite _ _)]
  rfl

theorem exists_projective_limit_of_equiv_nat [StandardBorelSpace A] [Nonempty A]
    (e : ℕ ≃ ι) (μ : (I : Finset ι) → Measure (I → A))
    [∀ I, IsProbabilityMeasure (μ I)] (hμ : IsProjectiveMeasureFamily (α := fun _ => A) μ) :
    ∃ ν : Measure (ι → A), IsProbabilityMeasure ν ∧ IsProjectiveLimit (α := fun _ => A) ν μ := by
  classical
  let μ' := pullFamily e.toEmbedding μ
  let (I : Finset ℕ) : IsProbabilityMeasure (μ' I) := by
    dsimp [μ', pullFamily]
    first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_pullFinite <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  obtain ⟨ν', hν', hmarg⟩ := exists_nat_projective_limit (X := fun _ => A) μ' (projective_pullFamily _ _ hμ)
  let := hν'
  let f : (ℕ → A) → (ι → A) := fun x i => x (e.symm i)
  have hf : Measurable f := by fun_prop
  let ν := ν'.map f
  refine ⟨ν, (by first | exact Measure.isProbabilityMeasure_map (by first | exact hf.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), ?_⟩
  have hmap (I : Finset ℕ) : ν.map (I.map e.toEmbedding).restrict = μ (I.map e.toEmbedding) := by
    apply (measurable_pullFinite (A := A) e.toEmbedding I).measurableEmbedding
      (injective_pullFinite _ _) |>.map_injective
    rw [Measure.map_map (measurable_pullFinite _ _) (Finset.measurable_restrict _)]
    change (ν'.map f).map _ = _
    rw [Measure.map_map ((measurable_pullFinite _ _).comp (Finset.measurable_restrict _)) hf]
    have heq : pullFinite (A := A) e.toEmbedding I ∘ (I.map e.toEmbedding).restrict ∘ f = I.restrict := by
      funext x i
      simp [pullFinite, f]
    rw [Function.comp_assoc, heq]
    exact hmarg I
  intro I
  have hi : (I.map e.symm.toEmbedding).map e.toEmbedding = I := by
    ext i
    simp only [mem_map]
    constructor
    · rintro ⟨j, ⟨k, hk, rfl⟩, rfl⟩
      simpa using hk
    · intro hi
      refine ⟨e.symm i, ⟨i, hi, rfl⟩, e.apply_symm_apply i⟩
  have H := hmap (I.map e.symm.toEmbedding)
  rw [hi] at H
  exact H

theorem exists_countable_projective_limit [Countable ι] [StandardBorelSpace A] [Nonempty A]
    (μ : (I : Finset ι) → Measure (I → A))
    [∀ I, IsProbabilityMeasure (μ I)] (hμ : IsProjectiveMeasureFamily (α := fun _ => A) μ) :
    ∃ ν : Measure (ι → A), IsProbabilityMeasure ν ∧ IsProjectiveLimit (α := fun _ => A) ν μ := by
  classical
  cases finite_or_infinite ι with
  | inl h =>
    let := Fintype.ofFinite ι
    let g : (↑(Finset.univ : Finset ι) → A) → (ι → A) := fun x i => x ⟨i, mem_univ i⟩
    have hg : Measurable g := by fun_prop
    refine ⟨(μ univ).map g, (by first | exact Measure.isProbabilityMeasure_map (by first | exact hg.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), ?_⟩
    intro I
    rw [Measure.map_map (Finset.measurable_restrict _) hg]
    exact (hμ univ I (subset_univ I)).symm
  | inr h =>
    obtain ⟨e⟩ : Nonempty (ℕ ≃ ι) := nonempty_equiv_of_countable
    exact exists_projective_limit_of_equiv_nat e μ hμ

lemma marginal_map_extension [StandardBorelSpace A]
    (e : κ ↪ ι) (μ : (I : Finset ι) → Measure (I → A))
    (ν : Measure (κ → A)) (hmarg : IsProjectiveLimit (α := fun _ => A) ν (pullFamily e μ))
    (f : (κ → A) → (ι → A)) (hf : Measurable f)
    (hleft : ∀ x i, f x (e i) = x i) (I : Finset κ) :
    (ν.map f).map (I.map e).restrict = μ (I.map e) := by
  apply (measurable_pullFinite (A := A) e I).measurableEmbedding
    (injective_pullFinite _ _) |>.map_injective
  rw [Measure.map_map (measurable_pullFinite _ _) (Finset.measurable_restrict _),
    Measure.map_map ((measurable_pullFinite _ _).comp (Finset.measurable_restrict _)) hf]
  have heq : (pullFinite (A := A) e I ∘ (I.map e).restrict) ∘ f = I.restrict := by
    funext x i
    exact hleft x i
  rw [heq]
  exact hmarg I

theorem exists_measure_for_countable_marginals [StandardBorelSpace A] [Nonempty A]
    (μ : (I : Finset ι) → Measure (I → A))
    [∀ I, IsProbabilityMeasure (μ I)] (hμ : IsProjectiveMeasureFamily (α := fun _ => A) μ)
    (I : ℕ → Finset ι) :
    ∃ ν : Measure (ι → A), IsProbabilityMeasure ν ∧ ∀ n, ν.map (I n).restrict = μ (I n) := by
  classical
  let S : Set ι := ⋃ n, (I n : Set ι)
  have hS : S.Countable := Set.countable_iUnion fun n => (I n).countable_toSet
  let : Countable S := hS.to_subtype
  let e : S ↪ ι := Function.Embedding.subtype _
  let μ' := pullFamily e μ
  let (J : Finset S) : IsProbabilityMeasure (μ' J) := by
    dsimp [μ', pullFamily]
    first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_pullFinite <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  obtain ⟨ν', hν', hmarg⟩ := exists_countable_projective_limit μ' (projective_pullFamily _ _ hμ)
  let := hν'
  let a : A := Classical.choice inferInstance
  let f : (S → A) → (ι → A) := fun x i => if hi : i ∈ S then x ⟨i, hi⟩ else a
  have hf : Measurable f := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ S
    · simpa only [f, dite_eq_left hi] using (measurable_pi_apply (⟨i, hi⟩ : S))
    · simpa only [f, dite_eq_right hi] using (measurable_const : Measurable (fun _ : S → A => a))
  have hleft (x : S → A) (i : S) : f x (e i) = x i := by simp [f, e, i.property]
  refine ⟨ν'.map f, (by first | exact Measure.isProbabilityMeasure_map (by first | exact hf.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), ?_⟩
  intro n
  have hn (i : ι) (hi : i ∈ I n) : i ∈ S := Set.mem_iUnion.mpr ⟨n, hi⟩
  have hj : ((I n).subtype (· ∈ S)).map e = I n := Finset.subtype_map_of_mem hn
  have H := marginal_map_extension e μ ν' hmarg f hf hleft ((I n).subtype (· ∈ S))
  rw [hj] at H
  exact H

lemma projectiveContent_tendsto_zero [StandardBorelSpace A] [Nonempty A]
    (μ : (I : Finset ι) → Measure (I → A))
    [∀ I, IsProbabilityMeasure (μ I)] (hμ : IsProjectiveMeasureFamily (α := fun _ => A) μ)
    (s : ℕ → Set (ι → A)) (hs : ∀ n, s n ∈ measurableCylinders (fun _ : ι => A))
    (hanti : Antitone s) (hempty : ⋂ n, s n = ∅) :
    Filter.Tendsto (fun n => projectiveFamilyContent hμ (s n)) Filter.atTop (nhds 0) := by
  classical
  let I n := measurableCylinders.finset (hs n)
  obtain ⟨ν, hν, hmarg⟩ := exists_measure_for_countable_marginals μ hμ I
  let := hν
  have heq (n : ℕ) : projectiveFamilyContent hμ (s n) = ν (s n) := by
    rw [measurableCylinders.eq_cylinder (hs n),
      projectiveFamilyContent_cylinder hμ (measurableCylinders.measurableSet (hs n))]
    rw [cylinder, ← Measure.map_apply (Finset.measurable_restrict _)
      (measurableCylinders.measurableSet (hs n)), hmarg n]
  simp_rw [heq]
  have hlim := tendsto_measure_iInter_atTop
    (fun n => (MeasurableSet.of_mem_measurableCylinders (hs n)).nullMeasurableSet (μ := ν))
    hanti ⟨0, measure_ne_top _ _⟩
  simpa only [hempty, measure_empty, Function.comp_def] using hlim

theorem exists_projective_limit [StandardBorelSpace A] [Nonempty A]
    (μ : (I : Finset ι) → Measure (I → A))
    [∀ I, IsProbabilityMeasure (μ I)] (hμ : IsProjectiveMeasureFamily (α := fun _ => A) μ) :
    ∃ ν : Measure (ι → A), IsProbabilityMeasure ν ∧ IsProjectiveLimit (α := fun _ => A) ν μ := by
  have hadd : (projectiveFamilyContent hμ).IsSigmaSubadditive := by
    refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
      isSetRing_measurableCylinders (fun f hf hu hd => ?_)
    refine addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
      (projectiveFamilyContent hμ) (fun _ _ => projectiveFamilyContent_ne_top hμ) ?_ hf hu hd
    exact fun s hs ha he => projectiveContent_tendsto_zero μ hμ s hs ha he
  let ν : Measure (ι → A) := (projectiveFamilyContent hμ).measure
    isSetSemiring_measurableCylinders generateFrom_measurableCylinders.ge hadd
  have hlimit : IsProjectiveLimit (α := fun _ => A) ν μ := by
    intro I
    ext t ht
    rw [Measure.map_apply (Finset.measurable_restrict _) ht]
    change ν (cylinder I t) = _
    dsimp [ν]
    rw [AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _
      (cylinder_mem_measurableCylinders (α := fun _ : ι => A) I t ht), projectiveFamilyContent_cylinder hμ ht]
  exact ⟨ν, hlimit.isProbabilityMeasure, hlimit⟩

end Problem367.CountableProjective

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_Existence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.BrownianExistence

theorem exists_preWienerMeasure :
    ∃ ν : Measure (ℝ≥0 → ℝ), IsProbabilityMeasure ν ∧
      IsProjectiveLimit ν BrownianReal.projectiveFamily :=
  CountableProjective.exists_projective_limit BrownianReal.projectiveFamily
    BrownianReal.isProjectiveMeasureFamily_projectiveFamily

def preWienerMeasure : Measure (ℝ≥0 → ℝ) := Classical.choose exists_preWienerMeasure

instance instIsProbabilityMeasureForallNNRealRealPreWienerMeasure : IsProbabilityMeasure preWienerMeasure :=
  (Classical.choose_spec exists_preWienerMeasure).1

theorem preWienerMeasure_projectiveLimit :
    IsProjectiveLimit preWienerMeasure BrownianReal.projectiveFamily :=
  (Classical.choose_spec exists_preWienerMeasure).2

theorem coordinate_isPreBrownianReal :
    IsPreBrownianReal (fun t (ω : ℝ≥0 → ℝ) => ω t) preWienerMeasure where
  hasLaw I := {
    aemeasurable := (Finset.measurable_restrict I).aemeasurable
    map_eq := preWienerMeasure_projectiveLimit I }

end Problem367.BrownianExistence

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ContinuousModification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367
namespace ContinuousModification

variable {T Ω : Type*}

def dyadicLeft (t : ℝ) (n : ℕ) : ℝ := (⌊(2 : ℝ)^n * t⌋ : ℤ) / (2 : ℝ)^n

theorem dyadicLeft_le (t : ℝ) (n : ℕ) : dyadicLeft t n ≤ t := by
  unfold dyadicLeft
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^n)).2
  simpa only [mul_comm] using Int.floor_le ((2 : ℝ)^n * t)

theorem sub_inv_pow_le_dyadicLeft (t : ℝ) (n : ℕ) :
    t - ((2 : ℝ)^n)⁻¹ ≤ dyadicLeft t n := by
  have hp : (0 : ℝ) < 2^n := by positivity
  unfold dyadicLeft
  apply (le_div_iff₀ hp).2
  have hfloor := Int.lt_floor_add_one ((2 : ℝ)^n * t)
  have hinv : ((2 : ℝ)^n)⁻¹ * (2 : ℝ)^n = 1 := inv_mul_cancel₀ hp.ne'
  nlinarith

theorem tendsto_dyadicLeft (t : ℝ) : Tendsto (dyadicLeft t) atTop (𝓝 t) := by
  have hinv : Tendsto (fun n : ℕ => ((2 : ℝ)^n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hlow : Tendsto (fun n : ℕ => t - ((2 : ℝ)^n)⁻¹) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub hinv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (sub_inv_pow_le_dyadicLeft t) (dyadicLeft_le t)

end ContinuousModification
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_DyadicContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology NNReal

namespace Problem367.DyadicContinuity

theorem geometric_limit {T : Type*} (u : ℕ → T → ℝ) (s : Set T)
    {C r : ℝ} (_hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hstep : ∀ n t, t ∈ s → dist (u n t) (u (n+1) t) ≤ C * r^n) :
    ∀ t ∈ s,
      Tendsto (fun n => u n t) atTop (𝓝 (limUnder atTop (fun n => u n t))) ∧
      ∀ n, dist (u n t) (limUnder atTop (fun m => u m t)) ≤
        C * r^n * (1-r)⁻¹ := by
  intro t ht
  have hs : Summable (fun n : ℕ => C * r^n) :=
    (summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hr1)).mul_left C
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable (fun n => C*r^n) (fun n => hstep n t ht) hs)
  have hlim : Tendsto (fun n => u n t) atTop
      (𝓝 (limUnder atTop (fun n => u n t))) := by rwa [ha.limUnder_eq]
  refine ⟨hlim, fun n => ?_⟩
  have h := dist_le_tsum_of_dist_le_of_tendsto (fun n => C*r^n)
    (fun n => hstep n t ht) hs hlim n
  calc
    dist (u n t) (limUnder atTop (fun m => u m t)) ≤ ∑' m : ℕ, C*r^(n+m) := h
    _ = C*r^n*(1-r)⁻¹ := by
      simp only [pow_add, ← mul_assoc]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr1]

theorem continuousOn_geometric_limit {T : Type*} [PseudoMetricSpace T]
    (u : ℕ → T → ℝ) (s : Set T) {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hstep : ∀ n t, t ∈ s → dist (u n t) (u (n+1) t) ≤ C*r^n)
    (hosc : ∀ n x, x ∈ s → ∃ δ > 0, ∀ y ∈ s,
      dist y x < δ → dist (u n y) (u n x) ≤ C*r^n) :
    ContinuousOn (fun t => limUnder atTop (fun n => u n t)) s := by
  apply Metric.continuousOn_iff.mpr
  intro x hx ε hε
  have he : Tendsto (fun n : ℕ => (2*C*(1-r)⁻¹+C)*r^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul
      (2*C*(1-r)⁻¹+C)
  obtain ⟨n, hn⟩ := (he.eventually_lt_const hε).exists
  obtain ⟨δ, hδ, hδbound⟩ := hosc n x hx
  refine ⟨δ, hδ, fun y hy hxy => ?_⟩
  have hxerr := (geometric_limit u s hC hr hr1 hstep x hx).2 n
  have hyerr := (geometric_limit u s hC hr hr1 hstep y hy).2 n
  have htri := dist_triangle4
    (limUnder atTop (fun n => u n y)) (u n y) (u n x)
    (limUnder atTop (fun n => u n x))
  rw [dist_comm (limUnder atTop (fun n => u n y)) (u n y)] at htri
  have hosc' := hδbound y hy hxy
  nlinarith

theorem floor_double_cases (x : ℝ) :
    ⌊2*x⌋ = 2*⌊x⌋ ∨ ⌊2*x⌋ = 2*⌊x⌋+1 := by
  have hlo : 2*⌊x⌋ ≤ ⌊2*x⌋ := Int.le_floor.mpr (by
    have := Int.floor_le x
    push_cast
    linarith)
  have hhi : ⌊2*x⌋ < 2*⌊x⌋+2 := Int.floor_lt.mpr (by
    have := Int.lt_floor_add_one x
    push_cast
    linarith)
  omega

theorem floor_near_cases {x y : ℝ} (h : |x-y| < 1) :
    ⌊x⌋ = ⌊y⌋ ∨ ⌊x⌋ = ⌊y⌋+1 ∨ ⌊y⌋ = ⌊x⌋+1 := by
  have hxy := (abs_lt.mp h)
  have h1 : ⌊x⌋ < ⌊y⌋+2 := Int.floor_lt.mpr (by
    have := Int.lt_floor_add_one y
    push_cast
    linarith)
  have h2 : ⌊y⌋ < ⌊x⌋+2 := Int.floor_lt.mpr (by
    have := Int.lt_floor_add_one x
    push_cast
    linarith)
  omega

open ContinuousModification

theorem dyadicLeft_refinement (t : ℝ) (n : ℕ) :
    dyadicLeft t (n+1) = dyadicLeft t n ∨
      dyadicLeft t (n+1) = dyadicLeft t n + ((2 : ℝ)^(n+1))⁻¹ := by
  have hp : (2 : ℝ)^n ≠ 0 := by positivity
  rcases floor_double_cases ((2 : ℝ)^n*t) with h | h
  · left
    unfold dyadicLeft
    rw [pow_succ]
    have he : (2 : ℝ)^n*2*t = 2*((2 : ℝ)^n*t) := by ring
    rw [he, h]
    push_cast
    field_simp
  · right
    unfold dyadicLeft
    rw [pow_succ]
    have he : (2 : ℝ)^n*2*t = 2*((2 : ℝ)^n*t) := by ring
    rw [he, h]
    push_cast
    field_simp

theorem dyadic_refinement_bound (f : ℝ → ℝ) {H B : ℝ} (hB : 0 ≤ B)
    (n : ℕ)
    (hinc : ∀ k : ℤ, 0 ≤ k → (k : ℝ)/(2:ℝ)^(n+1) ≤ H →
      dist (f ((k:ℝ)/(2:ℝ)^(n+1)))
        (f (((k:ℝ)+1)/(2:ℝ)^(n+1))) ≤ B)
    {t : ℝ} (ht : t ∈ Set.Icc 0 H) :
    dist (f (dyadicLeft t n)) (f (dyadicLeft t (n+1))) ≤ B := by
  rcases dyadicLeft_refinement t n with h | h
  · rw [h, dist_self]
    exact hB
  · let k : ℤ := 2*⌊(2:ℝ)^n*t⌋
    have hk : 0 ≤ k := by
      dsimp [k]
      exact mul_nonneg (by norm_num) (Int.floor_nonneg.mpr (mul_nonneg (by positivity) ht.1))
    have he : (k:ℝ)/(2:ℝ)^(n+1) = dyadicLeft t n := by
      dsimp [k, dyadicLeft]
      rw [pow_succ]
      push_cast
      field_simp
    have he' : ((k:ℝ)+1)/(2:ℝ)^(n+1) = dyadicLeft t (n+1) := by
      rw [h, ←he, add_div]
      simp [one_div]
    rw [←he, ←he']
    exact hinc k hk (he ▸ (dyadicLeft_le t n).trans ht.2)

theorem dyadic_oscillation_bound (f : ℝ → ℝ) {H B : ℝ} (hB : 0 ≤ B)
    (n : ℕ)
    (hinc : ∀ k : ℤ, 0 ≤ k → (k : ℝ)/(2:ℝ)^n ≤ H →
      dist (f ((k:ℝ)/(2:ℝ)^n)) (f (((k:ℝ)+1)/(2:ℝ)^n)) ≤ B)
    {x y : ℝ} (hx : x ∈ Set.Icc 0 H) (hy : y ∈ Set.Icc 0 H)
    (hxy : dist x y < ((2:ℝ)^n)⁻¹) :
    dist (f (dyadicLeft x n)) (f (dyadicLeft y n)) ≤ B := by
  have hp : (0:ℝ) < 2^n := by positivity
  have hclose : |(2:ℝ)^n*x-(2:ℝ)^n*y| < 1 := by
    rw [←mul_sub, abs_mul, abs_of_pos hp]
    have h := (mul_lt_mul_of_pos_left hxy hp)
    rw [Real.dist_eq, mul_inv_cancel₀ hp.ne'] at h
    exact h
  rcases floor_near_cases hclose with h | h | h
  · simp only [dyadicLeft, h, dist_self]
    exact hB
  · have hk := Int.floor_nonneg.mpr (mul_nonneg hp.le hy.1)
    have hb := hinc ⌊(2:ℝ)^n*y⌋ hk ((dyadicLeft_le y n).trans hy.2)
    simpa only [dyadicLeft, h, Int.cast_add, Int.cast_one, dist_comm] using hb
  · have hk := Int.floor_nonneg.mpr (mul_nonneg hp.le hx.1)
    have hb := hinc ⌊(2:ℝ)^n*x⌋ hk ((dyadicLeft_le x n).trans hx.2)
    simpa only [dyadicLeft, h, Int.cast_add, Int.cast_one] using hb

theorem continuousOn_dyadicLimit (f : ℝ → ℝ) {H C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1) (N : ℕ)
    (hinc : ∀ n ≥ N, ∀ k : ℤ, 0 ≤ k → (k:ℝ)/(2:ℝ)^n ≤ H →
      dist (f ((k:ℝ)/(2:ℝ)^n)) (f (((k:ℝ)+1)/(2:ℝ)^n)) ≤ C*r^n) :
    ContinuousOn (fun t => limUnder atTop (fun n => f (dyadicLeft t n)))
      (Set.Icc 0 H) := by
  let u : ℕ → ℝ → ℝ := fun n t => f (dyadicLeft t (n+N))
  have hD : 0 ≤ C*r^N := mul_nonneg hC (pow_nonneg hr _)
  have hstep : ∀ n t, t ∈ Set.Icc 0 H →
      dist (u n t) (u (n+1) t) ≤ (C*r^N)*r^n := by
    intro n t ht
    have hh := dyadic_refinement_bound f
      (mul_nonneg hC (pow_nonneg hr (n+N+1))) (n+N)
      (hinc (n+N+1) (by omega)) ht
    have hp : C*r^(n+N+1) ≤ C*r^(n+N) := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (pow_nonneg hr _) hr1.le) hC
    have he : C*r^(n+N) = (C*r^N)*r^n := by rw [pow_add]; ring
    simpa only [u, show n+1+N=n+N+1 by omega, he] using hh.trans hp
  have hosc : ∀ n x, x ∈ Set.Icc 0 H → ∃ δ > 0, ∀ y ∈ Set.Icc 0 H,
      dist y x < δ → dist (u n y) (u n x) ≤ (C*r^N)*r^n := by
    intro n x hx
    refine ⟨((2:ℝ)^(n+N))⁻¹, by positivity, fun y hy hxy => ?_⟩
    have hh := dyadic_oscillation_bound f
      (mul_nonneg hC (pow_nonneg hr (n+N))) (n+N)
      (hinc (n+N) (by omega)) hy hx hxy
    have he : C*r^(n+N) = (C*r^N)*r^n := by rw [pow_add]; ring
    simpa only [u, he] using hh
  have hc := continuousOn_geometric_limit u (Set.Icc 0 H) hD hr hr1 hstep hosc
  apply hc.congr
  intro t ht
  have hshift := (geometric_limit u (Set.Icc 0 H) hD hr hr1 hstep t ht).1
  have hfull := (tendsto_add_atTop_iff_nat (f := fun n => f (dyadicLeft t n)) N).mp hshift
  exact hfull.limUnder_eq

theorem dyadicLeft_grid (k : ℤ) (n m : ℕ) (hnm : n ≤ m) :
    dyadicLeft ((k:ℝ)/(2:ℝ)^n) m = (k:ℝ)/(2:ℝ)^n := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have hp : (2:ℝ)^n ≠ 0 := by positivity
  have he : (2:ℝ)^(n+l)*((k:ℝ)/(2:ℝ)^n) = ((2:ℤ)^l*k:ℤ) := by
    push_cast
    rw [pow_add]
    field_simp
  unfold dyadicLeft
  rw [he, Int.floor_intCast]
  push_cast
  rw [pow_add]
  field_simp

theorem dyadicLimit_grid (f : ℝ → ℝ) (k : ℤ) (n : ℕ) :
    limUnder atTop (fun m => f (dyadicLeft ((k:ℝ)/(2:ℝ)^n) m)) =
      f ((k:ℝ)/(2:ℝ)^n) := by
  have he : (fun m => f (dyadicLeft ((k:ℝ)/(2:ℝ)^n) m)) =ᶠ[atTop]
      (fun _ => f ((k:ℝ)/(2:ℝ)^n)) := by
    apply eventually_atTop.mpr
    exact ⟨n, fun m hm => by dsimp; rw [dyadicLeft_grid k n m hm]⟩
  exact ((tendsto_congr' he).mpr tendsto_const_nhds).limUnder_eq

theorem continuousOn_Ici_dyadicLimit (f : ℝ → ℝ) {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hinc : ∀ H : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℤ,
      0 ≤ k → (k:ℝ)/(2:ℝ)^n ≤ H →
      dist (f ((k:ℝ)/(2:ℝ)^n)) (f (((k:ℝ)+1)/(2:ℝ)^n)) ≤ C*r^n) :
    ContinuousOn (fun t => limUnder atTop (fun n => f (dyadicLeft t n)))
      (Set.Ici 0) := by
  intro t ht
  obtain ⟨H, hH⟩ := exists_nat_gt t
  obtain ⟨N, hN⟩ := hinc H
  have hc := continuousOn_dyadicLimit f hC hr hr1 N hN
  apply (hc t (show t ∈ Set.Icc 0 (H:ℝ) from ⟨ht, hH.le⟩)).mono_of_mem_nhdsWithin
  apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
  refine ⟨Set.Iio (H:ℝ), Iio_mem_nhds hH, ?_⟩
  intro x hx
  exact ⟨hx.2, hx.1.le⟩

theorem continuous_nnreal_dyadicLimit (f : ℝ → ℝ) {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hinc : ∀ H : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℤ,
      0 ≤ k → (k:ℝ)/(2:ℝ)^n ≤ H →
      dist (f ((k:ℝ)/(2:ℝ)^n)) (f (((k:ℝ)+1)/(2:ℝ)^n)) ≤ C*r^n) :
    Continuous (fun t : ℝ≥0 => limUnder atTop (fun n => f (dyadicLeft t n))) := by
  exact (continuousOn_Ici_dyadicLimit f hC hr hr1 hinc).comp_continuous
    continuous_subtype_val (fun t => t.property)

theorem continuous_nnreal_dyadicLimit_of_nat_grid (f : ℝ → ℝ) {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hinc : ∀ H : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ, k < H*2^n →
      dist (f ((k:ℝ)/(2:ℝ)^n)) (f (((k:ℝ)+1)/(2:ℝ)^n)) ≤ C*r^n) :
    Continuous (fun t : ℝ≥0 => limUnder atTop (fun n => f (dyadicLeft t n))) := by
  apply continuous_nnreal_dyadicLimit f hC hr hr1
  intro H
  obtain ⟨N, hN⟩ := hinc (H+1)
  refine ⟨N, fun n hn k hk hkH => ?_⟩
  have hcast : (k.toNat:ℝ) = (k:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hk
  have hkR : (k:ℝ) ≤ (H:ℝ)*(2:ℝ)^n :=
    (div_le_iff₀ (by positivity : (0:ℝ)<2^n)).mp hkH
  have hb : (k.toNat:ℝ) < ((H+1:ℕ):ℝ)*(2:ℝ)^n := by
    rw [hcast]
    have hp : (0:ℝ)<2^n := by positivity
    push_cast
    nlinarith
  have hbNat : k.toNat < (H+1)*2^n := by exact_mod_cast hb
  simpa only [hcast] using hN n hn k.toNat hbNat

end Problem367.DyadicContinuity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ContinuousExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367.BrownianContinuousExistence
open ContinuousModification BrownianDyadicMoments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def version (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => B (Real.toNNReal (dyadicLeft t n)) ω)

lemma toNNReal_nat_grid (n k : ℕ) :
    Real.toNNReal ((k : ℝ) / (2 : ℝ) ^ n) = time n k := by
  apply NNReal.coe_injective
  simp [time, Real.toNNReal_of_nonneg (by positivity : 0 ≤ (k : ℝ) / (2 : ℝ) ^ n)]

lemma ae_continuous_version (hB : IsPreBrownianReal B μ) :
    ∀ᵐ ω ∂μ, Continuous (fun t => version B t ω) := by
  filter_upwards [ae_eventually_increments hB] with ω hω
  apply DyadicContinuity.continuous_nnreal_dyadicLimit_of_nat_grid
    (fun t : ℝ => B t.toNNReal ω) (C := 1) (r := 9 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  intro H
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hω H)
  refine ⟨N, fun n hn k hk => ?_⟩
  have hh := hN n hn k hk
  rw [show ((k : ℝ) + 1) / 2 ^ n = ((k + 1 : ℕ) : ℝ) / 2 ^ n by push_cast; rfl,
    toNNReal_nat_grid, toNNReal_nat_grid]
  simpa only [Real.dist_eq, abs_sub_comm, one_mul] using hh

omit [MeasurableSpace Ω] in
lemma version_grid (B : ℝ≥0 → Ω → ℝ) (k : ℤ) (hk : 0 ≤ k) (n : ℕ) (ω : Ω) :
    version B (Real.toNNReal ((k : ℝ) / 2 ^ n)) ω =
      B (Real.toNNReal ((k : ℝ) / 2 ^ n)) ω := by
  have hg : 0 ≤ (k : ℝ) / (2 : ℝ) ^ n := div_nonneg (by exact_mod_cast hk) (by positivity)
  unfold version
  rw [Real.coe_toNNReal _ hg]
  exact DyadicContinuity.dyadicLimit_grid (fun t : ℝ => B t.toNNReal ω) k n

theorem ae_eq_version (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    B t =ᵐ[μ] version B t := by
  let s : ℕ → ℝ≥0 := fun n => (dyadicLeft t n).toNNReal
  have hs : Tendsto s atTop (𝓝 t) := by
    have hh := continuous_real_toNNReal.continuousAt.tendsto.comp (tendsto_dyadicLeft (t : ℝ))
    simpa only [Real.toNNReal_coe, Function.comp_def, s] using hh
  apply preBrownian_ae_eq_of_approximating_sequence hB (ae_continuous_version hB) hs
  intro n
  apply Filter.Eventually.of_forall
  intro ω
  exact (version_grid B ⌊(2 : ℝ) ^ n * (t : ℝ)⌋
    (Int.floor_nonneg.mpr (mul_nonneg (by positivity) t.property)) n ω).symm

theorem isBrownianReal_version (hB : IsPreBrownianReal B μ) :
    IsBrownianReal (version B) μ :=
  ⟨hB.congr (ae_eq_version hB), ae_continuous_version hB⟩

end Problem367.BrownianContinuousExistence

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem one_add_abs_pow_le_two_exp (x : ℝ) (p : ℕ) :
    (1 + |x|) ^ p ≤ Real.exp ((p : ℝ) * x) + Real.exp (-(p : ℝ) * x) := by
  calc
    (1 + |x|) ^ p ≤ (Real.exp |x|) ^ p := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp |x|
    _ = Real.exp ((p : ℝ) * |x|) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((p : ℝ) * x) + Real.exp (-(p : ℝ) * x) := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        exact le_add_of_nonneg_right (Real.exp_nonneg _)
      · rw [abs_of_nonpos hx, mul_neg, neg_mul]
        exact le_add_of_nonneg_left (Real.exp_nonneg _)

theorem integrable_one_add_abs_pow_gaussian (p : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ p) (gaussianReal 0 1) := by
  apply ((integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (p : ℝ)).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-(p : ℝ)))).mono'
  · fun_prop
  · filter_upwards [] with x
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 + |x|) ^ p)]
      using one_add_abs_pow_le_two_exp x p

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_BaseMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : AEMeasurable Y μ) (hY2 : Integrable (fun ω => Y ω ^ 2) μ) :
    (∫ ω, |Y ω| ∂μ) ≤ Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) := by
  have hm : MemLp Y 2 μ := (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).mpr hY2
  have hma : MemLp (fun ω => |Y ω|) 2 μ := by simpa only [Real.norm_eq_abs] using hm.norm
  have hv := variance_nonneg (fun ω => |Y ω|) μ
  rw [variance_eq_sub hma] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  exact Real.le_sqrt_of_sq_le (by linarith)

theorem integrable_abs_pow_of_bounded_perturbation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y X : Ω → ℝ} {B : ℝ} (p : ℕ)
    (hB : 0 ≤ B) (hY : AEMeasurable Y μ)
    (hX : Integrable (fun ω => |X ω| ^ p) μ)
    (hbound : ∀ᵐ ω ∂μ, |Y ω - X ω| ≤ B) :
    Integrable (fun ω => |Y ω| ^ p) μ := by
  apply ((hX.add (integrable_const (B ^ p))).const_mul (2 ^ (p - 1) : ℝ)).mono'
    (hY.abs.pow_const p).aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  change ‖|Y ω| ^ p‖ ≤ 2 ^ (p - 1) * (|X ω| ^ p + B ^ p)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) p)]
  have hsum : |Y ω| ≤ |X ω| + B := by
    have htriangle := abs_add_le (Y ω - X ω) (X ω)
    have heq : Y ω - X ω + X ω = Y ω := by ring
    rw [heq] at htriangle
    linarith
  exact (pow_le_pow_left₀ (abs_nonneg _) hsum p).trans (add_pow_le (abs_nonneg _) hB p)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_DriftMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

def standardGaussianThirdMoment : ℝ :=
  ∫ x : ℝ, |x| ^ 3 ∂gaussianReal 0 1

theorem standardGaussianThirdMoment_nonneg : 0 ≤ standardGaussianThirdMoment :=
  integral_nonneg (fun _ => by positivity)

theorem integrable_standardGaussian_abs_pow (p : ℕ) :
    Integrable (fun x : ℝ => |x| ^ p) (gaussianReal 0 1) := by
  apply (integrable_one_add_abs_pow_gaussian p).mono'
  · fun_prop
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ |x| ^ p)]
    exact pow_le_pow_left₀ (abs_nonneg x) (by linarith) p

theorem gaussianReal_map_sqrt_mul (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply Subtype.ext
    simp [Real.sq_sqrt v.coe_nonneg]

theorem integrable_gaussianReal_abs_pow (v : ℝ≥0) (p : ℕ) :
    Integrable (fun x : ℝ => |x| ^ p) (gaussianReal 0 v) := by
  rw [← gaussianReal_map_sqrt_mul v]
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  simpa only [Function.comp_def, abs_mul, mul_pow,
    abs_of_nonneg (Real.sqrt_nonneg (v : ℝ))] using
    (integrable_standardGaussian_abs_pow p).const_mul (Real.sqrt (v : ℝ) ^ p)

theorem integral_gaussianReal_abs_pow (v : ℝ≥0) (p : ℕ) :
    (∫ x : ℝ, |x| ^ p ∂gaussianReal 0 v) =
      Real.sqrt (v : ℝ) ^ p * (∫ x : ℝ, |x| ^ p ∂gaussianReal 0 1) := by
  rw [← gaussianReal_map_sqrt_mul v, integral_map (by fun_prop) (by fun_prop)]
  simp only [abs_mul, mul_pow, abs_of_nonneg (Real.sqrt_nonneg (v : ℝ)),
    integral_const_mul]

theorem integral_abs_cube_of_gaussianLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) :
    (∫ ω, |X ω| ^ 3 ∂P) = standardGaussianThirdMoment * (v : ℝ) * Real.sqrt v := by
  have heq := hX.integral_comp (f := fun x : ℝ => |x| ^ 3) (by fun_prop)
  change (∫ ω, |X ω| ^ 3 ∂P) = _ at heq
  rw [heq, integral_gaussianReal_abs_pow]
  rw [show Real.sqrt (v : ℝ) ^ 3 = (v : ℝ) * Real.sqrt v by
    rw [pow_succ, Real.sq_sqrt v.coe_nonneg]]
  unfold standardGaussianThirdMoment
  ring

theorem abs_sq_sub_sq_le_of_abs_sub_le {x y K : ℝ}
    (_hK : 0 ≤ K) (hxy : |y - x| ≤ K) :
    |y ^ 2 - x ^ 2| ≤ 2 * K * |x| + K ^ 2 := by
  have hrewrite : y ^ 2 - x ^ 2 = 2 * x * (y - x) + (y - x) ^ 2 := by ring
  rw [hrewrite]
  calc
    |2 * x * (y - x) + (y - x) ^ 2| ≤
        |2 * x * (y - x)| + |(y - x) ^ 2| := abs_add_le _ _
    _ = 2 * |x| * |y - x| + |y - x| ^ 2 := by
      simp only [abs_mul, abs_pow]
      norm_num
    _ ≤ 2 * |x| * K + K ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hxy (by positivity))
        (pow_le_pow_left₀ (abs_nonneg _) hxy 2)
    _ = _ := by ring

theorem integral_abs_sq_sub_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hX2 : Integrable (fun ω => X ω ^ 2) P)
    (hbound : ∀ᵐ ω ∂P, |Y ω - X ω| ≤ K) :
    Integrable (fun ω => |Y ω ^ 2 - X ω ^ 2|) P ∧
    (∫ ω, |Y ω ^ 2 - X ω ^ 2| ∂P) ≤
      2 * K * Real.sqrt (∫ ω, X ω ^ 2 ∂P) + K ^ 2 := by
  have hXL2 : MemLp X 2 P :=
    (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mpr hX2
  have hXabs : Integrable (fun ω => |X ω|) P := hXL2.integrable (by norm_num) |>.abs
  have hdom := (hXabs.const_mul (2 * K)).add (integrable_const (K ^ 2))
  have hle : ∀ᵐ ω ∂P, |Y ω ^ 2 - X ω ^ 2| ≤ 2 * K * |X ω| + K ^ 2 := by
    filter_upwards [hbound] with ω hω
    exact abs_sq_sub_sq_le_of_abs_sub_le hK hω
  have hint : Integrable (fun ω => |Y ω ^ 2 - X ω ^ 2|) P := by
    apply hdom.mono' ((hY.pow_const 2).sub (hX.pow_const 2)).abs.aestronglyMeasurable
    filter_upwards [hle] with ω hω
    simpa only [Real.norm_eq_abs, abs_abs, Pi.add_apply, Pi.sub_apply] using hω
  refine ⟨hint, ?_⟩
  calc
    (∫ ω, |Y ω ^ 2 - X ω ^ 2| ∂P) ≤
        ∫ ω, 2 * K * |X ω| + K ^ 2 ∂P := integral_mono_ae hint hdom hle
    _ = 2 * K * (∫ ω, |X ω| ∂P) + K ^ 2 := by
      rw [integral_add (hXabs.const_mul _) (integrable_const _), integral_const_mul]
      simp
    _ ≤ _ := by
      gcongr
      exact integral_abs_le_sqrt_integral_sq hX hX2

theorem integral_abs_cube_le_of_bounded_perturbation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K) (hY : AEMeasurable Y P)
    (hX3 : Integrable (fun ω => |X ω| ^ 3) P)
    (hbound : ∀ᵐ ω ∂P, |Y ω - X ω| ≤ K) :
    Integrable (fun ω => |Y ω| ^ 3) P ∧
    (∫ ω, |Y ω| ^ 3 ∂P) ≤ 4 * ((∫ ω, |X ω| ^ 3 ∂P) + K ^ 3) := by
  have hint := integrable_abs_pow_of_bounded_perturbation 3 hK hY hX3 hbound
  have hdom := (hX3.add (integrable_const (K ^ 3))).const_mul 4
  refine ⟨hint, ?_⟩
  calc
    (∫ ω, |Y ω| ^ 3 ∂P) ≤ ∫ ω, 4 * (|X ω| ^ 3 + K ^ 3) ∂P := by
      apply integral_mono_ae hint hdom
      filter_upwards [hbound] with ω hω
      have ht : |Y ω| ≤ |X ω| + K := by
        calc
          |Y ω| = |Y ω - X ω + X ω| := by congr 1; ring
          _ ≤ |Y ω - X ω| + |X ω| := abs_add_le _ _
          _ ≤ |X ω| + K := by linarith
      exact (pow_le_pow_left₀ (abs_nonneg _) ht 3).trans
        (by convert add_pow_le (abs_nonneg (X ω)) hK 3 using 1; norm_num)
    _ = _ := by
      rw [integral_const_mul, integral_add hX3 (integrable_const _)]
      simp

theorem integrable_abs_pow_of_gaussianLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) (p : ℕ) :
    Integrable (fun ω => |X ω| ^ p) P := by
  have hi := integrable_gaussianReal_abs_pow v p
  rw [← hX.map_eq] at hi
  exact hi.comp_aemeasurable hX.aemeasurable

theorem preBrownian_hasLaw_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => B t ω - B s ω) (gaussianReal 0 (t - s)) P := by
  simpa only [add_tsub_cancel_of_le hst] using (hB.shift s).hasLaw_eval (t - s)

theorem preBrownian_integral_abs_increment_cube
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, |B t ω - B s ω| ^ 3 ∂P) =
      standardGaussianThirdMoment * ((t : ℝ) - (s : ℝ)) *
        Real.sqrt ((t : ℝ) - (s : ℝ)) := by
  simpa only [NNReal.coe_sub hst] using
    integral_abs_cube_of_gaussianLaw (preBrownian_hasLaw_increment hB hst)

theorem preBrownian_bounded_drift_increment_moments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B W : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hW : ∀ t, AEMeasurable (W t) P)
    {s t : ℝ≥0} (hst : s ≤ t) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ᵐ ω ∂P,
      |(W t ω - W s ω) - (B t ω - B s ω)| ≤ L * ((t : ℝ) - (s : ℝ))) :
    Integrable (fun ω => |(W t ω - W s ω) ^ 2 - (B t ω - B s ω) ^ 2|) P ∧
    (∫ ω, |(W t ω - W s ω) ^ 2 - (B t ω - B s ω) ^ 2| ∂P) ≤
      2 * (L * ((t : ℝ) - (s : ℝ))) * Real.sqrt ((t : ℝ) - (s : ℝ)) +
        (L * ((t : ℝ) - (s : ℝ))) ^ 2 ∧
    Integrable (fun ω => |W t ω - W s ω| ^ 3) P ∧
    (∫ ω, |W t ω - W s ω| ^ 3 ∂P) ≤
      4 * (standardGaussianThirdMoment * ((t : ℝ) - (s : ℝ)) *
        Real.sqrt ((t : ℝ) - (s : ℝ)) + (L * ((t : ℝ) - (s : ℝ))) ^ 3) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hLaw := preBrownian_hasLaw_increment hB hst
  have hX2 : Integrable (fun ω => (B t ω - B s ω) ^ 2) P := by
    simpa only [sq_abs] using integrable_abs_pow_of_gaussianLaw hLaw 2
  have hsecond : (∫ ω, (B t ω - B s ω) ^ 2 ∂P) = (t : ℝ) - (s : ℝ) := by
    simpa only [add_tsub_cancel_of_le hst, NNReal.coe_sub hst] using
      preBrownian_integral_sq (hB.shift s) (t - s)
  have hK : 0 ≤ L * ((t : ℝ) - (s : ℝ)) :=
    mul_nonneg hL (sub_nonneg.mpr hst)
  obtain ⟨hquadInt, hquad⟩ := integral_abs_sq_sub_sq_le hK hLaw.aemeasurable
    ((hW t).sub (hW s)) hX2 hbound
  obtain ⟨hcubicInt, hcubic⟩ := integral_abs_cube_le_of_bounded_perturbation hK
    ((hW t).sub (hW s)) (integrable_abs_pow_of_gaussianLaw hLaw 3) hbound
  rw [hsecond] at hquad
  rw [preBrownian_integral_abs_increment_cube hB hst] at hcubic
  exact ⟨hquadInt, hquad, hcubicInt, hcubic⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Pair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NNReal

namespace Problem367
namespace CavityPair

variable {ψ : ℝ → ℝ} {θ : ℝ≥0}

def step (ψ : ℝ → ℝ) (H K x : ℝ) : ℝ := H - ψ (K - ψ x)

theorem contracting_step (hψ : LipschitzWith θ ψ) (hθ : θ < 1) (H K : ℝ) :
    ContractingWith (θ * θ) (step ψ H K) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul ?_⟩
  · have hnonneg : (0 : ℝ) ≤ θ := θ.coe_nonneg
    have hlt : (θ : ℝ) < 1 := hθ
    change (θ : ℝ) * θ < 1
    nlinarith
  · intro x y
    simp only [step, dist_sub_left, NNReal.coe_mul]
    calc
      dist (ψ (K - ψ x)) (ψ (K - ψ y)) ≤
          θ * dist (K - ψ x) (K - ψ y) := hψ.dist_le_mul _ _
      _ = θ * dist (ψ x) (ψ y) := by rw [dist_sub_left]
      _ ≤ θ * (θ * dist x y) :=
        mul_le_mul_of_nonneg_left (hψ.dist_le_mul x y) θ.coe_nonneg
      _ = θ * θ * dist x y := by ring

theorem existsUnique (hψ : LipschitzWith θ ψ) (hθ : θ < 1) (H K : ℝ) :
    ∃! p : ℝ × ℝ, p.1 + ψ p.2 = H ∧ p.2 + ψ p.1 = K := by
  let F := step ψ H K
  have hF : ContractingWith (θ * θ) F := contracting_step hψ hθ H K
  let x := hF.fixedPoint F
  have hx : F x = x := hF.fixedPoint_isFixedPt
  refine ⟨(x, K - ψ x), ?_, ?_⟩
  · change x + ψ (K - ψ x) = H ∧ K - ψ x + ψ x = K
    dsimp [F, step] at hx
    constructor <;> linarith
  · intro p hp
    have hpF : F p.1 = p.1 := by
      dsimp [F, step]
      rw [show K - ψ p.1 = p.2 by linarith [hp.2]]
      linarith [hp.1]
    have hp1 : p.1 = x := hF.fixedPoint_unique hpF
    apply Prod.ext hp1
    change p.2 = K - ψ x
    rw [← hp1]
    linarith [hp.2]

theorem stability_fst (hψ : LipschitzWith θ ψ) (hθ : θ < 1)
    {x y x' y' H K H' K' : ℝ}
    (hx : x + ψ y = H) (hy : y + ψ x = K)
    (hx' : x' + ψ y' = H') (hy' : y' + ψ x' = K') :
    dist x x' ≤ (dist H H' + θ * dist K K') / (1 - (θ : ℝ)^2) := by
  have hθ0 : (0 : ℝ) ≤ θ := θ.coe_nonneg
  have hθ1 : (θ : ℝ) < 1 := hθ
  have hden : 0 < 1 - (θ : ℝ)^2 := by nlinarith
  have hX : dist x x' ≤ dist H H' + θ * dist y y' := by
    calc
      dist x x' = dist (H - ψ y) (H' - ψ y') := by
        congr 1 <;> linarith
      _ ≤ dist H H' + dist (ψ y) (ψ y') := dist_sub_sub_le _ _ _ _
      _ ≤ dist H H' + θ * dist y y' := by
        gcongr
        exact hψ.dist_le_mul _ _
  have hY : dist y y' ≤ dist K K' + θ * dist x x' := by
    calc
      dist y y' = dist (K - ψ x) (K' - ψ x') := by
        congr 1 <;> linarith
      _ ≤ dist K K' + dist (ψ x) (ψ x') := dist_sub_sub_le _ _ _ _
      _ ≤ dist K K' + θ * dist x x' := by
        gcongr
        exact hψ.dist_le_mul _ _
  apply (le_div_iff₀ hden).2
  have hY' := mul_le_mul_of_nonneg_left hY hθ0
  nlinarith

theorem stability (hψ : LipschitzWith θ ψ) (hθ : θ < 1)
    {p p' z z' : ℝ × ℝ}
    (hp : p.1 + ψ p.2 = z.1 ∧ p.2 + ψ p.1 = z.2)
    (hp' : p'.1 + ψ p'.2 = z'.1 ∧ p'.2 + ψ p'.1 = z'.2) :
    dist p.1 p'.1 ≤ (dist z.1 z'.1 + θ * dist z.2 z'.2) / (1 - (θ : ℝ)^2) ∧
    dist p.2 p'.2 ≤ (dist z.2 z'.2 + θ * dist z.1 z'.1) / (1 - (θ : ℝ)^2) :=
  ⟨stability_fst hψ hθ hp.1 hp.2 hp'.1 hp'.2,
    stability_fst hψ hθ hp.2 hp.1 hp'.2 hp'.1⟩

def solve (hψ : LipschitzWith θ ψ) (hθ : θ < 1) (z : ℝ × ℝ) : ℝ × ℝ :=
  Classical.choose (existsUnique hψ hθ z.1 z.2)

theorem solve_spec (hψ : LipschitzWith θ ψ) (hθ : θ < 1) (z : ℝ × ℝ) :
    (solve hψ hθ z).1 + ψ (solve hψ hθ z).2 = z.1 ∧
    (solve hψ hθ z).2 + ψ (solve hψ hθ z).1 = z.2 :=
  (Classical.choose_spec (existsUnique hψ hθ z.1 z.2)).1

theorem solve_eq (hψ : LipschitzWith θ ψ) (hθ : θ < 1) {z p : ℝ × ℝ}
    (hp : p.1 + ψ p.2 = z.1 ∧ p.2 + ψ p.1 = z.2) :
    solve hψ hθ z = p :=
  ((Classical.choose_spec (existsUnique hψ hθ z.1 z.2)).2 p hp).symm

theorem lipschitzWith_solve (hψ : LipschitzWith θ ψ) (hθ : θ < 1) :
    LipschitzWith (((1 + (θ : ℝ)) / (1 - (θ : ℝ)^2)).toNNReal)
      (solve hψ hθ) := by
  apply LipschitzWith.of_dist_le'
  intro z z'
  have hθ0 : (0 : ℝ) ≤ θ := θ.coe_nonneg
  have hθ1 : (θ : ℝ) < 1 := hθ
  have hden : 0 < 1 - (θ : ℝ)^2 := by nlinarith
  have h := stability hψ hθ (solve_spec hψ hθ z) (solve_spec hψ hθ z')
  have hfst : dist z.1 z'.1 ≤ dist z z' := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hsnd : dist z.2 z'.2 ≤ dist z z' := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  rw [Prod.dist_eq]
  apply max_le
  · apply h.1.trans
    calc
      (dist z.1 z'.1 + θ * dist z.2 z'.2) / (1 - (θ : ℝ)^2) ≤
          (dist z z' + θ * dist z z') / (1 - (θ : ℝ)^2) := by
        gcongr
      _ = (1 + (θ : ℝ)) / (1 - (θ : ℝ)^2) * dist z z' := by ring
  · apply h.2.trans
    calc
      (dist z.2 z'.2 + θ * dist z.1 z'.1) / (1 - (θ : ℝ)^2) ≤
          (dist z z' + θ * dist z z') / (1 - (θ : ℝ)^2) := by
        gcongr
      _ = (1 + (θ : ℝ)) / (1 - (θ : ℝ)^2) * dist z z' := by ring

theorem continuous_solve (hψ : LipschitzWith θ ψ) (hθ : θ < 1) :
    Continuous (solve hψ hθ) :=
  (lipschitzWith_solve hψ hθ).continuous

end CavityPair
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

def responseAttenuation (theta z : ℝ) : ℝ :=
  (1 - Real.tanh z ^ 2) / (1 - theta ^ 2 * Real.tanh z ^ 2)

lemma attenuation_denominator_pos {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    0 < 1 - theta ^ 2 * Real.tanh z ^ 2 := by
  have hmul := mul_le_mul_of_nonneg_right hθ (sq_nonneg (Real.tanh z))
  have ht := Real.tanh_sq_lt_one z
  nlinarith

lemma responseAttenuation_pos {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    0 < responseAttenuation theta z := by
  exact div_pos (sub_pos.mpr (Real.tanh_sq_lt_one z))
    (attenuation_denominator_pos hθ z)

lemma responseAttenuation_le_one {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    responseAttenuation theta z ≤ 1 := by
  rw [responseAttenuation, div_le_one (attenuation_denominator_pos hθ z)]
  have := mul_le_mul_of_nonneg_right hθ (sq_nonneg (Real.tanh z))
  nlinarith

@[simp] lemma responseAttenuation_zero (theta : ℝ) :
    responseAttenuation theta 0 = 1 := by
  simp [responseAttenuation]

@[simp] lemma responseAttenuation_neg (theta z : ℝ) :
    responseAttenuation theta (-z) = responseAttenuation theta z := by
  simp [responseAttenuation]

lemma hasDerivAt_tanh_response (z : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh z ^ 2) z := by
  have hd := (Real.hasDerivAt_sinh z).div (Real.hasDerivAt_cosh z)
    (ne_of_gt (Real.cosh_pos z))
  convert! hd using 1
  · ext x
    exact Real.tanh_eq_sinh_div_cosh x
  · rw [Real.tanh_eq_sinh_div_cosh]
    field_simp

lemma hasDerivAt_log_responseAttenuation {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    HasDerivAt (fun x => Real.log (responseAttenuation theta x))
      (-2 * (1 - theta ^ 2) * Real.tanh z /
        (1 - theta ^ 2 * Real.tanh z ^ 2)) z := by
  have ht := hasDerivAt_tanh_response z
  have hn := (ht.pow 2).const_sub 1
  have hd := ((ht.pow 2).const_mul (theta ^ 2)).const_sub 1
  have hden := ne_of_gt (attenuation_denominator_pos hθ z)
  have hnum := ne_of_gt (sub_pos.mpr (Real.tanh_sq_lt_one z))
  have hh := (hn.div hd hden).log (ne_of_gt (responseAttenuation_pos hθ z))
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [responseAttenuation]
  field_simp
  ring

@[simp] lemma deriv_log_responseAttenuation_zero {theta : ℝ}
    (hθ : theta ^ 2 ≤ 1) :
    deriv (fun x => Real.log (responseAttenuation theta x)) 0 = 0 := by
  rw [(hasDerivAt_log_responseAttenuation hθ 0).deriv]
  simp

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_MessageFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def cavityMessage (theta z : ℝ) : ℝ :=
  Real.artanh (theta * Real.tanh z)

lemma hasDerivAt_artanh_interval {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have hminus : 0 < 1 - x := sub_pos.mpr hx.2
  have hplus : 0 < 1 + x := by linarith [hx.1]
  have hratio : 0 < (1 + x) / (1 - x) := div_pos hplus hminus
  have hsqrt : 0 < Real.sqrt ((1 + x) / (1 - x)) := Real.sqrt_pos.mpr hratio
  have hsq : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hr := ((hasDerivAt_id x).const_add 1).div
    ((hasDerivAt_id x).const_sub 1) hminus.ne'
  have hh := (hr.sqrt hratio.ne').log hsqrt.ne'
  change HasDerivAt Real.artanh _ x at hh
  apply hh.congr_deriv
  dsimp
  have hs := Real.sq_sqrt hratio.le
  field_simp
  rw [hs]
  field_simp
  ring

lemma cavityMessage_argument_mem {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    theta * Real.tanh z ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hmul := mul_le_mul_of_nonneg_right hθ (sq_nonneg (Real.tanh z))
  have hs : (theta * Real.tanh z) ^ 2 < 1 := by
    nlinarith [Real.tanh_sq_lt_one z]
  exact abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hs)

lemma hasDerivAt_cavityMessage {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    HasDerivAt (cavityMessage theta) (theta * responseAttenuation theta z) z := by
  have ha := hasDerivAt_artanh_interval (cavityMessage_argument_mem hθ z)
  have ht := (hasDerivAt_tanh_response z).const_mul theta
  have hh := ha.comp z ht
  change HasDerivAt (cavityMessage theta) _ z at hh
  apply hh.congr_deriv
  unfold responseAttenuation
  ring

@[simp] lemma cavityMessage_zero (theta : ℝ) : cavityMessage theta 0 = 0 := by
  simp [cavityMessage]

lemma abs_deriv_cavityMessage_le {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta ≤ 1) (z : ℝ) :
    |deriv (cavityMessage theta) z| ≤ theta := by
  have hsq : theta ^ 2 ≤ 1 := by nlinarith
  rw [(hasDerivAt_cavityMessage hsq z).deriv, abs_mul,
    abs_of_nonneg hθ0, abs_of_pos (responseAttenuation_pos hsq z)]
  simpa using mul_le_mul_of_nonneg_left (responseAttenuation_le_one hsq z) hθ0

lemma lipschitzWith_cavityMessage {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta ≤ 1) :
    LipschitzWith ⟨theta, hθ0⟩ (cavityMessage theta) := by
  have hsq : theta ^ 2 ≤ 1 := by nlinarith
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro z
    exact (hasDerivAt_cavityMessage hsq z).differentiableAt
  · intro z
    exact_mod_cast abs_deriv_cavityMessage_le hθ0 hθ1 z

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Homeomorph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def cavitySiteMap (theta : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 + cavityMessage theta p.2, p.2 + cavityMessage theta p.1)

def cavityHomeomorph {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := cavitySiteMap theta
  invFun := CavityPair.solve (lipschitzWith_cavityMessage h0 h1.le) h1
  left_inv p := CavityPair.solve_eq _ _ ⟨rfl, rfl⟩
  right_inv z := Prod.ext (CavityPair.solve_spec _ _ z).1 (CavityPair.solve_spec _ _ z).2
  continuous_toFun := by
    have hψ := (lipschitzWith_cavityMessage h0 h1.le).continuous
    exact (continuous_fst.add (hψ.comp continuous_snd)).prodMk
      (continuous_snd.add (hψ.comp continuous_fst))
  continuous_invFun := CavityPair.continuous_solve _ _

def cavityFromSites {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (z : ℝ × ℝ) : ℝ × ℝ := (cavityHomeomorph h0 h1).symm z

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RelabelMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem measurable_relabel {d : ℕ} {α : Type*} [MeasurableSpace α]
    (g : TreeAut d) :
    Measurable (relabel g : (TreeVertex d → α) → (TreeVertex d → α)) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

theorem map_labelMeasure_relabel {d : ℕ} (g : TreeAut d) :
    Measure.map (relabel g) (labelMeasure d) = labelMeasure d := by
  exact Measure.map_infinitePi_infinitePi_of_inj g.toEquiv.symm.injective

theorem measurePreserving_relabel {d : ℕ} (g : TreeAut d) :
    MeasurePreserving (relabel g) (labelMeasure d) (labelMeasure d) :=
  ⟨measurable_relabel g, map_labelMeasure_relabel g⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Transitivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

namespace TreeAut

def refl (d : ℕ) : TreeAut d where
  toEquiv := Equiv.refl _
  map_adj := fun _ _ => Iff.rfl

def symm {d : ℕ} (g : TreeAut d) : TreeAut d where
  toEquiv := g.toEquiv.symm
  map_adj := by
    intro u v
    simpa only [Equiv.apply_symm_apply] using
      (g.map_adj (g.toEquiv.symm u) (g.toEquiv.symm v)).symm

def trans {d : ℕ} (g h : TreeAut d) : TreeAut d where
  toEquiv := g.toEquiv.trans h.toEquiv
  map_adj := by
    intro u v
    exact (h.map_adj (g.toEquiv u) (g.toEquiv v)).trans (g.map_adj u v)

end TreeAut

def prefixFlipWord {α : Type*} [DecidableEq α] (c : α) : List α → List α
  | [] => [c]
  | a :: w => if c = a then w else c :: a :: w

theorem prefixFlipWord_chain {α : Type*} [DecidableEq α] (c : α)
    (w : List α) (hw : w.IsChain (· ≠ ·)) :
    (prefixFlipWord c w).IsChain (· ≠ ·) := by
  cases w with
  | nil => simp [prefixFlipWord]
  | cons a w =>
    by_cases h : c = a
    · simp only [prefixFlipWord, ite_eq_left h]
      exact hw.tail
    · simp only [prefixFlipWord, ite_eq_right h, List.isChain_cons_cons]
      exact ⟨h, hw⟩

theorem prefixFlipWord_involutive {α : Type*} [DecidableEq α] (c : α)
    (w : List α) (hw : w.IsChain (· ≠ ·)) :
    prefixFlipWord c (prefixFlipWord c w) = w := by
  cases w with
  | nil => simp [prefixFlipWord]
  | cons a w =>
    by_cases h : c = a
    · subst a
      cases w with
      | nil => simp [prefixFlipWord]
      | cons b w =>
        have hcb : c ≠ b := (List.isChain_cons_cons.mp hw).1
        simp [prefixFlipWord, hcb]
    · simp [prefixFlipWord, h]

def prefixFlip {d : ℕ} (c : Fin d) (w : TreeVertex d) : TreeVertex d :=
  ⟨prefixFlipWord c w.1, prefixFlipWord_chain c w.1 w.2⟩

@[simp] theorem prefixFlip_twice {d : ℕ} (c : Fin d) (w : TreeVertex d) :
    prefixFlip c (prefixFlip c w) = w := by
  apply Subtype.ext
  exact prefixFlipWord_involutive c w.1 w.2

theorem prefixFlipWord_append_adj {α : Type*} [DecidableEq α]
    (c a : α) (w : List α) :
    (∃ b, prefixFlipWord c (w ++ [a]) = prefixFlipWord c w ++ [b]) ∨
    (∃ b, prefixFlipWord c w = prefixFlipWord c (w ++ [a]) ++ [b]) := by
  cases w with
  | nil =>
    by_cases h : c = a
    · subst a
      right
      exact ⟨c, by simp [prefixFlipWord]⟩
    · left
      exact ⟨a, by simp [prefixFlipWord, h]⟩
  | cons b w =>
    left
    refine ⟨a, ?_⟩
    by_cases h : c = b <;> simp [prefixFlipWord, h]

theorem prefixFlip_adj {d : ℕ} (c : Fin d) {u v : TreeVertex d}
    (h : treeAdj u v) : treeAdj (prefixFlip c u) (prefixFlip c v) := by
  rcases h with ⟨a, h⟩ | ⟨a, h⟩
  · simpa only [treeAdj, prefixFlip, h] using prefixFlipWord_append_adj c a u.1
  · simpa only [treeAdj, prefixFlip, h, or_comm] using prefixFlipWord_append_adj c a v.1

def prefixTreeAut {d : ℕ} (c : Fin d) : TreeAut d where
  toEquiv :=
    { toFun := prefixFlip c
      invFun := prefixFlip c
      left_inv := prefixFlip_twice c
      right_inv := prefixFlip_twice c }
  map_adj := by
    intro u v
    constructor
    · intro h
      change treeAdj (prefixFlip c u) (prefixFlip c v) at h
      have h' := prefixFlip_adj c h
      simpa only [prefixFlip_twice] using h'
    · exact prefixFlip_adj c

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Array
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.CavityArray

variable {d : ℕ} {theta : ℝ}

def field (h0 : 0 ≤ theta) (h1 : theta < 1)
    (H : TreeVertex d → ℝ) (v w : TreeVertex d) : ℝ :=
  (cavityFromSites h0 h1 (H v, H w)).1

end Problem367.CavityArray

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteMarginals
attribute [-simp] _root_.OAI.Problem367.prefixFlip_twice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

def extendFiniteSpin {d : ℕ} (D : Finset (TreeVertex d))
    (eta : D → IsingSpin) : TreeVertex d → IsingSpin := by
  classical
  exact fun v => if hv : v ∈ D then eta ⟨v, hv⟩ else IsingSpin.neg

@[simp]
theorem extendFiniteSpin_apply {d : ℕ} (D : Finset (TreeVertex d))
    (eta : D → IsingSpin) (v : D) : extendFiniteSpin D eta v = eta v := by
  classical
  simp [extendFiniteSpin]

@[simp]
theorem restrict_extendFiniteSpin {d : ℕ} (D : Finset (TreeVertex d))
    (eta : D → IsingSpin) : D.restrict (extendFiniteSpin D eta) = eta := by
  funext v
  exact extendFiniteSpin_apply D eta v

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ConnectedHull
attribute [-simp] _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

namespace ConnectedHull

def root (d : ℕ) : TreeVertex d := ⟨[], List.IsChain.nil⟩

def takeVertex {d : ℕ} (v : TreeVertex d) (n : ℕ) : TreeVertex d :=
  ⟨v.1.take n, v.2.take n⟩

@[simp] theorem prefix_zero {d : ℕ} (v : TreeVertex d) : takeVertex v 0 = root d := by
  apply Subtype.ext
  simp [takeVertex, root]

@[simp] theorem prefix_length {d : ℕ} (v : TreeVertex d) :
    takeVertex v v.1.length = v := by
  apply Subtype.ext
  simp [takeVertex]

def vertices {d : ℕ} (v : TreeVertex d) : Finset (TreeVertex d) := by
  classical
  exact (Finset.range (v.1.length + 1)).image (takeVertex v)

def hull {d : ℕ} (D : Finset (TreeVertex d)) : Finset (TreeVertex d) := by
  classical
  exact insert (root d) (D.biUnion vertices)

theorem prefix_mem_hull {d : ℕ} {D : Finset (TreeVertex d)} {v : TreeVertex d}
    (hv : v ∈ D) {n : ℕ} (hn : n ≤ v.1.length) : takeVertex v n ∈ hull D := by
  classical
  apply Finset.mem_insert_of_mem
  apply Finset.mem_biUnion.mpr
  refine ⟨v, hv, ?_⟩
  exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (by omega), rfl⟩

theorem subset_hull {d : ℕ} (D : Finset (TreeVertex d)) : D ⊆ hull D := by
  intro v hv
  simpa using prefix_mem_hull hv (Nat.le_refl v.1.length)

end ConnectedHull

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Flip
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

def IsingSpin.flip : IsingSpin → IsingSpin
  | .neg => .pos
  | .pos => .neg

@[simp] theorem IsingSpin.flip_flip (s : IsingSpin) : s.flip.flip = s := by
  cases s <;> rfl

@[simp] theorem IsingSpin.flip_eq_iff (s t : IsingSpin) :
    s.flip = t ↔ s = t.flip := by
  cases s <;> cases t <;> simp [IsingSpin.flip]

def flipConfig {ι : Type*} (x : ι → IsingSpin) : ι → IsingSpin :=
  fun v => (x v).flip

@[simp] theorem flipConfig_apply {ι : Type*} (x : ι → IsingSpin) (v : ι) :
    flipConfig x v = (x v).flip := rfl

@[simp] theorem flipConfig_flipConfig {ι : Type*} (x : ι → IsingSpin) :
    flipConfig (flipConfig x) = x := by
  funext v
  exact IsingSpin.flip_flip (x v)

@[simp] theorem flipConfig_preimage_spin {ι : Type*} (v : ι) (s : IsingSpin) :
    flipConfig ⁻¹' {x : ι → IsingSpin | x v = s} =
      {x : ι → IsingSpin | x v = s.flip} := by
  ext x
  simp [flipConfig]

@[simp] theorem freeCylinderWeight_flipConfig {d : ℕ} (theta : ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D (flipConfig eta) = freeCylinderWeight theta D eta := by
  simp [freeCylinderWeight, flipConfig]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Kernel
attribute [-simp] _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.restrict_extendFiniteSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

@[simp] theorem isingSpin_neg_ne_pos : IsingSpin.neg ≠ IsingSpin.pos := by decide

@[simp] theorem isingSpin_pos_ne_neg : IsingSpin.pos ≠ IsingSpin.neg := by decide

theorem spinKernel_univ : (Finset.univ : Finset IsingSpin) = {.neg, .pos} := by decide

theorem sum_isingSpin {α : Type*} [AddCommMonoid α] (f : IsingSpin → α) :
    ∑ a : IsingSpin, f a = f .neg + f .pos := by
  simp [spinKernel_univ]

def spinSign : IsingSpin → ℝ
  | .neg => -1
  | .pos => 1

@[simp] theorem spinSign_neg : spinSign .neg = -1 := rfl
@[simp] theorem spinSign_pos : spinSign .pos = 1 := rfl

@[simp] theorem spinSign_sq (a : IsingSpin) : spinSign a ^ 2 = 1 := by
  cases a <;> norm_num [spinSign]

@[simp] theorem spinSign_mul_self (a : IsingSpin) : spinSign a * spinSign a = 1 := by
  simpa only [pow_two] using spinSign_sq a

def transitionKernel (theta : ℝ) (a b : IsingSpin) : ℝ :=
  (1 + theta * spinSign a * spinSign b) / 2

theorem transitionKernel_eq (theta : ℝ) (a b : IsingSpin) :
    transitionKernel theta a b = (1 + (if a = b then theta else -theta)) / 2 := by
  cases a <;> cases b <;> simp [transitionKernel, spinSign]

@[simp] theorem transitionKernel_zero (a b : IsingSpin) :
    transitionKernel 0 a b = (1 / 2 : ℝ) := by
  simp [transitionKernel]

@[simp] theorem transitionKernel_one (a b : IsingSpin) :
    transitionKernel 1 a b = if a = b then 1 else 0 := by
  cases a <;> cases b <;> norm_num [transitionKernel, spinSign]

@[simp] theorem sum_spinSign : ∑ a : IsingSpin, spinSign a = 0 := by
  simp [sum_isingSpin, spinSign]

@[simp] theorem transitionKernel_sum (theta : ℝ) (a : IsingSpin) :
    ∑ b : IsingSpin, transitionKernel theta a b = 1 := by
  rw [sum_isingSpin]
  simp only [transitionKernel, spinSign_neg, spinSign_pos]
  ring

@[simp] theorem transitionKernel_spinSum (theta : ℝ) (a : IsingSpin) :
    ∑ b : IsingSpin, transitionKernel theta a b * spinSign b = theta * spinSign a := by
  rw [sum_isingSpin]
  simp only [transitionKernel, spinSign_neg, spinSign_pos]
  ring

theorem transitionKernel_nonneg {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (a b : IsingSpin) : 0 ≤ transitionKernel theta a b := by
  rw [transitionKernel_eq]
  split_ifs <;> linarith

theorem freeCylinderWeight_eq_transitionKernel {d : ℕ} (theta : ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D eta = ENNReal.ofReal
      ((1 / 2 : ℝ) * ∏ e ∈ inducedEdges D, transitionKernel theta (eta e.1) (eta e.2)) := by
  simp only [freeCylinderWeight, transitionKernel_eq]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PlantedSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.PlantedSymmetry

def observation {ι : Type*} (t : ℝ) (p : (ι → IsingSpin) × (ι → ℝ)) : ι → ℝ :=
  fun v => t * spinSign (p.1 v) + p.2 v

end Problem367.PlantedSymmetry

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_PlantedInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem367.PlantedInformation

open PlantedSymmetry

variable {ι κ : Type*}

@[reducible] def observationSigma (v : ι → κ) (t : ℝ) :
    MeasurableSpace ((κ → IsingSpin) × (κ → ℝ)) :=
  MeasurableSpace.comap (fun p i => observation t p (v i)) inferInstance

end Problem367.PlantedInformation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Shells
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

abbrev ReducedTail {d : ℕ} (c : Fin d) (n : ℕ) :=
  {w : List (Fin d) // w.length = n ∧ List.IsChain (fun a b => a ≠ b) (c :: w)}

abbrev TreeShell (d n : ℕ) := {v : TreeVertex d // v.1.length = n}

instance reducedTailFinite {d : ℕ} (c : Fin d) (n : ℕ) : Finite (ReducedTail c n) :=
  Finite.of_injective (β := List.Vector (Fin d) n)
    (fun w : ReducedTail c n => (⟨w.1, w.2.1⟩ : List.Vector (Fin d) n))
    (fun _ _ h => Subtype.ext (congrArg (fun w : List.Vector (Fin d) n => w.1) h))

instance reducedTailFintype {d : ℕ} (c : Fin d) (n : ℕ) : Fintype (ReducedTail c n) :=
  Fintype.ofFinite _

instance treeShellFinite (d n : ℕ) : Finite (TreeShell d n) :=
  Finite.of_injective (β := List.Vector (Fin d) n)
    (fun w : TreeShell d n => (⟨w.1.1, w.2⟩ : List.Vector (Fin d) n))
    (fun _ _ h => Subtype.ext (Subtype.ext
      (congrArg (fun w : List.Vector (Fin d) n => w.1) h)))

instance treeShellFintype (d n : ℕ) : Fintype (TreeShell d n) :=
  Fintype.ofFinite _

def reducedTailSuccEquiv {d : ℕ} (c : Fin d) (n : ℕ) :
    ReducedTail c (n + 1) ≃ Σ a : {a : Fin d // c ≠ a}, ReducedTail a.1 n where
  toFun w := by
    rcases w with ⟨w, hlen, hchain⟩
    cases w with
    | nil => simp at hlen
    | cons a w =>
      exact ⟨⟨a, (List.isChain_cons_cons.mp hchain).1⟩,
        ⟨w, by simpa using hlen, (List.isChain_cons_cons.mp hchain).2⟩⟩
  invFun w := ⟨w.1.1 :: w.2.1,
    by simp [w.2.2.1], List.isChain_cons_cons.mpr ⟨w.1.2, w.2.2.2⟩⟩
  left_inv w := by
    rcases w with ⟨w, hlen, hchain⟩
    cases w with
    | nil => simp at hlen
    | cons a w => rfl
  right_inv w := by
    rcases w with ⟨⟨a, ha⟩, ⟨w, hlen, hchain⟩⟩
    rfl

def treeShellSuccEquiv (d n : ℕ) :
    TreeShell d (n + 1) ≃ Σ c : Fin d, ReducedTail c n where
  toFun w := by
    rcases w with ⟨⟨w, hchain⟩, hlen⟩
    cases w with
    | nil => simp at hlen
    | cons a w => exact ⟨a, ⟨w, by simpa using hlen, hchain⟩⟩
  invFun w := ⟨⟨w.1 :: w.2.1, w.2.2.2⟩, by simp [w.2.2.1]⟩
  left_inv w := by
    rcases w with ⟨⟨w, hchain⟩, hlen⟩
    cases w with
    | nil => simp at hlen
    | cons a w => rfl
  right_inv w := by
    rcases w with ⟨a, ⟨w, hlen, hchain⟩⟩
    rfl

def reducedTailZeroEquiv {d : ℕ} (c : Fin d) : ReducedTail c 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], by simp⟩
  left_inv w := by
    apply Subtype.ext
    exact (List.length_eq_zero_iff.mp w.2.1).symm
  right_inv _ := rfl

def treeShellZeroEquiv (d : ℕ) : TreeShell d 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨⟨[], by simp⟩, rfl⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    exact (List.length_eq_zero_iff.mp w.2).symm
  right_inv _ := rfl

@[simp] theorem card_reducedTail {d : ℕ} (c : Fin d) (n : ℕ) :
    Fintype.card (ReducedTail c n) = (d - 1) ^ n := by
  induction n generalizing c with
  | zero =>
    simpa using Fintype.card_congr (reducedTailZeroEquiv c)
  | succ n ih =>
    rw [Fintype.card_congr (reducedTailSuccEquiv c n), Fintype.card_sigma]
    simp only [ih]
    have hc : Fintype.card {a : Fin d // c ≠ a} = d - 1 := by
      simp
    simp [hc, pow_succ, Nat.mul_comm]

@[simp] theorem card_treeShell_zero (d : ℕ) : Fintype.card (TreeShell d 0) = 1 := by
  simpa using Fintype.card_congr (treeShellZeroEquiv d)

@[simp] theorem card_treeShell_succ (d n : ℕ) :
    Fintype.card (TreeShell d (n + 1)) = d * (d - 1) ^ n := by
  rw [Fintype.card_congr (treeShellSuccEquiv d n), Fintype.card_sigma]
  simp

abbrev TreeBall (d n : ℕ) := {v : TreeVertex d // v.1.length ≤ n}

def treeBallEquivSigma (d n : ℕ) :
    TreeBall d n ≃ Σ k : Fin (n + 1), TreeShell d k.1 where
  toFun w := ⟨⟨w.1.1.length, Nat.lt_succ_of_le w.2⟩, ⟨w.1, rfl⟩⟩
  invFun w := ⟨w.2.1, by
    rw [w.2.2]
    exact Nat.le_of_lt_succ w.1.2⟩
  left_inv _ := rfl
  right_inv w := by
    rcases w with ⟨⟨k, hk⟩, ⟨v, hv⟩⟩
    cases hv
    rfl

instance treeBallFinite (d n : ℕ) : Finite (TreeBall d n) :=
  Finite.of_equiv (Σ k : Fin (n + 1), TreeShell d k.1) (treeBallEquivSigma d n).symm

instance treeBallFintype (d n : ℕ) : Fintype (TreeBall d n) := Fintype.ofFinite _

@[simp] theorem card_treeBall (d n : ℕ) :
    Fintype.card (TreeBall d n) = 1 + d * ∑ k ∈ Finset.range n, (d - 1) ^ k := by
  rw [Fintype.card_congr (treeBallEquivSigma d n), Fintype.card_sigma]
  rw [Fin.sum_univ_eq_sum_range (fun k => Fintype.card (TreeShell d k)),
    Finset.sum_range_succ']
  simp [Finset.mul_sum, Nat.add_comm]

def treeBallFinset (d n : ℕ) : Finset (TreeVertex d) :=
  Finset.univ.map ⟨fun v : TreeBall d n => v.1, Subtype.val_injective⟩

@[simp] theorem mem_treeBallFinset (d n : ℕ) (v : TreeVertex d) :
    v ∈ treeBallFinset d n ↔ v.1.length ≤ n := by
  simp [treeBallFinset]

@[simp] theorem card_treeBallFinset (d n : ℕ) :
    (treeBallFinset d n).card = 1 + d * ∑ k ∈ Finset.range n, (d - 1) ^ k := by
  simp [treeBallFinset]

@[simp] theorem iUnion_treeBallFinset (d : ℕ) :
    (⋃ n : ℕ, (treeBallFinset d n : Set (TreeVertex d))) = Set.univ := by
  ext v
  simp only [Set.mem_iUnion, Finset.mem_coe, mem_treeBallFinset, Set.mem_univ, iff_true]
  exact ⟨v.1.length, le_rfl⟩

@[simp] theorem sum_treeShell_zero {M : Type*} [AddCommMonoid M]
    (d : ℕ) (f : List (Fin d) → M) : (∑ v : TreeShell d 0, f v.1.1) = f [] := by
  calc
    (∑ v : TreeShell d 0, f v.1.1) = ∑ _ : Unit, f [] :=
      ((treeShellZeroEquiv d).symm.sum_comp (fun v => f v.1.1)).symm
    _ = _ := by simp

@[simp] theorem sum_reducedTail_zero {M : Type*} [AddCommMonoid M]
    {d : ℕ} (c : Fin d) (f : List (Fin d) → M) :
    (∑ w : ReducedTail c 0, f w.1) = f [] := by
  calc
    (∑ w : ReducedTail c 0, f w.1) = ∑ _ : Unit, f [] :=
      ((reducedTailZeroEquiv c).symm.sum_comp (fun w => f w.1)).symm
    _ = _ := by simp

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_CylinderBasics
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem connectedFinset_singleton {d : ℕ} (v : TreeVertex d) :
    ConnectedFinset {v} := by
  classical
  refine ⟨Finset.singleton_nonempty v, ?_⟩
  intro x hx y hy
  simp only [Finset.mem_singleton] at hx hy
  subst x
  subst y
  exact Relation.ReflTransGen.refl

@[simp] theorem inducedEdges_singleton {d : ℕ} (v : TreeVertex d) :
    inducedEdges {v} = ∅ := by
  classical
  ext e
  simp [inducedEdges]
  rintro rfl
  simp

@[simp] theorem freeCylinderWeight_singleton {d : ℕ} (θ : ℝ)
    (v : TreeVertex d) (η : TreeVertex d → IsingSpin) :
    freeCylinderWeight θ {v} η = ENNReal.ofReal (1 / 2 : ℝ) := by
  classical
  simp [freeCylinderWeight]

theorem HasFreeIsingLaw.marginal {d : ℕ} {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (v : TreeVertex d) (s : IsingSpin) :
    μ {x | x v = s} = ENNReal.ofReal (1 / 2 : ℝ) := by
  classical
  simpa using hμ {v} (connectedFinset_singleton v) (fun _ => s)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Moments
attribute [-instance] _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

def IsingSpin.toReal : IsingSpin → ℝ
  | .neg => -1
  | .pos => 1

@[simp] lemma IsingSpin.toReal_neg : IsingSpin.toReal .neg = -1 := rfl
@[simp] lemma IsingSpin.toReal_pos : IsingSpin.toReal .pos = 1 := rfl

local instance spinMomentsMeasurableSingleton : MeasurableSingletonClass IsingSpin where
  measurableSet_singleton _ := trivial

lemma measurable_spinToReal : Measurable IsingSpin.toReal := measurable_of_finite _

lemma measurable_spinEvent {d : ℕ} (v : TreeVertex d) (s : IsingSpin) :
    MeasurableSet {x : TreeVertex d → IsingSpin | x v = s} :=
  measurableSet_eq_fun (measurable_pi_apply v) measurable_const

lemma HasFreeIsingLaw.isProbabilityMeasure {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (h : HasFreeIsingLaw theta mu) :
    IsProbabilityMeasure mu := by
  let v : TreeVertex d := ⟨[], List.isChain_nil⟩
  have hu : (Set.univ : Set (TreeVertex d → IsingSpin)) =
      {x | x v = IsingSpin.neg} ∪ {x | x v = IsingSpin.pos} := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_ofPred_eq, true_iff]
    cases x v <;> simp
  have hd : Disjoint {x : TreeVertex d → IsingSpin | x v = IsingSpin.neg}
      {x | x v = IsingSpin.pos} := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact IsingSpin.noConfusion (hx.symm.trans hy)
  constructor
  rw [hu, measure_union hd (measurable_spinEvent v .pos),
    h.marginal v .neg, h.marginal v .pos]
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using ENNReal.add_halves 1

lemma norm_spinToReal (s : IsingSpin) : ‖s.toReal‖ = 1 := by
  cases s <;> norm_num [IsingSpin.toReal]

lemma HasFreeIsingLaw.integral_spin {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (h : HasFreeIsingLaw theta mu)
    (v : TreeVertex d) : ∫ x, (x v).toReal ∂mu = 0 := by
  let := h.isProbabilityMeasure
  have hf : (fun x : TreeVertex d → IsingSpin => (x v).toReal) =
      (fun x => ({x | x v = IsingSpin.pos} : Set (TreeVertex d → IsingSpin)).indicator (fun _ => (2 : ℝ)) x - 1) := by
    funext x
    cases hv : x v <;> simp [hv, Set.indicator, IsingSpin.toReal]
    norm_num
  rw [hf, integral_sub]
  · rw [integral_indicator_const _ (measurable_spinEvent v .pos), integral_const]
    simp [Measure.real, h.marginal v .pos]
  · exact (integrable_const (2 : ℝ)).indicator (measurable_spinEvent v .pos)
  · exact integrable_const 1

lemma HasFreeIsingLaw.integral_factor_spin {d : ℕ} {theta : ℝ}
    {Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin)}
    (hPhi : Measurable Phi)
    (h : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (v : TreeVertex d) : ∫ U, (Phi U v).toReal ∂labelMeasure d = 0 := by
  have hm : Measurable (fun x : TreeVertex d → IsingSpin => (x v).toReal) :=
    measurable_spinToReal.comp (measurable_pi_apply v)
  exact (integral_map (μ := labelMeasure d) hPhi.aemeasurable hm.aestronglyMeasurable).symm.trans
    (h.integral_spin v)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathCylinders
attribute [-simp] _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
namespace Problem367
namespace ConnectedHull

theorem prefix_length_eq {d : ℕ} (v : TreeVertex d) {n : ℕ}
    (hn : n ≤ v.1.length) : (takeVertex v n).1.length = n := by
  simp [takeVertex, Nat.min_eq_left hn]

theorem mem_vertices {d : ℕ} {v u : TreeVertex d} :
    u ∈ vertices v ↔ ∃ n ≤ v.1.length, takeVertex v n = u := by
  classical
  simp only [vertices, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, heq⟩
    exact ⟨n, by omega, heq⟩
  · rintro ⟨n, hn, heq⟩
    exact ⟨n, by omega, heq⟩

theorem prefix_mem_vertices {d : ℕ} (v : TreeVertex d) {n : ℕ}
    (hn : n ≤ v.1.length) : takeVertex v n ∈ vertices v :=
  mem_vertices.mpr ⟨n, hn, rfl⟩

def path {d : ℕ} (v : TreeVertex d) (i : Fin (v.1.length+1)) : TreeVertex d :=
  takeVertex v i

theorem path_injective {d : ℕ} (v : TreeVertex d) : Function.Injective (path v) := by
  intro i j h
  apply Fin.ext
  have hl := congrArg (fun x : TreeVertex d => x.1.length) h
  simpa only [path, prefix_length_eq v (Nat.le_of_lt_succ i.isLt),
    prefix_length_eq v (Nat.le_of_lt_succ j.isLt)] using hl

def pathAssignment {d : ℕ} (v : TreeVertex d)
    (eta : Fin (v.1.length+1) → IsingSpin) (u : TreeVertex d) : IsingSpin :=
  if h : u.1.length ≤ v.1.length then eta ⟨u.1.length, by omega⟩ else .neg

@[simp] theorem pathAssignment_path {d : ℕ} (v : TreeVertex d)
    (eta : Fin (v.1.length+1) → IsingSpin) (i : Fin (v.1.length+1)) :
    pathAssignment v eta (path v i) = eta i := by
  unfold pathAssignment path
  have hi := Nat.le_of_lt_succ i.isLt
  simp only [prefix_length_eq v hi, dite_eq_left hi]

end ConnectedHull
namespace ConnectedHull

@[simp] theorem path_zero {d : ℕ} (v : TreeVertex d) :
    path v 0 = root d := prefix_zero v

@[simp] theorem path_last {d : ℕ} (v : TreeVertex d) :
    path v (Fin.last v.1.length) = v := prefix_length v

end ConnectedHull

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

def componentVertex {d n : ℕ} {c : Fin d} (u : ReducedTail c n) : TreeVertex d :=
  ⟨c :: u.1, u.2.2⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ComponentInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal

namespace Problem367

abbrev ComponentIndex {d : ℕ} (c : Fin d) := Σ n : ℕ, ReducedTail c n

def componentIndexVertex {d : ℕ} {c : Fin d} (u : ComponentIndex c) : TreeVertex d :=
  componentVertex u.2

theorem componentIndexVertex_injective {d : ℕ} (c : Fin d) :
    Function.Injective (componentIndexVertex (c := c)) := by
  rintro ⟨k, u⟩ ⟨l, v⟩ h
  have hw : u.1 = v.1 := (List.cons.inj (congrArg Subtype.val h)).2
  have hkl : k = l := by
    simpa only [u.2.1, v.2.1] using congrArg List.length hw
  subst l
  have huv : u = v := Subtype.ext hw
  subst v
  rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_GaussianVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

namespace Problem367.ConditionalGaussianVector

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

section FiniteVector

variable {ι : Type*} [Fintype ι]

theorem condExp_linear_character_of_unit_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → ι → ℝ} (v : ℝ≥0)
    (hchar : ∀ a : ι → ℝ, (∑ i, (a i) ^ 2) = 1 → ∀ u : ℝ,
      P[ConditionalCharacteristic.character (fun ω => ∑ i, a i * X ω i) u | m] =ᵐ[P]
        fun _ => Complex.exp (-((v : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2)) :
    ∀ a : ι → ℝ,
      P[(fun ω => Complex.exp (((∑ i, a i * X ω i : ℝ) : ℂ) * Complex.I)) | m] =ᵐ[P]
        fun _ => Complex.exp (-((∑ i, (v : ℝ) * (a i) ^ 2 : ℝ) : ℂ) / 2) := by
  classical
  intro a
  by_cases hz : (∑ i, (a i) ^ 2) = 0
  · have ha : ∀ i, a i = 0 := by
      intro i
      have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (a j))).mp hz
      exact sq_eq_zero_iff.mp (hs i (Finset.mem_univ i))
    simpa [ha] using
      Filter.EventuallyEq.of_eq (condExp_const (μ := P) hm (1 : ℂ))
  let q : ℝ := Real.sqrt (∑ i, (a i) ^ 2)
  have hsq : 0 < ∑ i, (a i) ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg (a i))) (Ne.symm hz)
  have hq : 0 < q := Real.sqrt_pos.mpr hsq
  have hq2 : q ^ 2 = ∑ i, (a i) ^ 2 := Real.sq_sqrt hsq.le
  let b : ι → ℝ := fun i => a i / q
  have hb : (∑ i, (b i) ^ 2) = 1 := by
    simp only [b, div_pow, ← Finset.sum_div, hq2]
    exact div_self hz
  have heq : ConditionalCharacteristic.character (fun ω => ∑ i, b i * X ω i) q =
      (fun ω => Complex.exp (((∑ i, a i * X ω i : ℝ) : ℂ) * Complex.I)) := by
    funext ω
    have hs : q * (∑ i, b i * X ω i) = ∑ i, a i * X ω i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [b]
      field_simp
    simp only [ConditionalCharacteristic.character, ← Complex.ofReal_mul, hs]
  have h := hchar b hb q
  rw [heq] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  congr 1
  rw [← Complex.ofReal_pow, hq2, ← Finset.mul_sum]
  push_cast
  ring

theorem condExp_weighted_character_of_unit_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → ι → ℝ} (v : ℝ≥0)
    (hchar : ∀ a : ι → ℝ, (∑ i, (a i) ^ 2) = 1 → ∀ u : ℝ,
      P[ConditionalCharacteristic.character (fun ω => ∑ i, a i * X ω i) u | m] =ᵐ[P]
        fun _ => Complex.exp (-((v : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2)) :
    ∀ a : ι → ℝ,
      P[ConditionalCharacteristic.character (fun ω => ∑ i, a i * X ω i) 1 | m] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i, ((v : ℝ) : ℂ) * (a i : ℂ)^2) / 2) := by
  intro a
  have he : ConditionalCharacteristic.character (fun ω => ∑ i, a i * X ω i) 1 =
      (fun ω => Complex.exp (((∑ i, a i * X ω i : ℝ) : ℂ) * Complex.I)) := by
    funext ω
    simp [ConditionalCharacteristic.character]
  rw [he]
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow] using
    condExp_linear_character_of_unit_character hm v hchar a

end FiniteVector

end Problem367.ConditionalGaussianVector

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_InnovationConditionalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.InnovationConditionalMoments

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem integral_abs_condExp_sub_const_le [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} {X Y : Ω → ℝ} {c : ℝ}
    (hX : Integrable X P) (hY : Integrable Y P)
    (hmean : P[Y | m] =ᵐ[P] fun _ => c) :
    (∫ ω, |P[X | m] ω - c| ∂P) ≤ ∫ ω, |X ω - Y ω| ∂P := by
  have heq : (fun ω => P[X | m] ω - c) =ᵐ[P] P[X - Y | m] := by
    filter_upwards [condExp_sub hX hY m, hmean] with ω hsub hy
    simpa only [Pi.sub_apply, hy] using hsub.symm
  calc
    (∫ ω, |P[X | m] ω - c| ∂P) = ∫ ω, |P[X - Y | m] ω| ∂P :=
      integral_congr_ae (heq.fun_comp abs)
    _ ≤ ∫ ω, |X ω - Y ω| ∂P := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        (integral_norm_condExp_le (μ := P) (m := m) (X - Y))

theorem integral_smul_eq_integral_condExp_smul [IsFiniteMeasure P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f : Ω → ℝ} (hf : Integrable f P)
    {Z : Ω → E} (hZ : StronglyMeasurable[m] Z) {C : ℝ}
    (hbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) :
    (∫ ω, f ω • Z ω ∂P) = ∫ ω, P[f | m] ω • Z ω ∂P := by
  have hprod : Integrable (f • Z) P :=
    hf.smul_bdd C (hZ.mono hm).aestronglyMeasurable hbound
  calc
    (∫ ω, f ω • Z ω ∂P) = ∫ ω, P[f • Z | m] ω ∂P :=
      (integral_condExp hm).symm
    _ = ∫ ω, P[f | m] ω • Z ω ∂P :=
      integral_congr_ae
        (condExp_smul_of_aestronglyMeasurable_right hf hprod hZ.aestronglyMeasurable)

theorem norm_integral_smul_le_conditional_abs [IsFiniteMeasure P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f : Ω → ℝ} (hf : Integrable f P)
    {Z : Ω → E} (hZ : StronglyMeasurable[m] Z) {C : ℝ}
    (hbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) :
    ‖∫ ω, f ω • Z ω ∂P‖ ≤ C * ∫ ω, |P[f | m] ω| ∂P := by
  rw [integral_smul_eq_integral_condExp_smul (mΩ := mΩ) hm hf hZ hbound]
  calc
    ‖∫ ω, P[f | m] ω • Z ω ∂P‖ ≤ ∫ ω, C * |P[f | m] ω| ∂P := by
      apply norm_integral_le_of_norm_le (integrable_condExp.abs.const_mul C)
      filter_upwards [hbound] with ω hω
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg (P[f | m] ω)]
    _ = C * ∫ ω, |P[f | m] ω| ∂P := integral_const_mul _ _

theorem norm_integral_test_sub_const_le [IsFiniteMeasure P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X Y : Ω → ℝ} {c : ℝ}
    (hX : Integrable X P) (hY : Integrable Y P)
    (hmean : P[Y | m] =ᵐ[P] fun _ => c)
    {Z : Ω → E} (hZ : StronglyMeasurable[m] Z) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) :
    ‖∫ ω, (X ω - c) • Z ω ∂P‖ ≤ C * ∫ ω, |X ω - Y ω| ∂P := by
  have hce : P[(fun ω => X ω - c) | m] =ᵐ[P]
      fun ω => P[X | m] ω - c := by
    have h := condExp_sub hX (integrable_const c) m
    rw [condExp_const hm] at h
    exact h
  calc
    ‖∫ ω, (X ω - c) • Z ω ∂P‖ ≤
        C * ∫ ω, |P[(fun ω => X ω - c) | m] ω| ∂P :=
      norm_integral_smul_le_conditional_abs (mΩ := mΩ) hm
        (hX.sub (integrable_const c)) hZ hbound
    _ = C * ∫ ω, |P[X | m] ω - c| ∂P := by
      congr 1
      exact integral_congr_ae (hce.fun_comp abs)
    _ ≤ C * ∫ ω, |X ω - Y ω| ∂P :=
      mul_le_mul_of_nonneg_left
        (integral_abs_condExp_sub_const_le (mΩ := mΩ) hX hY hmean) hC

end Problem367.InnovationConditionalMoments

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_DiscrepancyRowEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Problem367.DiscrepancyEnergy

def density {Ω ι : Type*} (c c' : ι → Ω → ℝ) (X m m' : Ω → ℝ) (ω : Ω) : ℝ :=
  (∑' i, (c i ω - c' i ω) ^ 2) +
    2 * X ω * (m ω * (∑' i, (c i ω) ^ 2) - m' ω * (∑' i, (c' i ω) ^ 2))

end Problem367.DiscrepancyEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LeafDeletion
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem reflTransGen_erase_of_unique_neighbor
    {α : Type*} [DecidableEq α] {D : Finset α} {R : α → α → Prop}
    {v p a b : α}
    (hsymm : ∀ {x y}, R x y → R y x)
    (hp : p ∈ D) (hpv : p ≠ v)
    (hleaf : ∀ x ∈ D, R v x → x = p)
    (ha : a ∈ D.erase v) (hb : b ∈ D.erase v)
    (hab : Relation.ReflTransGen (fun x y => x ∈ D ∧ y ∈ D ∧ R x y) a b) :
    Relation.ReflTransGen
      (fun x y => x ∈ D.erase v ∧ y ∈ D.erase v ∧ R x y) a b := by
  let f : α → α := fun x => if x = v then p else x
  have hf : ∀ x ∈ D, f x ∈ D.erase v := by
    intro x hx
    by_cases hxv : x = v
    · simp [f, hxv, hpv, hp]
    · simp [f, hxv, hx]
  have hstep : ∀ x y, x ∈ D ∧ y ∈ D ∧ R x y →
      Relation.ReflTransGen
        (fun x y => x ∈ D.erase v ∧ y ∈ D.erase v ∧ R x y) (f x) (f y) := by
    intro x y hxy
    by_cases hxv : x = v
    · have hyp : y = p := hleaf y hxy.2.1 (hxv ▸ hxy.2.2)
      subst x
      subst y
      simp only [f, ite_eq_left rfl, ite_eq_right hpv]
      exact Relation.ReflTransGen.refl
    · by_cases hyv : y = v
      · have hxp : x = p := hleaf x hxy.1 (hsymm (hyv ▸ hxy.2.2))
        subst y
        subst x
        simp only [f, ite_eq_left rfl, ite_eq_right hpv]
        exact Relation.ReflTransGen.refl
      · apply Relation.ReflTransGen.single
        exact ⟨hf x hxy.1, hf y hxy.2.1, by simpa [f, hxv, hyv] using hxy.2.2⟩
  have h := Relation.ReflTransGen.lift' f hstep a b hab
  simpa [Function.onFun, f, (Finset.mem_erase.mp ha).1, (Finset.mem_erase.mp hb).1] using h

theorem reflTransGen_connected_erase_of_leaf
    {α : Type*} [DecidableEq α] {D : Finset α} {R : α → α → Prop} {v : α}
    (hsymm : ∀ {x y}, R x y → R y x)
    (hirrefl : ∀ x, ¬ R x x)
    (hconn : ∀ a ∈ D, ∀ b ∈ D,
      Relation.ReflTransGen (fun x y => x ∈ D ∧ y ∈ D ∧ R x y) a b)
    (hv : v ∈ D) (hn : (D.erase v).Nonempty)
    (hleaf : ∀ x ∈ D, ∀ y ∈ D, R v x → R v y → x = y) :
    ∀ a ∈ D.erase v, ∀ b ∈ D.erase v,
      Relation.ReflTransGen
        (fun x y => x ∈ D.erase v ∧ y ∈ D.erase v ∧ R x y) a b := by
  obtain ⟨q, hq⟩ := hn
  obtain h | ⟨p, hvp, _⟩ := (hconn v hv q (Finset.mem_erase.mp hq).2).cases_head
  · exact False.elim ((Finset.mem_erase.mp hq).1 h.symm)
  · have hpv : p ≠ v := by
      intro h
      subst p
      exact hirrefl v hvp.2.2
    intro a ha b hb
    exact reflTransGen_erase_of_unique_neighbor hsymm hvp.2.1 hpv
      (fun x hx hxv => hleaf x hx p hvp.2.1 hxv hvp.2.2) ha hb
      (hconn a (Finset.mem_erase.mp ha).2 b (Finset.mem_erase.mp hb).2)

theorem connectedFinset_erase_of_leaf
    {d : ℕ} {D : Finset (TreeVertex d)} {v : TreeVertex d}
    (hD : ConnectedFinset D) (hv : v ∈ D) (hn : (D.erase v).Nonempty)
    (hleaf : ∀ x ∈ D, ∀ y ∈ D, treeAdj v x → treeAdj v y → x = y) :
    ConnectedFinset (D.erase v) := by
  refine ⟨hn, reflTransGen_connected_erase_of_leaf ?_ ?_ hD.2 hv hn hleaf⟩
  · intro x y h
    exact h.elim Or.inr Or.inl
  · intro x h
    rcases h with ⟨c, h⟩ | ⟨c, h⟩ <;>
      have := congrArg List.length h <;> simp at this

theorem treeAdj_unique_neighbor_of_max_length
    {d : ℕ} {D : Finset (TreeVertex d)} {v : TreeVertex d}
    (hmax : ∀ x ∈ D, x.1.length ≤ v.1.length) :
    ∀ x ∈ D, ∀ y ∈ D, treeAdj v x → treeAdj v y → x = y := by
  have hlower : ∀ x ∈ D, treeAdj v x → ∃ c : Fin d, v.1 = x.1 ++ [c] := by
    intro x hx hadj
    rcases hadj with ⟨c, hc⟩ | h
    · have hlen := congrArg List.length hc
      have hbound := hmax x hx
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    · exact h
  intro x hx y hy hvx hvy
  obtain ⟨c, hc⟩ := hlower x hx hvx
  obtain ⟨e, he⟩ := hlower y hy hvy
  apply Subtype.ext
  have h := congrArg List.dropLast (hc.symm.trans he)
  simpa using h

theorem connectedFinset_erase_of_max_length
    {d : ℕ} {D : Finset (TreeVertex d)} {v : TreeVertex d}
    (hD : ConnectedFinset D) (hv : v ∈ D) (hn : (D.erase v).Nonempty)
    (hmax : ∀ x ∈ D, x.1.length ≤ v.1.length) :
    ConnectedFinset (D.erase v) :=
  connectedFinset_erase_of_leaf hD hv hn (treeAdj_unique_neighbor_of_max_length hmax)

theorem inducedEdges_eq_insert_erase_of_max_length
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (hv : v ∈ D) (hp : p ∈ D) (hpv : treeAdj p v)
    (hplen : p.1.length < v.1.length)
    (hmax : ∀ x ∈ D, x.1.length ≤ v.1.length) :
    inducedEdges D = insert (p, v) (inducedEdges (D.erase v)) := by
  classical
  ext e
  rcases e with ⟨x, y⟩
  simp only [inducedEdges, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_insert, Prod.mk.injEq, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hx, hy⟩, hxy, hlen⟩
    have hxv : x ≠ v := by
      intro h
      subst x
      have := hmax y hy
      omega
    by_cases hyv : y = v
    · left
      refine ⟨?_, hyv⟩
      apply treeAdj_unique_neighbor_of_max_length hmax x hx p hp
      · exact (hyv ▸ hxy).elim Or.inr Or.inl
      · exact hpv.elim Or.inr Or.inl
    · exact Or.inr ⟨⟨⟨hxv, hx⟩, ⟨hyv, hy⟩⟩, hxy, hlen⟩
  · rintro (⟨rfl, rfl⟩ | ⟨⟨⟨_, hx⟩, ⟨_, hy⟩⟩, hxy, hlen⟩)
    · exact ⟨⟨hp, hv⟩, hpv, hplen⟩
    · exact ⟨⟨hx, hy⟩, hxy, hlen⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LeafWeights
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem leafWeight_congr_on {d : ℕ} (theta : ℝ)
    (D : Finset (TreeVertex d)) {eta eta' : TreeVertex d → IsingSpin}
    (h : ∀ v ∈ D, eta v = eta' v) :
    freeCylinderWeight theta D eta = freeCylinderWeight theta D eta' := by
  classical
  apply congrArg ENNReal.ofReal
  apply congrArg ((1 / 2 : ℝ) * ·)
  apply Finset.prod_congr rfl
  intro e he
  have hm := (Finset.mem_filter.mp he).1
  rw [Finset.product_eq_sprod] at hm
  have hmem := Finset.mem_product.mp hm
  rw [h e.1 hmem.1, h e.2 hmem.2]

theorem freeCylinderWeight_eq_mul_erase_of_edges
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D eta =
      freeCylinderWeight theta (D.erase v) eta *
        ENNReal.ofReal (transitionKernel theta (eta p) (eta v)) := by
  classical
  have hnot : (p, v) ∉ inducedEdges (D.erase v) := by
    simp [inducedEdges, Finset.product_eq_sprod]
  rw [freeCylinderWeight_eq_transitionKernel,
    hedges,
    Finset.prod_insert hnot, freeCylinderWeight_eq_transitionKernel]
  rw [show (1 / 2 : ℝ) * (transitionKernel theta (eta p) (eta v) *
      ∏ e ∈ inducedEdges (D.erase v), transitionKernel theta (eta e.1) (eta e.2)) =
      ((1 / 2 : ℝ) * ∏ e ∈ inducedEdges (D.erase v),
        transitionKernel theta (eta e.1) (eta e.2)) *
      transitionKernel theta (eta p) (eta v) by ring]
  exact ENNReal.ofReal_mul (by
    apply mul_nonneg (by norm_num)
    apply Finset.prod_nonneg
    intro e he
    exact transitionKernel_nonneg hlo hhi _ _)

theorem freeCylinderWeight_update_erase {d : ℕ} (theta : ℝ)
    (D : Finset (TreeVertex d)) (v : TreeVertex d)
    (eta : TreeVertex d → IsingSpin) (s : IsingSpin) :
    freeCylinderWeight theta (D.erase v) (Function.update eta v s) =
      freeCylinderWeight theta (D.erase v) eta := by
  apply leafWeight_congr_on
  intro x hx
  exact Function.update_of_ne (Finset.mem_erase.mp hx).1 _ _

theorem sum_ofReal_transitionKernel {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (a : IsingSpin) :
    ∑ s : IsingSpin, ENNReal.ofReal (transitionKernel theta a s) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => transitionKernel_nonneg hlo hhi a s)]
  simp

theorem freeCylinderWeight_sum_update_of_edges
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    ∑ s : IsingSpin, freeCylinderWeight theta D (Function.update eta v s) =
      freeCylinderWeight theta (D.erase v) eta := by
  simp_rw [freeCylinderWeight_eq_mul_erase_of_edges hlo hhi hedges,
    freeCylinderWeight_update_erase, Function.update_of_ne hpne, Function.update_self]
  rw [← Finset.mul_sum, sum_ofReal_transitionKernel hlo hhi, mul_one]

theorem freeCylinderWeight_sum_update_leaf
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (hv : v ∈ D) (hp : p ∈ D) (hpv : treeAdj p v)
    (hplen : p.1.length < v.1.length)
    (hmax : ∀ x ∈ D, x.1.length ≤ v.1.length)
    (eta : TreeVertex d → IsingSpin) :
    ∑ s : IsingSpin, freeCylinderWeight theta D (Function.update eta v s) =
      freeCylinderWeight theta (D.erase v) eta := by
  have hpne : p ≠ v := by
    intro h
    subst p
    exact (lt_irrefl _ hplen)
  exact freeCylinderWeight_sum_update_of_edges hlo hhi hpne
    (inducedEdges_eq_insert_erase_of_max_length hv hp hpv hplen hmax) eta

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteWeightNormalization
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.sum_treeShell_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def finiteSpinEraseEquiv {d : ℕ} {D : Finset (TreeVertex d)} {v : TreeVertex d}
    (hv : v ∈ D) : (D → IsingSpin) ≃ ((D.erase v → IsingSpin) × IsingSpin) := by
  classical
  exact
    { toFun := fun f => ⟨(fun x => f ⟨x.1, (Finset.mem_erase.mp x.2).2⟩), f ⟨v, hv⟩⟩
      invFun := fun f x => if h : x.1 = v then f.2 else
        f.1 ⟨x.1, Finset.mem_erase.mpr ⟨h, x.2⟩⟩
      left_inv := by
        intro f
        funext x
        dsimp
        split_ifs with h
        · congr 1
          exact Subtype.ext h.symm
        · rfl
      right_inv := by
        intro f
        apply Prod.ext
        · funext x
          simp [(Finset.mem_erase.mp x.2).1]
        · simp }

theorem extendFiniteSpin_eraseEquiv_symm
    {d : ℕ} {D : Finset (TreeVertex d)} {v : TreeVertex d} (hv : v ∈ D)
    (eta : D.erase v → IsingSpin) (s : IsingSpin) :
    extendFiniteSpin D ((finiteSpinEraseEquiv hv).symm (eta, s)) =
      Function.update (extendFiniteSpin (D.erase v) eta) v s := by
  classical
  funext x
  by_cases hxv : x = v
  · subst x
    simp [extendFiniteSpin, finiteSpinEraseEquiv, hv]
  · by_cases hx : x ∈ D
    · simp [extendFiniteSpin, finiteSpinEraseEquiv, hxv, hx]
    · simp [extendFiniteSpin, hxv, hx]

theorem sum_freeCylinderWeight_erase_of_max_length
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (hv : v ∈ D) (hp : p ∈ D) (hpv : treeAdj p v)
    (hplen : p.1.length < v.1.length)
    (hmax : ∀ x ∈ D, x.1.length ≤ v.1.length) :
    (∑ eta : D → IsingSpin, freeCylinderWeight theta D (extendFiniteSpin D eta)) =
      ∑ eta : D.erase v → IsingSpin,
        freeCylinderWeight theta (D.erase v) (extendFiniteSpin (D.erase v) eta) := by
  classical
  calc
    _ = ∑ z : (D.erase v → IsingSpin) × IsingSpin,
        freeCylinderWeight theta D
          (extendFiniteSpin D ((finiteSpinEraseEquiv hv).symm z)) :=
      ((finiteSpinEraseEquiv hv).symm.sum_comp
        (fun eta => freeCylinderWeight theta D (extendFiniteSpin D eta))).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro eta _
      simp only [extendFiniteSpin_eraseEquiv_symm]
      exact freeCylinderWeight_sum_update_leaf hlo hhi hv hp hpv hplen hmax _

theorem sum_freeCylinderWeight_singleton {d : ℕ} (v : TreeVertex d) (theta : ℝ) :
    (∑ eta : ({v} : Finset (TreeVertex d)) → IsingSpin,
      freeCylinderWeight theta {v} (extendFiniteSpin {v} eta)) = 1 := by
  classical
  have hE : inducedEdges ({v} : Finset (TreeVertex d)) = ∅ := by
    ext e
    simp only [inducedEdges, Finset.product_eq_sprod, Finset.mem_filter,
      Finset.mem_product, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hx, hy⟩, _, hlen⟩
    rw [hx, hy] at hlen
    exact lt_irrefl _ hlen
  have hc : Fintype.card IsingSpin = 2 := by decide
  simp [freeCylinderWeight, hE, hc]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem sum_freeCylinderWeight_eq_one
    {d : ℕ} {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) :
    (∑ eta : D → IsingSpin, freeCylinderWeight theta D (extendFiniteSpin D eta)) = 1 := by
  classical
  revert hD
  refine Finset.strongInductionOn D ?_
  intro D ih hD
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image D (fun x => x.1.length) hD.1
  by_cases hn : (D.erase v).Nonempty
  · obtain ⟨q, hq⟩ := hn
    obtain h | ⟨p, hvp, _⟩ := (hD.2 v hv q (Finset.mem_erase.mp hq).2).cases_head
    · exact False.elim ((Finset.mem_erase.mp hq).1 h.symm)
    · have hpv : treeAdj p v := hvp.2.2.elim Or.inr Or.inl
      have hplen : p.1.length < v.1.length := by
        rcases hvp.2.2 with ⟨c, hc⟩ | ⟨c, hc⟩
        · have hlen := congrArg List.length hc
          have hbound := hmax p hvp.2.1
          simp only [List.length_append, List.length_singleton] at hlen
          omega
        · have hlen := congrArg List.length hc
          simp only [List.length_append, List.length_singleton] at hlen
          omega
      rw [sum_freeCylinderWeight_erase_of_max_length hlo hhi hv hvp.2.1 hpv hplen hmax]
      exact ih (D.erase v) (Finset.erase_ssubset hv)
        (connectedFinset_erase_of_max_length hD hv ⟨q, hq⟩ hmax)
  · have he : D.erase v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hsingle : D = {v} := ((Finset.erase_eq_empty_iff D v).mp he).resolve_left hD.1.ne_empty
    subst D
    exact sum_freeCylinderWeight_singleton v theta

def finiteFreeIsingPMF
    {d : ℕ} {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) : PMF (D → IsingSpin) :=
  PMF.ofFintype (fun eta => freeCylinderWeight theta D (extendFiniteSpin D eta))
    (sum_freeCylinderWeight_eq_one hlo hhi D hD)

@[simp]
theorem finiteFreeIsingPMF_apply
    {d : ℕ} {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (eta : D → IsingSpin) :
    finiteFreeIsingPMF hlo hhi D hD eta =
      freeCylinderWeight theta D (extendFiniteSpin D eta) := rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_Fields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Fintype V]

def fieldEnergy (energy : S → ℝ) (spin : S → V → ℝ) (x : V → ℝ) (s : S) : ℝ :=
  energy s + ∑ v, x v * spin s v

def fieldMean (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (x : V → ℝ) : ℝ :=
  (∑ s, observable s * Real.exp (fieldEnergy energy spin x s)) /
    (∑ s, Real.exp (fieldEnergy energy spin x s))

lemma fieldPartition_pos [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (x : V → ℝ) : 0 < ∑ s, Real.exp (fieldEnergy energy spin x s) := by
  exact Finset.sum_pos (fun s _ => Real.exp_pos _) Finset.univ_nonempty

theorem continuous_fieldMean [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) : Continuous (fieldMean energy spin observable) := by
  unfold fieldMean
  apply Continuous.div
  · unfold fieldEnergy
    fun_prop
  · unfold fieldEnergy
    fun_prop
  · intro x
    exact ne_of_gt (fieldPartition_pos energy spin x)

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_GaussianPosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace Problem367

local instance gaussianPosteriorNonemptyIsingSpin_r34b34c_1 : Nonempty IsingSpin := ⟨.neg⟩
def finiteIsingEnergy {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d))
    (eta : D → IsingSpin) : ℝ :=
  beta * ∑ e ∈ inducedEdges D,
    spinSign (extendFiniteSpin D eta e.1) * spinSign (extendFiniteSpin D eta e.2)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_Symmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace Problem367.PlantedSymmetry

@[implicit_reducible] def observationSigma (ι : Type*) (t : ℝ) :
    MeasurableSpace ((ι → IsingSpin) × (ι → ℝ)) :=
  MeasurableSpace.comap (observation t) inferInstance

end Problem367.PlantedSymmetry

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ConnectedExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def connectedExhaustion {d : ℕ} (v : TreeVertex d) (n : ℕ) : Finset (TreeVertex d) := by
  classical
  exact ConnectedHull.hull (insert v (treeBallFinset d n))

theorem mem_connectedExhaustion {d : ℕ} (v : TreeVertex d) (n : ℕ) :
    v ∈ connectedExhaustion v n := by
  classical
  exact ConnectedHull.subset_hull _ (Finset.mem_insert_self _ _)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Regularity
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem367

def treeStep {d : ℕ} (v : TreeVertex d) (c : Fin d) : TreeVertex d :=
  if h : v.1.getLast? = some c then
    ⟨v.1.dropLast, v.2.dropLast⟩
  else
    ⟨v.1 ++ [c], by
      apply List.isChain_append.mpr
      refine ⟨v.2, by simp, ?_⟩
      intro a ha b hb
      simp only [List.head?_cons, Option.mem_some_iff] at hb
      subst b
      intro hac
      subst a
      exact h ha⟩

theorem treeStep_adj {d : ℕ} (v : TreeVertex d) (c : Fin d) :
    treeAdj v (treeStep v c) := by
  unfold treeStep
  split_ifs with h
  · right
    refine ⟨c, ?_⟩
    obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp h
    simp [hl]
  · exact Or.inl ⟨c, rfl⟩

theorem treeStep_injective {d : ℕ} (v : TreeVertex d) :
    Function.Injective (treeStep v) := by
  intro c c' heq
  by_cases hc : v.1.getLast? = some c
  · by_cases hc' : v.1.getLast? = some c'
    · exact Option.some.inj (hc.symm.trans hc')
    · have hh := congrArg (fun w : TreeVertex d => w.1.length) heq
      simp only [treeStep, dite_eq_left hc, dite_eq_right hc', List.length_dropLast, List.length_append, List.length_singleton] at hh
      omega
  · by_cases hc' : v.1.getLast? = some c'
    · have hh := congrArg (fun w : TreeVertex d => w.1.length) heq
      simp only [treeStep, dite_eq_right hc, dite_eq_left hc', List.length_dropLast, List.length_append, List.length_singleton] at hh
      omega
    · have hh := congrArg (fun w : TreeVertex d => w.1) heq
      simpa [treeStep, hc, hc'] using hh

theorem treeStep_eq_iff {d : ℕ} (v w : TreeVertex d) (c : Fin d) :
    treeStep v c = w ↔ w.1 = v.1 ++ [c] ∨ v.1 = w.1 ++ [c] := by
  constructor
  · intro h
    by_cases hc : v.1.getLast? = some c
    · right
      obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp hc
      have hw := congrArg Subtype.val h
      simp only [treeStep, dite_eq_left hc] at hw
      simpa [hl] using (congrArg (fun x : List (Fin d) => x ++ [c]) hw)
    · left
      have hw := congrArg Subtype.val h
      simpa only [treeStep, dite_eq_right hc] using hw.symm
  · rintro (hc | hc)
    · have hn : v.1.getLast? ≠ some c := by
        intro hlast
        have hchain : List.IsChain (fun a b : Fin d => a ≠ b) (v.1 ++ [c]) := by
          rw [← hc]
          exact w.2
        exact (List.isChain_append.mp hchain).2.2 c hlast c rfl rfl
      apply Subtype.ext
      simp [treeStep, hn, hc]
    · apply Subtype.ext
      simp [treeStep, hc]

theorem treeAdj_iff_exists_treeStep {d : ℕ} (v w : TreeVertex d) :
    treeAdj v w ↔ ∃ c : Fin d, treeStep v c = w := by
  constructor
  · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
    · exact ⟨c, (treeStep_eq_iff v w c).mpr (Or.inl hc)⟩
    · exact ⟨c, (treeStep_eq_iff v w c).mpr (Or.inr hc)⟩
  · rintro ⟨c, rfl⟩
    exact treeStep_adj v c

def treeNeighborFinset {d : ℕ} (v : TreeVertex d) : Finset (TreeVertex d) := by
  classical
  exact Finset.univ.image (treeStep v)

@[simp] theorem mem_treeNeighborFinset {d : ℕ} (v w : TreeVertex d) :
    w ∈ treeNeighborFinset v ↔ treeAdj v w := by
  classical
  simp [treeNeighborFinset, treeAdj_iff_exists_treeStep]

@[simp] theorem card_treeNeighborFinset {d : ℕ} (v : TreeVertex d) :
    (treeNeighborFinset v).card = d := by
  classical
  rw [treeNeighborFinset, Finset.card_image_of_injective _ (treeStep_injective v)]
  simp

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ProgressiveIsingPosterior
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.prefixFlip_twice
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

local instance progressiveIsingPosteriorNonemptyIsingSpin : Nonempty IsingSpin := ⟨.neg⟩

def finiteGibbsSpinMean {d : ℕ} (beta : ℝ) (v : TreeVertex d) (n : ℕ)
    (y : TreeVertex d → ℝ) : ℝ :=
  FinitePosterior.fieldMean (finiteIsingEnergy beta (connectedExhaustion v n))
    (fun (eta : connectedExhaustion v n → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta ⟨v, mem_connectedExhaustion v n⟩))
    ((connectedExhaustion v n).restrict y)

theorem continuous_finiteGibbsSpinMean {d : ℕ} (beta : ℝ) (v : TreeVertex d) (n : ℕ) :
    Continuous (finiteGibbsSpinMean beta v n) := by
  apply (FinitePosterior.continuous_fieldMean _ _ _).comp
  exact continuous_pi (fun w => continuous_apply w.1)

def infiniteGibbsSpinMean {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (y : TreeVertex d → ℝ) : ℝ :=
  max (-1) (min 1 (limUnder atTop (fun n => finiteGibbsSpinMean beta v n y)))

theorem measurable_infiniteGibbsSpinMean {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    Measurable (infiniteGibbsSpinMean beta v) := by
  have hm : StronglyMeasurable (fun y =>
      limUnder atTop (fun n => finiteGibbsSpinMean beta v n y)) :=
    StronglyMeasurable.limUnder
      (fun n => (continuous_finiteGibbsSpinMean beta v n).measurable.stronglyMeasurable)
  exact measurable_const.max (measurable_const.min hm.measurable)

theorem infiniteGibbsSpinMean_abs_le_one {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (y : TreeVertex d → ℝ) : |infiniteGibbsSpinMean beta v y| ≤ 1 := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem isStronglyProgressive_infiniteGibbsSpinMean
    {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (beta : ℝ) (v : TreeVertex d)
    (X : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i, IsStronglyProgressive F (X i)) :
    IsStronglyProgressive F
      (fun t omega => infiniteGibbsSpinMean beta v (fun i => X i t omega)) := by
  intro t
  let : MeasurableSpace Ω := F t
  exact ((measurable_infiniteGibbsSpinMean beta v).comp
    (Measurable.of_eval (fun i => (hX i t).measurable))).stronglyMeasurable

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ProgressiveIsingCovariance
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

def pairExhaustion {d : ℕ} (v w : TreeVertex d) (n : ℕ) : Finset (TreeVertex d) :=
  connectedExhaustion v (n + w.1.length)

lemma mem_pairExhaustion_left {d : ℕ} (v w : TreeVertex d) (n : ℕ) :
    v ∈ pairExhaustion v w n := mem_connectedExhaustion v _

lemma mem_pairExhaustion_right {d : ℕ} (v w : TreeVertex d) (n : ℕ) :
    w ∈ pairExhaustion v w n := by
  classical
  apply ConnectedHull.subset_hull
  apply Finset.mem_insert_of_mem
  exact (mem_treeBallFinset d (n + w.1.length) w).mpr (by omega)

local instance progressiveIsingCovarianceNonemptySpin_r34b34c_1 : Nonempty IsingSpin := ⟨.neg⟩
def finiteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d) (n : ℕ)
    (y : TreeVertex d → ℝ) : ℝ :=
  FinitePosterior.fieldMean (finiteIsingEnergy beta (pairExhaustion v w n))
    (fun (eta : pairExhaustion v w n → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta ⟨v, mem_pairExhaustion_left v w n⟩) *
      spinSign (eta ⟨w, mem_pairExhaustion_right v w n⟩))
    ((pairExhaustion v w n).restrict y)

def infiniteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d)
    (y : TreeVertex d → ℝ) : ℝ :=
  max (-1) (min 1 (limUnder atTop (fun n => finiteGibbsPairMean beta v w n y)))

def infiniteGibbsCovariance {d : ℕ} (beta : ℝ) (v w : TreeVertex d)
    (y : TreeVertex d → ℝ) : ℝ :=
  infiniteGibbsPairMean beta v w y -
    infiniteGibbsSpinMean beta v y * infiniteGibbsSpinMean beta w y

def infiniteGibbsResponse {d : ℕ} (beta : ℝ) (v w : TreeVertex d)
    (y : TreeVertex d → ℝ) : ℝ :=
  infiniteGibbsCovariance beta v w y / (1 - infiniteGibbsSpinMean beta v y ^ 2)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_BoundedInnovationDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

theorem intervalIntegrable_of_measurable_norm_le_const
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hbound : ∀ t, ‖f t‖ ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  apply (intervalIntegrable_const (c := C)).mono_fun' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall hbound

theorem lipschitzWith_intervalPrimitive_of_bound
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ≥0}
    (hbound : ∀ t, ‖f t‖ ≤ (C : ℝ)) (a : ℝ) :
    LipschitzWith C (fun t : ℝ => ∫ r in a..t, f r) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq, ← Real.norm_eq_abs, intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_of_measurable_norm_le_const hf hbound a s)
    (intervalIntegrable_of_measurable_norm_le_const hf hbound a t)]
  simpa only [Real.dist_eq] using
    intervalIntegral.norm_integral_le_of_norm_le_const (fun r _ => hbound r)

theorem lipschitzWith_nnrealTimePrimitive
    {Ω : Type*} {m : ℝ≥0 → Ω → ℝ}
    (hm : ∀ ω, Measurable (fun t => m t ω)) {C : ℝ≥0}
    (hbound : ∀ t ω, ‖m t ω‖ ≤ (C : ℝ)) (ω : Ω) :
    LipschitzWith C (fun t => nnrealTimePrimitive m t ω) := by
  have h := lipschitzWith_intervalPrimitive_of_bound
    ((hm ω).comp measurable_real_toNNReal) (fun r => hbound _ ω) 0
  apply LipschitzWith.of_dist_le_mul
  intro s t
  exact h.dist_le_mul (s : ℝ) (t : ℝ)

theorem measurable_path_of_isStronglyProgressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) (ω : Ω) :
    Measurable (fun t => m t ω) := by
  have hstop (n : ℕ) : StronglyMeasurable
      (fun t : ℝ≥0 => m (min t (n : ℝ≥0)) ω) := by
    let : MeasurableSpace Ω := F n
    have htime : Measurable (fun t : ℝ≥0 =>
        (⟨min t (n : ℝ≥0), by simp⟩ : Set.Iic (n : ℝ≥0))) :=
      (measurable_id.min measurable_const).subtype_mk
    exact (hm n).comp_measurable (htime.prodMk measurable_const)
  apply (stronglyMeasurable_of_tendsto atTop hstop ?_).measurable
  apply tendsto_pi_nhds.mpr
  intro t
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := exists_nat_ge t
  filter_upwards [eventually_ge_atTop N] with n hn
  have htn : t ≤ (n : ℝ≥0) := hN.trans (by exact_mod_cast hn)
  simp [min_eq_left htn]

theorem lipschitzWith_nnrealTimePrimitive_of_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) {C : ℝ≥0}
    (hbound : ∀ t ω, ‖m t ω‖ ≤ (C : ℝ)) (ω : Ω) :
    LipschitzWith C (fun t => nnrealTimePrimitive m t ω) :=
  lipschitzWith_nnrealTimePrimitive (measurable_path_of_isStronglyProgressive hm)
    hbound ω

end Problem367

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

def koopmanL2 (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ τ hτ).toContinuousLinearMap

@[simp] theorem koopmanL2_norm (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (f : Lp ℝ 2 μ) : ‖koopmanL2 τ hτ f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f hτ

theorem koopmanL2_involutive (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) : Function.Involutive (koopmanL2 τ hτ) := by
  intro f
  change Lp.compMeasurePreserving τ hτ (Lp.compMeasurePreserving τ hτ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f hτ hτ]
  have hid : τ ∘ τ = id := funext hinv
  simp [hid]

theorem koopmanL2_selfAdjoint (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) : IsSelfAdjoint (koopmanL2 τ hτ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  have hi := (Lp.compMeasurePreservingₗᵢ ℝ τ hτ).inner_map_map f (koopmanL2 τ hτ g)
  change inner ℝ (koopmanL2 τ hτ f)
    (koopmanL2 τ hτ (koopmanL2 τ hτ g)) = inner ℝ f (koopmanL2 τ hτ g) at hi
  simpa only [ContinuousLinearMap.coe_coe, koopmanL2_involutive τ hτ hinv g] using hi

def koopmanAverage {ι : Type*} [Fintype ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, koopmanL2 (τ i) (hτ i)

section Centered

variable [IsFiniteMeasure μ]

@[simp] theorem koopmanL2_const (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (c : ℝ) : koopmanL2 τ hτ (Lp.const 2 μ c) = Lp.const 2 μ c := by
  apply Subtype.ext
  change (AEEqFun.const Ω c).compMeasurePreserving τ hτ = AEEqFun.const Ω c
  simp [AEEqFun.const, AEEqFun.compMeasurePreserving_mk, Function.comp_def]

theorem inner_const_one_eq_integral (f : Lp ℝ 2 μ) :
    inner ℝ (Lp.const 2 μ (1 : ℝ)) f = ∫ ω, f ω ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with ω hω
  change (AEEqFun.const Ω (1 : ℝ) : Ω →ₘ[μ] ℝ) ω = 1 at hω
  simp [hω]

def centeredL2 (μ : Measure Ω) [IsFiniteMeasure μ] : Submodule ℝ (Lp ℝ 2 μ) :=
  (innerSL ℝ (Lp.const 2 μ (1 : ℝ))).ker

@[simp] theorem mem_centeredL2_iff (f : Lp ℝ 2 μ) :
    f ∈ centeredL2 μ ↔ (∫ ω, f ω ∂μ) = 0 := by
  change inner ℝ (Lp.const 2 μ (1 : ℝ)) f = 0 ↔ _
  rw [inner_const_one_eq_integral]

theorem koopmanL2_integral (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) (f : Lp ℝ 2 μ) :
    (∫ ω, koopmanL2 τ hτ f ω ∂μ) = ∫ ω, f ω ∂μ := by
  rw [← inner_const_one_eq_integral, ← inner_const_one_eq_integral]
  have hsym := (koopmanL2_selfAdjoint τ hτ hinv).isSymmetric
  have hs := hsym (Lp.const 2 μ (1 : ℝ)) f
  simp only [ContinuousLinearMap.coe_coe, koopmanL2_const] at hs
  exact hs.symm

theorem koopmanL2_preserves_centered (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) :
    ∀ f ∈ centeredL2 μ, koopmanL2 τ hτ f ∈ centeredL2 μ := by
  intro f hf
  rw [mem_centeredL2_iff] at hf ⊢
  rw [koopmanL2_integral τ hτ hinv, hf]

theorem koopmanAverage_preserves_centered {ι : Type*} [Fintype ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hinv : ∀ i, Function.Involutive (τ i)) :
    ∀ f ∈ centeredL2 μ, koopmanAverage τ hτ f ∈ centeredL2 μ := by
  intro f hf
  change (Fintype.card ι : ℝ)⁻¹ • (∑ i, koopmanL2 (τ i) (hτ i)) f ∈ centeredL2 μ
  apply Submodule.smul_mem
  simp only [sum_apply]
  exact Submodule.sum_mem _ fun i _ => koopmanL2_preserves_centered (τ i) (hτ i) (hinv i) f hf

def centeredKoopmanAverage {ι : Type*} [Fintype ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hinv : ∀ i, Function.Involutive (τ i)) :
    centeredL2 μ →L[ℝ] centeredL2 μ :=
  (koopmanAverage τ hτ).restrict (koopmanAverage_preserves_centered τ hτ hinv)

@[simp] theorem centeredKoopmanAverage_apply_coe {ι : Type*} [Fintype ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hinv : ∀ i, Function.Involutive (τ i)) (f : centeredL2 μ) :
    (centeredKoopmanAverage τ hτ hinv f : Lp ℝ 2 μ) = koopmanAverage τ hτ f := rfl

end Centered

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Koopman
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem367.TreeKoopman

instance labelProbability (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def reflection {d : ℕ} (c : Fin d) :
    (TreeVertex d → ℝ) → (TreeVertex d → ℝ) :=
  relabel (prefixTreeAut c)

theorem reflection_measurePreserving {d : ℕ} (c : Fin d) :
    MeasurePreserving (reflection c) (labelMeasure d) (labelMeasure d) :=
  measurePreserving_relabel (prefixTreeAut c)

theorem reflection_involutive {d : ℕ} (c : Fin d) :
    Function.Involutive (reflection c) := by
  intro U
  funext v
  change U (prefixFlip c (prefixFlip c v)) = U v
  rw [prefixFlip_twice]

def average (d : ℕ) :
    Lp ℝ 2 (labelMeasure d) →L[ℝ] Lp ℝ 2 (labelMeasure d) :=
  koopmanAverage (fun c : Fin d => reflection c) reflection_measurePreserving

def centeredAverage (d : ℕ) :
    centeredL2 (labelMeasure d) →L[ℝ] centeredL2 (labelMeasure d) :=
  centeredKoopmanAverage (fun c : Fin d => reflection c)
    reflection_measurePreserving reflection_involutive

@[simp] theorem centeredAverage_apply_coe {d : ℕ}
    (f : centeredL2 (labelMeasure d)) :
    (centeredAverage d f : Lp ℝ 2 (labelMeasure d)) = average d f := rfl

@[simp] theorem centeredAverage_pow_apply_coe {d : ℕ}
    (n : ℕ) (f : centeredL2 (labelMeasure d)) :
    ((centeredAverage d ^ n) f : Lp ℝ 2 (labelMeasure d)) =
      (average d ^ n) (f : Lp ℝ 2 (labelMeasure d)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ']
    change (average d) (((centeredAverage d ^ n) f : centeredL2 (labelMeasure d)) :
      Lp ℝ 2 (labelMeasure d)) = average d ((average d ^ n) (f : Lp ℝ 2 (labelMeasure d)))
    rw [ih]

end Problem367.TreeKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_WordAction
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeKoopman

def wordAut {d : ℕ} : List (Fin d) → TreeAut d
  | [] => TreeAut.refl d
  | c :: w => (wordAut w).trans (prefixTreeAut c)

def wordRelabel {d : ℕ} (w : List (Fin d)) :
    (TreeVertex d → ℝ) → (TreeVertex d → ℝ) :=
  relabel (wordAut w).symm

@[simp] theorem wordRelabel_nil {d : ℕ} : wordRelabel ([] : List (Fin d)) = id := rfl

@[simp] theorem wordRelabel_cons {d : ℕ} (c : Fin d) (w : List (Fin d)) :
    wordRelabel (c :: w) = wordRelabel w ∘ reflection c := rfl

def generatorOperator {d : ℕ} (c : Fin d) :
    Lp ℝ 2 (labelMeasure d) →L[ℝ] Lp ℝ 2 (labelMeasure d) :=
  koopmanL2 (reflection c) (reflection_measurePreserving c)

@[simp] theorem generatorOperator_sq {d : ℕ} (c : Fin d) :
    generatorOperator c * generatorOperator c = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  exact koopmanL2_involutive _ _ (reflection_involutive c) f

end Problem367.TreeKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_CenteredWordAction
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeKoopman

def centeredGenerator {d : ℕ} (c : Fin d) :
    centeredL2 (labelMeasure d) →L[ℝ] centeredL2 (labelMeasure d) :=
  (generatorOperator c).restrict
    (koopmanL2_preserves_centered (reflection c) (reflection_measurePreserving c)
      (reflection_involutive c))

@[simp] theorem centeredGenerator_apply_coe {d : ℕ} (c : Fin d)
    (f : centeredL2 (labelMeasure d)) :
    (centeredGenerator c f : Lp ℝ 2 (labelMeasure d)) =
      generatorOperator c (f : Lp ℝ 2 (labelMeasure d)) := rfl

@[simp] theorem centeredGenerator_sq {d : ℕ} (c : Fin d) :
    centeredGenerator c * centeredGenerator c = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  change generatorOperator c (generatorOperator c (f : Lp ℝ 2 (labelMeasure d))) = f
  have h := congrArg (fun A : Lp ℝ 2 (labelMeasure d) →L[ℝ] Lp ℝ 2 (labelMeasure d) =>
    A (f : Lp ℝ 2 (labelMeasure d))) (generatorOperator_sq c)
  exact h

end Problem367.TreeKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_CharacteristicRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology NNReal

namespace Problem367.ExponentialTaylor

theorem sum_mul_sqrt_le_total_mul_sqrt_mesh
    (dt : ℕ → ℝ) (n : ℕ) {mesh : ℝ}
    (hdt : ∀ k < n, 0 ≤ dt k) (hmesh : ∀ k < n, dt k ≤ mesh) :
    (∑ k ∈ Finset.range n, dt k * Real.sqrt (dt k)) ≤
      (∑ k ∈ Finset.range n, dt k) * Real.sqrt mesh := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hmesh k (Finset.mem_range.mp hk)))
    (hdt k (Finset.mem_range.mp hk))

theorem sum_cube_le_total_mul_mesh_sq
    (dt : ℕ → ℝ) (n : ℕ) {mesh : ℝ}
    (hdt : ∀ k < n, 0 ≤ dt k) (hmesh : ∀ k < n, dt k ≤ mesh) :
    (∑ k ∈ Finset.range n, (dt k) ^ 3) ≤
      (∑ k ∈ Finset.range n, dt k) * mesh ^ 2 := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hsq : (dt k) ^ 2 ≤ mesh ^ 2 :=
    pow_le_pow_left₀ (hdt k hk') (hmesh k hk') 2
  convert mul_le_mul_of_nonneg_left hsq (hdt k hk') using 1 <;> first | rfl | ring

end Problem367.ExponentialTaylor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ColorAutomorphisms
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

def colorPermMap {d : ℕ} (p : Equiv.Perm (Fin d)) (u : TreeVertex d) : TreeVertex d :=
  ⟨u.1.map p, by
    change (u.1.map p).IsChain (· ≠ ·)
    rw [List.isChain_map]
    exact u.2.imp (fun _ _ hab hab' => hab (p.injective hab'))⟩

@[simp] theorem colorPermMap_val {d : ℕ} (p : Equiv.Perm (Fin d))
    (u : TreeVertex d) : (colorPermMap p u).1 = u.1.map p := rfl

@[simp] theorem colorPermMap_symm_apply {d : ℕ} (p : Equiv.Perm (Fin d))
    (u : TreeVertex d) : colorPermMap p.symm (colorPermMap p u) = u := by
  apply Subtype.ext
  simp [colorPermMap, List.map_map, Function.comp_def]

theorem colorPermMap_adj {d : ℕ} (p : Equiv.Perm (Fin d)) {u v : TreeVertex d}
    (h : treeAdj u v) : treeAdj (colorPermMap p u) (colorPermMap p v) := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact Or.inl ⟨p c, by simp [colorPermMap, hc]⟩
  · exact Or.inr ⟨p c, by simp [colorPermMap, hc]⟩

def colorPermAut {d : ℕ} (p : Equiv.Perm (Fin d)) : TreeAut d where
  toEquiv :=
    { toFun := colorPermMap p
      invFun := colorPermMap p.symm
      left_inv := colorPermMap_symm_apply p
      right_inv := by
        intro u
        simpa only [Equiv.symm_symm] using colorPermMap_symm_apply p.symm u }
  map_adj := by
    intro u v
    change treeAdj (colorPermMap p u) (colorPermMap p v) ↔ treeAdj u v
    constructor
    · intro h
      simpa using colorPermMap_adj p.symm h
    · exact colorPermMap_adj p

@[simp] theorem colorPermAut_val {d : ℕ} (p : Equiv.Perm (Fin d))
    (u : TreeVertex d) : ((colorPermAut p).toEquiv u).1 = u.1.map p := rfl

@[simp] theorem colorPermAut_length {d : ℕ} (p : Equiv.Perm (Fin d))
    (u : TreeVertex d) : ((colorPermAut p).toEquiv u).1.length = u.1.length := by
  simp

@[simp] theorem colorPermAut_nil {d : ℕ} (p : Equiv.Perm (Fin d))
    (h : List.IsChain (fun a b : Fin d => a ≠ b) []) :
    (colorPermAut p).toEquiv ⟨[], h⟩ = ⟨[], h⟩ := by
  apply Subtype.ext
  rfl

def branchColorList {d : ℕ} (p : Fin d → Equiv.Perm (Fin d)) :
    List (Fin d) → List (Fin d)
  | [] => []
  | c :: w => c :: w.map (p c)

lemma branchColorList_chain {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) (w : List (Fin d)) (hw : w.IsChain (· ≠ ·)) :
    (branchColorList p w).IsChain (· ≠ ·) := by
  cases w with
  | nil => simp [branchColorList]
  | cons c w =>
    have h := (colorPermMap (p c) ⟨c :: w, hw⟩).2
    change ((c :: w).map (p c)).IsChain (· ≠ ·) at h
    simpa [colorPermMap, branchColorList, hp c] using h

lemma branchColorList_inverse {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (w : List (Fin d)) :
    branchColorList (fun c => (p c).symm) (branchColorList p w) = w := by
  cases w <;> simp [branchColorList, List.map_map, Function.comp_def]

lemma branchColorList_append {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (w : List (Fin d)) (a : Fin d) :
    ∃ b, branchColorList p (w ++ [a]) = branchColorList p w ++ [b] := by
  cases w with
  | nil => exact ⟨a, rfl⟩
  | cons c w => exact ⟨p c a, by simp [branchColorList]⟩

def branchColorMap {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) (u : TreeVertex d) : TreeVertex d :=
  ⟨branchColorList p u.1, branchColorList_chain p hp u.1 u.2⟩

lemma branchColorMap_adj {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) {u v : TreeVertex d} (h : treeAdj u v) :
    treeAdj (branchColorMap p hp u) (branchColorMap p hp v) := by
  change (∃ a, branchColorList p v.1 = branchColorList p u.1 ++ [a]) ∨
    (∃ a, branchColorList p u.1 = branchColorList p v.1 ++ [a])
  rcases h with ⟨a, ha⟩ | ⟨a, ha⟩
  · rw [ha]
    exact Or.inl (branchColorList_append p u.1 a)
  · rw [ha]
    exact Or.inr (branchColorList_append p v.1 a)

lemma branchColor_inverse_fixes {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) (c : Fin d) : (p c).symm c = c := by
  apply (p c).injective
  simp [hp c]

@[simp] lemma branchColorMap_symm_apply {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) (u : TreeVertex d) :
    branchColorMap (fun c => (p c).symm) (branchColor_inverse_fixes p hp)
      (branchColorMap p hp u) = u := by
  apply Subtype.ext
  exact branchColorList_inverse p u.1

def branchColorAut {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) : TreeAut d where
  toEquiv :=
    { toFun := branchColorMap p hp
      invFun := branchColorMap (fun c => (p c).symm) (branchColor_inverse_fixes p hp)
      left_inv := branchColorMap_symm_apply p hp
      right_inv := by
        intro u
        apply Subtype.ext
        simpa only [branchColorMap, Equiv.symm_symm] using
          branchColorList_inverse (fun c => (p c).symm) u.1 }
  map_adj := by
    intro u v
    change treeAdj (branchColorMap p hp u) (branchColorMap p hp v) ↔ treeAdj u v
    constructor
    · intro h
      simpa using branchColorMap_adj (fun c => (p c).symm)
        (branchColor_inverse_fixes p hp) h
    · exact branchColorMap_adj p hp

@[simp] theorem branchColorAut_val {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) (u : TreeVertex d) :
    ((branchColorAut p hp).toEquiv u).1 = branchColorList p u.1 := rfl

@[simp] theorem branchColorAut_length {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) (u : TreeVertex d) :
    ((branchColorAut p hp).toEquiv u).1.length = u.1.length := by
  rcases u with ⟨w, hw⟩
  cases w <;> simp [branchColorList]

@[simp] theorem branchColorAut_singleton {d : ℕ} (p : Fin d → Equiv.Perm (Fin d))
    (hp : ∀ c, p c c = c) (c : Fin d)
    (h : List.IsChain (fun a b : Fin d => a ≠ b) [c]) :
    (branchColorAut p hp).toEquiv ⟨[c], h⟩ = ⟨[c], h⟩ := by
  apply Subtype.ext
  rfl

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Parents
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

def parentVertex {d : ℕ} (v : TreeVertex d) : TreeVertex d :=
  ⟨v.1.dropLast, v.2.dropLast⟩

@[simp] theorem parentVertex_val {d : ℕ} (v : TreeVertex d) :
    (parentVertex v).1 = v.1.dropLast := rfl

@[simp] theorem parentVertex_length {d : ℕ} (v : TreeVertex d) :
    (parentVertex v).1.length = v.1.length - 1 := by
  simp [parentVertex]

theorem treeAdj_preserves_prefix {d : ℕ} {r u v : TreeVertex d}
    (hu : r.1 <+: u.1) (h : treeAdj u v) (hne : u ≠ r) : r.1 <+: v.1 := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · rw [hc]
    exact hu.trans (List.prefix_append _ _)
  · have hlen : r.1.length < u.1.length := by
      have hle := hu.length_le
      have hneq : r.1.length ≠ u.1.length := by
        intro heq
        exact hne (Subtype.ext (hu.eq_of_length heq).symm)
      omega
    have hv : v.1 <+: u.1 := by
      rw [hc]
      exact List.prefix_append _ _
    apply List.prefix_of_prefix_length_le hu hv
    have hlen' : u.1.length = v.1.length + 1 := by simp [hc]
    omega

theorem treeAdj_preserves_prefix_of_parent_not_mem {d : ℕ}
    {D : Finset (TreeVertex d)} {r u v : TreeVertex d}
    (hr : parentVertex r ∉ D) (hv : v ∈ D)
    (hu : r.1 <+: u.1) (h : treeAdj u v) : r.1 <+: v.1 := by
  by_cases hne : u = r
  · subst u
    rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
    · rw [hc]
      exact List.prefix_append _ _
    · have heq : parentVertex r = v := by
        apply Subtype.ext
        simp [parentVertex, hc]
      exact False.elim (hr (heq.symm ▸ hv))
  · exact treeAdj_preserves_prefix hu h hne

theorem prefix_of_reachable_of_parent_not_mem {d : ℕ}
    {D : Finset (TreeVertex d)} {r v : TreeVertex d}
    (hr : parentVertex r ∉ D)
    (h : Relation.ReflTransGen
      (fun x y : TreeVertex d => x ∈ D ∧ y ∈ D ∧ treeAdj x y) r v) :
    r.1 <+: v.1 := by
  induction h with
  | refl => exact List.prefix_refl _
  | tail h hab ih =>
      exact treeAdj_preserves_prefix_of_parent_not_mem hr hab.2.1 ih hab.2.2

theorem ConnectedFinset.parent_mem_of_ne_min {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r v : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    (hv : v ∈ D) (hne : v ≠ r) : parentVertex v ∈ D := by
  by_contra hp
  have hpre := prefix_of_reachable_of_parent_not_mem hp (hD.2 v hv r hr)
  exact hne (Subtype.ext (hpre.eq_of_length_le (hmin v hv)))

theorem ConnectedFinset.ne_nil_of_ne_min {d : ℕ}
    {D : Finset (TreeVertex d)} {r v : TreeVertex d}
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    (hv : v ∈ D) (hne : v ≠ r) : v.1 ≠ [] := by
  intro heq
  have hrlen : r.1.length = 0 := by
    have := hmin v hv
    rw [heq, List.length_nil] at this
    omega
  have hre : r.1 = [] := List.length_eq_zero_iff.mp hrlen
  exact hne (Subtype.ext (heq.trans hre.symm))

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteComponentGeometry
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def rootComponentFinset {d : ℕ} (D : Finset (TreeVertex d)) (c : Fin d) :
    Finset (TreeVertex d) := by
  classical
  exact D.filter (fun v => [c] <+: v.1)

def rootComplementFinset {d : ℕ} (D : Finset (TreeVertex d)) (c : Fin d) :
    Finset (TreeVertex d) := by
  classical
  exact D.filter (fun v => ¬ [c] <+: v.1)

@[simp] theorem mem_rootComponentFinset {d : ℕ} {D : Finset (TreeVertex d)}
    {c : Fin d} {v : TreeVertex d} : v ∈ rootComponentFinset D c ↔
      v ∈ D ∧ [c] <+: v.1 := by
  classical
  simp [rootComponentFinset]

@[simp] theorem mem_rootComplementFinset {d : ℕ} {D : Finset (TreeVertex d)}
    {c : Fin d} {v : TreeVertex d} : v ∈ rootComplementFinset D c ↔
      v ∈ D ∧ ¬ [c] <+: v.1 := by
  classical
  simp [rootComplementFinset]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ThresholdArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma tanh_nonneg_of_beta_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    0 ≤ Real.tanh beta := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta) (Real.cosh_pos beta).le

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteIsingSplit
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FiniteIsingSplit

variable {V : Type*} [DecidableEq V]

def splitEquiv (A B : Finset V) (hAB : Disjoint A B) :
    (↥(A ∪ B) → IsingSpin) ≃ (A → IsingSpin) × (B → IsingSpin) where
  toFun eta := (fun v => eta ⟨v, Finset.mem_union_left B v.property⟩,
    fun v => eta ⟨v, Finset.mem_union_right A v.property⟩)
  invFun eta v := if h : v.1 ∈ A then eta.1 ⟨v.1, h⟩ else
    eta.2 ⟨v.1, (Finset.mem_union.mp v.property).resolve_left h⟩
  left_inv eta := by
    funext v
    dsimp only
    split_ifs <;> rfl
  right_inv eta := by
    apply Prod.ext
    · funext v
      simp only [dite_eq_left v.property]
    · funext v
      have hv : v.1 ∉ A := fun h => Finset.disjoint_left.mp hAB h v.property
      simp only [dite_eq_right hv]

@[simp] lemma splitEquiv_fst (A B : Finset V) (hAB : Disjoint A B)
    (eta : ↥(A ∪ B) → IsingSpin) (v : A) :
    (splitEquiv A B hAB eta).1 v =
      eta ⟨v, Finset.mem_union_left B v.property⟩ := rfl

@[simp] lemma splitEquiv_snd (A B : Finset V) (hAB : Disjoint A B)
    (eta : ↥(A ∪ B) → IsingSpin) (v : B) :
    (splitEquiv A B hAB eta).2 v =
      eta ⟨v, Finset.mem_union_right A v.property⟩ := rfl

end Problem367.FiniteIsingSplit

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

@[reducible] def selectedObservationField {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) :
    MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) :=
  MeasurableSpace.comap (fun p i => F (p.1 (v i)) (p.2 (v i))) inferInstance

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ComponentGibbsLimit
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

def rootComponentIndices {d : ℕ} (D : Finset (TreeVertex d)) (c : Fin d) :
    Finset (ComponentIndex c) := by
  classical
  exact D.preimage componentIndexVertex (componentIndexVertex_injective c).injOn

@[simp] theorem mem_rootComponentIndices {d : ℕ} {D : Finset (TreeVertex d)}
    {c : Fin d} {u : ComponentIndex c} :
    u ∈ rootComponentIndices D c ↔ componentIndexVertex u ∈ D := by
  classical
  exact Finset.mem_preimage

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InhomogeneousSpinChain
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.InhomogeneousChain

variable {A : Type*}

def weight (K : ℕ → A → A → ℝ) : (n : ℕ) → A → (Fin n → A) → ℝ
  | 0, _, _ => 1
  | n + 1, a, x => K 0 a (x 0) *
      weight (fun i => K (i + 1)) n (x 0) (Fin.tail x)

@[simp] theorem weight_zero (K : ℕ → A → A → ℝ) (a : A) (x : Fin 0 → A) :
    weight K 0 a x = 1 := rfl

@[simp] theorem weight_cons (K : ℕ → A → A → ℝ)
    (n : ℕ) (a b : A) (x : Fin n → A) :
    weight K (n + 1) a (Fin.cons b x) =
      K 0 a b * weight (fun i => K (i + 1)) n b x := by
  simp [weight]

end Problem367.InhomogeneousChain

namespace Problem367.PosteriorChain

def transition (beta z : ℝ) (a b : IsingSpin) : ℝ :=
  (1 + spinSign b * Real.tanh (z + beta * spinSign a)) / 2

@[simp] theorem transition_sum (beta z : ℝ) (a : IsingSpin) :
    ∑ b, transition beta z a b = 1 := by
  rw [sum_isingSpin]
  simp only [transition, spinSign_neg, spinSign_pos]
  ring

@[simp] theorem transition_spinMean (beta z : ℝ) (a : IsingSpin) :
    ∑ b, transition beta z a b * spinSign b =
      Real.tanh (z + beta * spinSign a) := by
  rw [sum_isingSpin]
  simp only [transition, spinSign_neg, spinSign_pos]
  ring

end Problem367.PosteriorChain

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InnovationCharacteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem367.InnovationCharacteristic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem integrable_increment_sq_of_bounded_drift
    {B W : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hW : ∀ t, AEMeasurable (W t) P) {s t : ℝ≥0} (hst : s ≤ t)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ᵐ ω ∂P,
      |(W t ω - W s ω) - (B t ω - B s ω)| ≤ L * ((t : ℝ) - (s : ℝ))) :
    Integrable (fun ω => (W t ω - W s ω) ^ 2) P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hK : 0 ≤ L * ((t : ℝ) - (s : ℝ)) := mul_nonneg hL (sub_nonneg.mpr hst)
  have h := integrable_abs_pow_of_bounded_perturbation 2 hK ((hW t).sub (hW s))
    (integrable_abs_pow_of_gaussianLaw (preBrownian_hasLaw_increment hB hst) 2) hbound
  simpa only [sq_abs, Pi.sub_apply] using h

def driftMomentConstant (L : ℝ) : ℝ :=
  4 * standardGaussianThirdMoment + 4 * L ^ 3 + 2 * L + L ^ 2

theorem driftMomentConstant_nonneg {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ driftMomentConstant L := by
  have := standardGaussianThirdMoment_nonneg
  unfold driftMomentConstant
  positivity

theorem integral_increment_cube_le_common_constant
    {B W : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hW : ∀ t, AEMeasurable (W t) P) {s t : ℝ≥0} (hst : s ≤ t)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ᵐ ω ∂P,
      |(W t ω - W s ω) - (B t ω - B s ω)| ≤ L * ((t : ℝ) - (s : ℝ))) :
    (∫ ω, |W t ω - W s ω| ^ 3 ∂P) ≤ driftMomentConstant L *
      (((t : ℝ) - (s : ℝ)) * Real.sqrt ((t : ℝ) - (s : ℝ)) +
        ((t : ℝ) - (s : ℝ)) ^ 3) := by
  have hp := standardGaussianThirdMoment_nonneg
  have h1 : 4 * standardGaussianThirdMoment ≤ driftMomentConstant L := by
    unfold driftMomentConstant
    nlinarith [pow_nonneg hL 3, sq_nonneg L]
  have h2 : 4 * L ^ 3 ≤ driftMomentConstant L := by
    unfold driftMomentConstant
    nlinarith [pow_nonneg hL 3, sq_nonneg L]
  have htime : 0 ≤ (t : ℝ) - (s : ℝ) := sub_nonneg.mpr hst
  calc
    _ ≤ 4 * (standardGaussianThirdMoment * ((t : ℝ) - (s : ℝ)) *
        Real.sqrt ((t : ℝ) - (s : ℝ)) + (L * ((t : ℝ) - (s : ℝ))) ^ 3) :=
      (preBrownian_bounded_drift_increment_moments hB hW hst hL hbound).2.2.2
    _ = (4 * standardGaussianThirdMoment) *
        (((t : ℝ) - (s : ℝ)) * Real.sqrt ((t : ℝ) - (s : ℝ))) +
        (4 * L ^ 3) * ((t : ℝ) - (s : ℝ)) ^ 3 := by ring
    _ ≤ driftMomentConstant L * (((t : ℝ) - (s : ℝ)) * Real.sqrt ((t : ℝ) - (s : ℝ))) +
        driftMomentConstant L * ((t : ℝ) - (s : ℝ)) ^ 3 := by
      exact add_le_add (mul_le_mul_of_nonneg_right h1 (by positivity))
        (mul_le_mul_of_nonneg_right h2 (by positivity))
    _ = _ := by ring

end Problem367.InnovationCharacteristic

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LocalColorAutomorphisms
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

def prefixColorList {d : ℕ} (stem : List (Fin d)) (p : Equiv.Perm (Fin d))
    (w : List (Fin d)) : List (Fin d) :=
  match stem, w with
  | [], w => w.map p
  | _ :: _, [] => []
  | a :: r, b :: w => if a = b then b :: prefixColorList r p w else b :: w

@[simp] lemma prefixColorList_nil {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) : prefixColorList stem p [] = [] := by
  cases stem <;> rfl

@[simp] lemma prefixColorList_head {d : ℕ} (a : Fin d) (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (w : List (Fin d)) :
    (prefixColorList (a :: stem) p w).head? = w.head? := by
  cases w with
  | nil => rfl
  | cons b w => by_cases h : a = b <;> simp [prefixColorList, h]

lemma prefixColorList_inverse {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (w : List (Fin d)) :
    prefixColorList stem p.symm (prefixColorList stem p w) = w := by
  induction stem generalizing w with
  | nil => simp [prefixColorList, List.map_map, Function.comp_def]
  | cons a r ih =>
    cases w with
    | nil => simp
    | cons b w => by_cases h : a = b <;> simp [prefixColorList, h, ih]

lemma prefixColorList_append {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (w : List (Fin d)) (c : Fin d) :
    ∃ e, prefixColorList stem p (w ++ [c]) = prefixColorList stem p w ++ [e] := by
  induction stem generalizing w with
  | nil => exact ⟨p c, by simp [prefixColorList]⟩
  | cons a r ih =>
    cases w with
    | nil =>
      refine ⟨c, ?_⟩
      by_cases h : a = c <;> simp [prefixColorList, h]
    | cons b w =>
      by_cases h : a = b
      · obtain ⟨e, he⟩ := ih w
        exact ⟨e, by simpa [prefixColorList, h] using congrArg (List.cons b) he⟩
      · exact ⟨c, by simp [prefixColorList, h]⟩

lemma prefixColorList_chain {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c)
    (w : List (Fin d)) (hw : w.IsChain (· ≠ ·)) :
    (prefixColorList stem p w).IsChain (· ≠ ·) := by
  induction stem generalizing w with
  | nil =>
    rw [prefixColorList, List.isChain_map]
    exact hw.imp (fun _ _ hab heq => hab (p.injective heq))
  | cons a r ih =>
    cases w with
    | nil => simp
    | cons b w =>
      by_cases hab : a = b
      · subst a
        cases r with
        | nil =>
          have hpb : p b = b := hp b (by simp)
          have hmap : ((b :: w).map p).IsChain (· ≠ ·) := by
            rw [List.isChain_map]
            exact hw.imp (fun _ _ hne heq => hne (p.injective heq))
          simpa [prefixColorList, hpb] using hmap
        | cons c r =>
          have hp' : ∀ x ∈ (c :: r).getLast?, p x = x := by
            simpa only [List.getLast?_cons_cons] using hp
          have ht := ih hp' w hw.tail
          simp only [prefixColorList]
          apply List.isChain_cons.mpr
          refine ⟨?_, ht⟩
          intro y hy
          rw [prefixColorList_head] at hy
          exact hw.rel_head? hy
      · simpa [prefixColorList, hab] using hw

@[simp] lemma prefixColorList_length {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (w : List (Fin d)) :
    (prefixColorList stem p w).length = w.length := by
  induction stem generalizing w with
  | nil => simp [prefixColorList]
  | cons a r ih =>
    cases w with
    | nil => simp
    | cons b w => by_cases h : a = b <;> simp [prefixColorList, h, ih]

lemma prefixColor_inverse_fixes {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c) :
    ∀ c ∈ stem.getLast?, p.symm c = c := by
  intro c hc
  apply p.injective
  simp [hp c hc]

def prefixColorMap {d : ℕ} (stem : List (Fin d)) (p : Equiv.Perm (Fin d))
    (hp : ∀ c ∈ stem.getLast?, p c = c) (u : TreeVertex d) : TreeVertex d :=
  ⟨prefixColorList stem p u.1, prefixColorList_chain stem p hp u.1 u.2⟩

@[simp] lemma prefixColorMap_symm_apply {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c)
    (u : TreeVertex d) :
    prefixColorMap stem p.symm (prefixColor_inverse_fixes stem p hp)
      (prefixColorMap stem p hp u) = u := by
  apply Subtype.ext
  exact prefixColorList_inverse stem p u.1

lemma prefixColorMap_adj {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c)
    {u v : TreeVertex d} (h : treeAdj u v) :
    treeAdj (prefixColorMap stem p hp u) (prefixColorMap stem p hp v) := by
  change (∃ a, prefixColorList stem p v.1 = prefixColorList stem p u.1 ++ [a]) ∨
    (∃ a, prefixColorList stem p u.1 = prefixColorList stem p v.1 ++ [a])
  rcases h with ⟨a, ha⟩ | ⟨a, ha⟩
  · rw [ha]
    exact Or.inl (prefixColorList_append stem p u.1 a)
  · rw [ha]
    exact Or.inr (prefixColorList_append stem p v.1 a)

def prefixColorAut {d : ℕ} (stem : List (Fin d)) (p : Equiv.Perm (Fin d))
    (hp : ∀ c ∈ stem.getLast?, p c = c) : TreeAut d where
  toEquiv :=
    { toFun := prefixColorMap stem p hp
      invFun := prefixColorMap stem p.symm (prefixColor_inverse_fixes stem p hp)
      left_inv := prefixColorMap_symm_apply stem p hp
      right_inv := by
        intro u
        apply Subtype.ext
        simpa only [prefixColorMap, Equiv.symm_symm] using
          prefixColorList_inverse stem p.symm u.1 }
  map_adj := by
    intro u v
    change treeAdj (prefixColorMap stem p hp u) (prefixColorMap stem p hp v) ↔ treeAdj u v
    constructor
    · intro h
      simpa using prefixColorMap_adj stem p.symm (prefixColor_inverse_fixes stem p hp) h
    · exact prefixColorMap_adj stem p hp

@[simp] theorem prefixColorAut_val {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c)
    (u : TreeVertex d) :
    ((prefixColorAut stem p hp).toEquiv u).1 = prefixColorList stem p u.1 := rfl

@[simp] theorem prefixColorAut_length {d : ℕ} (stem : List (Fin d))
    (p : Equiv.Perm (Fin d)) (hp : ∀ c ∈ stem.getLast?, p c = c)
    (u : TreeVertex d) : ((prefixColorAut stem p hp).toEquiv u).1.length = u.1.length := by
  simp

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ObservableDisintegration
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

def graphLaw (P : Measure X) (Z : X → W) : Measure (W × X) :=
  P.map (fun x => (Z x, x))

instance graphLaw_finite (P : Measure X) [IsFiniteMeasure P] (Z : X → W) :
    IsFiniteMeasure (graphLaw P Z) := by
  unfold graphLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def kernel (P : Measure X) [IsFiniteMeasure P] (Z : X → W) : Kernel W X :=
  (graphLaw P Z).condKernel

end Problem367.ObservableDisintegration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RadialSummability
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

@[simp] theorem tsum_treeShell_radial (d n : ℕ) (f : ℕ → ℝ) :
    (∑' v : TreeShell d n, f v.1.1.length) =
      (Fintype.card (TreeShell d n) : ℝ) * f n := by
  calc
    (∑' v : TreeShell d n, f v.1.1.length) = ∑' _ : TreeShell d n, f n :=
      tsum_congr fun v => congrArg f v.2
    _ = _ := by simp [tsum_fintype]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_SeparatedLocalSupports
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.LocalSupportGeometry

def prefixVertex {d : ℕ} (v : TreeVertex d) (n : ℕ) : TreeVertex d :=
  ⟨v.1.take n, v.2.take n⟩

@[simp] theorem prefixVertex_length {d : ℕ} (v : TreeVertex d) (n : ℕ) :
    (prefixVertex v n).1.length = min n v.1.length := by
  simp [prefixVertex]

end Problem367.LocalSupportGeometry

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_UniformSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped unitInterval

namespace Problem367

theorem measurePreserving_uniform01_projIcc :
    MeasurePreserving (Set.projIcc (0 : ℝ) 1 (by norm_num))
      uniform01 (volume : Measure I) := by
  have hp : Measurable (Set.projIcc (0 : ℝ) 1 (by norm_num)) :=
    continuous_projIcc.measurable
  refine ⟨hp, ?_⟩
  change (volume.restrict (Set.Icc (0 : ℝ) 1)).map _ = _
  rw [← unitInterval.measurePreserving_coe.map_eq,
    Measure.map_map hp measurable_subtype_coe]
  simp only [Function.comp_def, Set.projIcc_val]
  exact Measure.map_id

theorem exists_uniform01_sampler {α : Type*} [MeasurableSpace α]
    [Nonempty α] [StandardBorelSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] :
    ∃ ξ : ℝ → α, Measurable ξ ∧ Measure.map ξ uniform01 = ν := by
  obtain ⟨f, hf, hmap⟩ := ν.exists_measurable_map_eq
  let p : ℝ → I := Set.projIcc 0 1 (by norm_num)
  have hp : Measurable p := measurePreserving_uniform01_projIcc.measurable
  refine ⟨f ∘ p, hf.comp hp, ?_⟩
  rw [← Measure.map_map hf hp]
  change (uniform01.map (Set.projIcc (0 : ℝ) 1 (by norm_num))).map f = ν
  rw [measurePreserving_uniform01_projIcc.map_eq]
  exact hmap

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_Observable
attribute [-simp] _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.FactorObservable

variable {d : ℕ}
variable {Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin)}

def field (Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin))
    (U : TreeVertex d → ℝ) (v : TreeVertex d) : ℝ :=
  (Phi U v).toReal

lemma measurable_field (hPhi : Measurable Phi) (v : TreeVertex d) :
    Measurable (fun U => field Phi U v) :=
  measurable_spinToReal.comp ((measurable_pi_apply v).comp hPhi)

lemma memLp_field (hPhi : Measurable Phi) (v : TreeVertex d) (p : ENNReal) :
    MemLp (fun U => field Phi U v) p (labelMeasure d) := by
  apply MemLp.of_bound (measurable_field hPhi v).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun U => (norm_spinToReal (Phi U v)).le)

def spinLp (hPhi : Measurable Phi) (v : TreeVertex d) : Lp ℝ 2 (labelMeasure d) :=
  (memLp_field hPhi v 2).toLp (fun U => field Phi U v)

lemma coe_spinLp (hPhi : Measurable Phi) (v : TreeVertex d) :
    (spinLp hPhi v : (TreeVertex d → ℝ) → ℝ) =ᵐ[labelMeasure d]
      (fun U => field Phi U v) :=
  (memLp_field hPhi v 2).coeFn_toLp

lemma integral_spinLp {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (v : TreeVertex d) : ∫ U, spinLp hPhi v U ∂labelMeasure d = 0 := by
  exact (integral_congr_ae (coe_spinLp hPhi v)).trans
    (hlaw.integral_factor_spin hPhi v)

lemma spinLp_mem_centered {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (v : TreeVertex d) : spinLp hPhi v ∈ centeredL2 (labelMeasure d) := by
  rw [mem_centeredL2_iff]
  exact integral_spinLp hPhi hlaw v

def centeredSpinLp {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (v : TreeVertex d) : centeredL2 (labelMeasure d) :=
  ⟨spinLp hPhi v, spinLp_mem_centered hPhi hlaw v⟩

@[simp] lemma centeredSpinLp_coe {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d))) (v : TreeVertex d) :
    (centeredSpinLp hPhi hlaw v : Lp ℝ 2 (labelMeasure d)) = spinLp hPhi v := rfl

end Problem367.FactorObservable

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_Transfer
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

def vertexSampler {d : ℕ} {α β : Type*} (f : α → β)
    (x : TreeVertex d → α) : TreeVertex d → β := fun v => f (x v)

@[simp] theorem vertexSampler_relabel {d : ℕ} {α β : Type*}
    (f : α → β) (g : TreeAut d) (x : TreeVertex d → α) :
    vertexSampler f (relabel g x) = relabel g (vertexSampler f x) := rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_WienerSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.WienerSampler

abbrev Path := C(ℝ≥0, ℝ)

instance pathMeasurableSpace : MeasurableSpace Path := borel Path
instance pathBorelSpace : BorelSpace Path := ⟨rfl⟩

theorem measurableEmbedding_denseEval : MeasurableEmbedding
    (fun f : Path => fun n : ℕ => f (TopologicalSpace.denseSeq ℝ≥0 n)) := by
  apply Measurable.measurableEmbedding
  · exact Measurable.of_eval fun index => (continuous_eval_const _).measurable
  · intro f g h
    apply ContinuousMap.coe_injective
    exact (TopologicalSpace.denseRange_denseSeq ℝ≥0).equalizer f.continuous g.continuous h

theorem measurable_path_of_eval {Ω : Type*} [MeasurableSpace Ω]
    {F : Ω → Path} (hF : ∀ t, Measurable (fun ω => F ω t)) : Measurable F := by
  apply measurableEmbedding_denseEval.measurable_comp_iff.mp
  exact Measurable.of_eval fun index => hF _

theorem exists_measurable_path_version {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t))
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => B t ω)) :
    ∃ F : Ω → Path, Measurable F ∧ ∀ᵐ ω ∂μ, ∀ t, F ω t = B t ω := by
  classical
  obtain ⟨N, hNsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hc)
  have hcont (ω : Ω) (hω : ω ∉ N) : Continuous (fun t => B t ω) := by
    by_contra h
    exact hω (hNsub h)
  let F : Ω → Path := fun ω => if hω : ω ∈ N then 0 else ⟨fun t => B t ω, hcont ω hω⟩
  refine ⟨F, ?_, ?_⟩
  · apply measurable_path_of_eval
    intro t
    have heq : (fun ω => F ω t) = N.piecewise (fun _ => 0) (B t) := by
      funext ω
      by_cases hω : ω ∈ N <;> simp [F, hω, Set.piecewise]
    rw [heq]
    exact measurable_const.piecewise hNm (hm t)
  · have hgood : ∀ᵐ ω ∂μ, ω ∉ N := by simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hNzero
    filter_upwards [hgood] with ω hω t
    simp [F, hω]

theorem measurable_brownian_version (t : ℝ≥0) : Measurable
    (BrownianContinuousExistence.version (fun s (ω : ℝ≥0 → ℝ) => ω s) t) := by
  exact (StronglyMeasurable.limUnder (fun n =>
    (measurable_pi_apply (Real.toNNReal (ContinuousModification.dyadicLeft t n))).stronglyMeasurable)).measurable

theorem isBrownian_eval_map {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {F : Ω → Path} (hF : Measurable F)
    (heq : ∀ᵐ ω ∂μ, ∀ t, F ω t = B t ω) :
    IsBrownianReal (fun t (f : Path) => f t) (μ.map F) where
  hasLaw I := by
    have hI : Measurable (fun f : Path => I.restrict (fun t => f t)) :=
      Measurable.of_eval fun index => (continuous_eval_const index.1).measurable
    refine ⟨hI.aemeasurable, ?_⟩
    rw [Measure.map_map hI hF]
    have he : (fun ω => I.restrict (fun t => F ω t)) =ᵐ[μ]
        (fun ω => I.restrict (fun t => B t ω)) := by
      filter_upwards [heq] with ω hω
      exact funext (fun i => hω i.1)
    exact (Measure.map_congr he).trans (hB.hasLaw I).map_eq
  cont := Filter.Eventually.of_forall (fun f => f.continuous)

theorem exists_wienerMeasure :
    ∃ ν : Measure Path, IsProbabilityMeasure ν ∧
      IsBrownianReal (fun t (f : Path) => f t) ν := by
  let B := BrownianContinuousExistence.version (fun t (ω : ℝ≥0 → ℝ) => ω t)
  have hB : IsBrownianReal B BrownianExistence.preWienerMeasure :=
    BrownianContinuousExistence.isBrownianReal_version
      BrownianExistence.coordinate_isPreBrownianReal
  obtain ⟨F, hF, heq⟩ := exists_measurable_path_version
    BrownianExistence.preWienerMeasure B measurable_brownian_version hB.cont
  exact ⟨BrownianExistence.preWienerMeasure.map F,
    (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),
    isBrownian_eval_map hB.toIsPreBrownianReal hF heq⟩

def wienerMeasure : Measure Path := Classical.choose exists_wienerMeasure

instance wienerProbability : IsProbabilityMeasure wienerMeasure :=
  (Classical.choose_spec exists_wienerMeasure).1

theorem exists_uniform01_wiener_sampler :
    ∃ ξ : ℝ → Path, Measurable ξ ∧ Measure.map ξ uniform01 = wienerMeasure :=
  exists_uniform01_sampler wienerMeasure

def sample : ℝ → Path := Classical.choose exists_uniform01_wiener_sampler

theorem measurable_sample : Measurable sample :=
  (Classical.choose_spec exists_uniform01_wiener_sampler).1

end Problem367.WienerSampler

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ContinuousObservationHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ContinuousObservationHistory

open WienerSampler

def stoppedPath (s : ℝ≥0) (f : Path) : Path :=
  ⟨fun t => f (min t s), f.continuous.comp (continuous_id.min continuous_const)⟩

@[simp]
theorem stoppedPath_apply (s : ℝ≥0) (f : Path) (t : ℝ≥0) :
    stoppedPath s f t = f (min t s) := rfl

end Problem367.ContinuousObservationHistory

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_ContinuousNoiseSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ContinuousNoiseSplit

open WienerSampler ContinuousObservationHistory

def futurePath (s : ℝ≥0) (f : Path) : Path :=
  ⟨fun t => f (s + t) - f s,
    (f.continuous.comp (continuous_const.add continuous_id)).sub continuous_const⟩

@[simp]
theorem futurePath_apply (s : ℝ≥0) (f : Path) (t : ℝ≥0) :
    futurePath s f t = f (s + t) - f s := rfl

end Problem367.ContinuousNoiseSplit

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ArrayPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367

namespace ArrayPosteriorStationarity

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

def spinArray (σ : TreeVertex d → IsingSpin) : TreeVertex d → ℝ :=
  fun v => spinSign (σ v)

end ArrayPosteriorStationarity
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_Innovation
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingInnovation

abbrev State (d : ℕ) (A : Type*) :=
  (TreeVertex d → IsingSpin) × (TreeVertex d → A)

def posterior {d : ℕ} {A : Type*} (beta : ℝ) (B : ℝ≥0 → A → ℝ)
    (v : TreeVertex d) (t : ℝ≥0) (q : State d A) : ℝ :=
  infiniteGibbsSpinMean beta v
    (fun i => plantedArrayObservation (fun _ : TreeVertex d => B)
      ArrayPosteriorStationarity.spinArray i t q)

def innovation {d : ℕ} {A : Type*} (beta : ℝ) (B : ℝ≥0 → A → ℝ)
    (v : TreeVertex d) (t : ℝ≥0) (q : State d A) : ℝ :=
  plantedArrayObservation (fun _ : TreeVertex d => B)
      ArrayPosteriorStationarity.spinArray v t q -
    nnrealTimePrimitive (posterior beta B v) t q

def uniformInnovation {d : ℕ} (beta : ℝ) :
    State d ℝ → TreeVertex d → ℝ≥0 → ℝ :=
  fun q v t => innovation beta (fun r u => WienerSampler.sample u r) v t q

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

def innovationPath
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} (X : Ω → C(ℝ≥0, ℝ))
    (m : ℝ≥0 → Ω → ℝ) (hm : IsStronglyProgressive F m)
    {K : ℝ≥0} (hbound : ∀ t ω, ‖m t ω‖ ≤ (K : ℝ)) (ω : Ω) :
    C(ℝ≥0, ℝ) :=
  ⟨fun t => X ω t - nnrealTimePrimitive m t ω,
    (X ω).continuous.sub (lipschitzWith_nnrealTimePrimitive_of_progressive hm hbound ω).continuous⟩

@[simp] theorem innovationPath_apply
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} (X : Ω → C(ℝ≥0, ℝ))
    (m : ℝ≥0 → Ω → ℝ) (hm : IsStronglyProgressive F m)
    {K : ℝ≥0} (hbound : ∀ t ω, ‖m t ω‖ ≤ (K : ℝ)) (ω : Ω) (t : ℝ≥0) :
    innovationPath X m hm hbound ω t = X ω t - nnrealTimePrimitive m t ω := rfl

@[simp] theorem innovationPath_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} (X : Ω → C(ℝ≥0, ℝ))
    (m : ℝ≥0 → Ω → ℝ) (hm : IsStronglyProgressive F m)
    {K : ℝ≥0} (hbound : ∀ t ω, ‖m t ω‖ ≤ (K : ℝ)) (ω : Ω) :
    innovationPath X m hm hbound ω 0 = X ω 0 := by
  simp [innovationPath, nnrealTimePrimitive]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationInnovation
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ContinuousNoiseSplit.futurePath_apply _root_.OAI.Problem367.ContinuousObservationHistory.stoppedPath_apply _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationInnovation

abbrev Paths (d : ℕ) := TreeVertex d → WienerSampler.Path

def evaluation {d : ℕ} (v : TreeVertex d) (t : ℝ≥0) (x : Paths d) : ℝ := x v t

theorem measurable_evaluation {d : ℕ} (v : TreeVertex d) (t : ℝ≥0) :
    Measurable (evaluation v t) :=
  (continuous_eval_const t).measurable.comp (measurable_pi_apply v)

def filtration (d : ℕ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Paths d)) :=
  arrayNaturalFiltration evaluation measurable_evaluation

def posterior {d : ℕ} (beta : ℝ) (v : TreeVertex d) (t : ℝ≥0) (x : Paths d) : ℝ :=
  infiniteGibbsSpinMean beta v (fun i => x i t)

theorem posterior_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (posterior beta v) := by
  apply isStronglyProgressive_infiniteGibbsSpinMean
  intro i
  apply (arrayNaturalFiltration_stronglyAdapted evaluation measurable_evaluation i).isStronglyProgressive_of_continuous
  intro x
  exact (x i).continuous

theorem posterior_norm_le_one {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : ‖posterior beta v t x‖ ≤ (1 : ℝ≥0) :=
  infiniteGibbsSpinMean_abs_le_one beta v _

def innovationMap {d : ℕ} (beta : ℝ) (x : Paths d) : Paths d := fun v =>
  innovationPath (fun x : Paths d => x v) (posterior beta v)
    (posterior_progressive beta v) (posterior_norm_le_one beta v) x

@[simp] theorem innovationMap_apply {d : ℕ} (beta : ℝ) (x : Paths d)
    (v : TreeVertex d) (t : ℝ≥0) :
    innovationMap beta x v t = x v t - nnrealTimePrimitive (posterior beta v) t x := rfl

@[simp] theorem innovationMap_zero {d : ℕ} (beta : ℝ) (x : Paths d)
    (v : TreeVertex d) : innovationMap beta x v 0 = x v 0 := by
  simp [innovationMap, nnrealTimePrimitive]

def uniformObservation {d : ℕ} (q : IsingInnovation.State d ℝ) : Paths d := fun v =>
  ⟨fun t => WienerSampler.sample (q.2 v) t + (t : ℝ) * spinSign (q.1 v),
    (WienerSampler.sample (q.2 v)).continuous.add
      (NNReal.continuous_coe.mul continuous_const)⟩

theorem measurable_uniformObservation {d : ℕ} :
    Measurable (uniformObservation (d := d)) := by
  apply Measurable.of_eval
  intro v
  apply WienerSampler.measurable_path_of_eval
  intro t
  have hsign : Measurable spinSign := by intro s hs; trivial
  exact ((continuous_eval_const t).measurable.comp
    (WienerSampler.measurable_sample.comp ((measurable_pi_apply v).comp measurable_snd))).add
    ((hsign.comp ((measurable_pi_apply v).comp measurable_fst)).const_mul (t : ℝ))

@[simp] theorem innovationMap_uniformObservation {d : ℕ} (beta : ℝ)
    (q : IsingInnovation.State d ℝ) (v : TreeVertex d) (t : ℝ≥0) :
    innovationMap beta (uniformObservation q) v t =
      IsingInnovation.uniformInnovation beta q v t := rfl

@[simp] theorem uniformObservation_relabel {d : ℕ} (g : TreeAut d)
    (q : IsingInnovation.State d ℝ) :
    uniformObservation (Prod.map (relabel g) (relabel g) q) =
      relabel g (uniformObservation q) := rfl

def observationLaw {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin)) : Measure (Paths d) :=
  (μ.prod (labelMeasure d)).map uniformObservation

end Problem367.IsingObservationInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_ContinuousCopyBrownian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ContinuousCopyBrownian

open WienerSampler ContinuousObservationHistory ContinuousNoiseSplit

variable {ι : Type*}

abbrev Joint := (ι → Path) × ((ι → Path) × (ι → Path))

end Problem367.ContinuousCopyBrownian

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ConditionalCopyBounds
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
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

abbrev CopySpace (d : ℕ) := ContinuousCopyBrownian.Joint (ι := TreeVertex d)

def fieldDifference {d : ℕ} (beta : ℝ) (v : TreeVertex d) (t : ℝ≥0)
    (q : CopySpace d) : ℝ :=
  Real.artanh (posterior beta v t q.2.1) - Real.artanh (posterior beta v t q.2.2)

end Problem367.IsingConditionalCopyBounds

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_FinitePathGibbs
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePathGibbs

def rawKernel (beta : ℝ) (h : ℕ → ℝ) (i : ℕ) (a b : IsingSpin) : ℝ :=
  Real.exp ((h i + beta * spinSign a) * spinSign b)

def tailPartition (beta : ℝ) (h : ℕ → ℝ) (n : ℕ) (a : IsingSpin) : ℝ :=
  ∑ x : Fin n → IsingSpin, InhomogeneousChain.weight (rawKernel beta h) n a x

@[simp] theorem tailPartition_zero (beta : ℝ) (h : ℕ → ℝ) (a : IsingSpin) :
    tailPartition beta h 0 a = 1 := by
  simp [tailPartition]

end Problem367.FinitePathGibbs

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathGibbs
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.TreePathGibbs

def vertexEquiv {d : ℕ} (v : TreeVertex d) :
    Fin (v.1.length + 1) ≃ ConnectedHull.vertices v :=
  Equiv.ofBijective
    (fun i => ⟨ConnectedHull.path v i,
      ConnectedHull.prefix_mem_vertices v (Nat.le_of_lt_succ i.isLt)⟩)
    ⟨fun i j hij => ConnectedHull.path_injective v (congrArg Subtype.val hij), by
      intro u
      obtain ⟨i, hi, he⟩ := ConnectedHull.mem_vertices.mp u.property
      exact ⟨⟨i, by omega⟩, Subtype.ext he⟩⟩

@[simp] theorem vertexEquiv_val {d : ℕ} (v : TreeVertex d)
    (i : Fin (v.1.length + 1)) :
    (vertexEquiv v i).val = ConnectedHull.path v i := rfl

end Problem367.TreePathGibbs

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_GibbsAutomorphism
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem367.TreeGibbsAut

variable {d : ℕ}

def vertexEquiv (g : TreeAut d) (D : Finset (TreeVertex d)) :
    D ≃ D.image g.toEquiv where
  toFun u := ⟨g.toEquiv u, Finset.mem_image.mpr ⟨u, u.property, rfl⟩⟩
  invFun v := ⟨g.toEquiv.symm v, by
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp v.property
    rw [← he, Equiv.symm_apply_apply]
    exact hu⟩
  left_inv u := Subtype.ext (g.toEquiv.symm_apply_apply u)
  right_inv v := Subtype.ext (g.toEquiv.apply_symm_apply v)

def spinEquiv (g : TreeAut d) (D : Finset (TreeVertex d)) :
    (D → IsingSpin) ≃ (D.image g.toEquiv → IsingSpin) where
  toFun eta v := eta ((vertexEquiv g D).symm v)
  invFun xi u := xi (vertexEquiv g D u)
  left_inv eta := by funext u; simp
  right_inv xi := by funext v; simp

@[simp] theorem spinEquiv_apply_image (g : TreeAut d) (D : Finset (TreeVertex d))
    (eta : D → IsingSpin) (u : D) :
    spinEquiv g D eta (vertexEquiv g D u) = eta u := by
  simp [spinEquiv]

end Problem367.TreeGibbsAut

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationLaw
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationInnovation

instance observationLaw_probability {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (observationLaw μ) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  unfold observationLaw
  exact Measure.isProbabilityMeasure_map measurable_uniformObservation.aemeasurable

end Problem367.IsingObservationInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationFactor
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
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

def field (beta : ℝ) (v : TreeVertex d) (t : ℝ≥0) (x : Paths d) : ℝ :=
  Real.artanh (posterior beta v t x)

def kernel (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] : Kernel (Paths d) (Paths d) :=
  ObservableDisintegration.kernel (observationLaw μ) (innovationMap beta)

def copies (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] : Measure (Paths d × (Paths d × Paths d)) :=
  ((observationLaw μ).map (innovationMap beta)) ⊗ₘ
    ((kernel beta μ) ×ₖ (kernel beta μ))

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyEnergyIntegrability
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
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

def responseRow {d : ℕ} (beta : ℝ) (v w : TreeVertex d) (p : ℝ × Paths d) : ℝ :=
  infiniteGibbsResponse beta v w (fun i => p.2 i p.1.toNNReal)

abbrev Joint (d : ℕ) := Paths d × (Paths d × Paths d)

def density {d : ℕ} (beta : ℝ) (v : TreeVertex d) (t : ℝ) (q : Joint d) : ℝ :=
  DiscrepancyEnergy.density
    (fun w q => responseRow beta v w (t, q.2.1))
    (fun w q => responseRow beta v w (t, q.2.2))
    (fun q => field beta v t.toNNReal q.2.1 - field beta v t.toNNReal q.2.2)
    (fun q => posterior beta v t.toNNReal q.2.1)
    (fun q => posterior beta v t.toNNReal q.2.2) q

end Problem367.IsingCopyEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcast
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

local instance rootedBroadcastMeasurableSingletonSpin_r34b34c_1 :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
def spinMul (a b : IsingSpin) : IsingSpin :=
  if a = b then IsingSpin.pos else IsingSpin.neg

@[simp] lemma spinMul_pos (a : IsingSpin) : spinMul a IsingSpin.pos = a := by
  cases a <;> rfl
@[simp] lemma pos_spinMul (a : IsingSpin) : spinMul IsingSpin.pos a = a := by
  cases a <;> rfl
@[simp] lemma spinMul_self (a : IsingSpin) : spinMul a a = IsingSpin.pos := by
  simp [spinMul]

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SpinEncoding
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def spinAgreementCode (a b : IsingSpin) : IsingSpin :=
  if a = b then .pos else .neg

lemma spinAgreementCode_injective_right (a : IsingSpin) :
    Function.Injective (spinAgreementCode a) := by
  intro b c h
  cases a <;> cases b <;> cases c <;> simp_all [spinAgreementCode]

@[simp] lemma spinAgreementCode_eq_pos_iff (a b : IsingSpin) :
    spinAgreementCode a b = .pos ↔ a = b := by
  cases a <;> cases b <;> simp [spinAgreementCode]

@[simp] lemma spinAgreementCode_eq_neg_iff (a b : IsingSpin) :
    spinAgreementCode a b = .neg ↔ a ≠ b := by
  cases a <;> cases b <;> simp [spinAgreementCode]

def connectedSpinEncode {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    (σ : D → IsingSpin) (v : D) : IsingSpin := by
  classical
  exact if hv : (v : TreeVertex d) = r then σ v else
    spinAgreementCode
      (σ ⟨parentVertex v, hD.parent_mem_of_ne_min hr hmin v.2 hv⟩) (σ v)

@[simp] lemma connectedSpinEncode_apply_root {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) (σ : D → IsingSpin) :
    connectedSpinEncode hD r hr hmin σ ⟨r, hr⟩ = σ ⟨r, hr⟩ := by
  simp [connectedSpinEncode]

lemma connectedSpinEncode_injective {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) :
    Function.Injective (connectedSpinEncode hD r hr hmin) := by
  classical
  intro σ τ hστ
  have aux : ∀ n : ℕ, ∀ v : D, v.1.1.length = n → σ v = τ v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hn
      by_cases hv : (v : TreeVertex d) = r
      · have hh := congrFun hστ v
        simpa [connectedSpinEncode, hv] using hh
      · let p : D := ⟨parentVertex v, hD.parent_mem_of_ne_min hr hmin v.2 hv⟩
        have hnil := ConnectedFinset.ne_nil_of_ne_min hmin v.2 hv
        have hpos : 0 < v.1.1.length := List.length_pos_iff.mpr hnil
        have hplen : p.1.1.length < n := by
          change (parentVertex v.1).1.length < n
          rw [parentVertex_length]
          omega
        have hpeq : σ p = τ p := ih p.1.1.length hplen p rfl
        have hh : spinAgreementCode (σ p) (σ v) =
            spinAgreementCode (τ p) (τ v) := by
          simpa [connectedSpinEncode, hv, p] using congrFun hστ v
        rw [hpeq] at hh
        exact spinAgreementCode_injective_right (τ p) hh
  funext v
  exact aux v.1.1.length v rfl

lemma connectedSpinEncode_bijective {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) :
    Function.Bijective (connectedSpinEncode hD r hr hmin) := by
  have hi := connectedSpinEncode_injective hD r hr hmin
  exact ⟨hi, Finite.surjective_of_injective hi⟩

def connectedSpinEquiv {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) :
    (D → IsingSpin) ≃ (D → IsingSpin) :=
  Equiv.ofBijective _ (connectedSpinEncode_bijective hD r hr hmin)

@[simp] lemma connectedSpinEquiv_apply {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) (σ : D → IsingSpin) :
    connectedSpinEquiv hD r hr hmin σ = connectedSpinEncode hD r hr hmin σ := rfl

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

def root (d : ℕ) : TreeVertex d := ⟨[], List.isChain_nil⟩

@[simp] lemma root_val (d : ℕ) : (root d).val = [] := rfl

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

abbrev BranchVertex {d : ℕ} (c : Fin d) := {v : TreeVertex d // [c] <+: v.val}

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastConeLocality
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

abbrev DescendantVertex {d : ℕ} (c : TreeVertex d) :=
  {v : TreeVertex d // c.1 <+: v.1}

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_LawSpectral
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
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

def reflection (c : Fin d) : (TreeVertex d → A) → (TreeVertex d → A) :=
  relabel (prefixTreeAut c)

omit [MeasurableSpace A] in
theorem reflection_involutive (c : Fin d) :
    Function.Involutive (reflection (A := A) c) := by
  intro U
  funext v
  change U (prefixFlip c (prefixFlip c v)) = U v
  rw [prefixFlip_twice]

def average : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  koopmanAverage (fun c : Fin d => reflection c) (fun c => hμ (prefixTreeAut c))

def generatorOperator (c : Fin d) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  koopmanL2 (reflection c) (hμ (prefixTreeAut c))

@[simp] theorem generatorOperator_sq (c : Fin d) :
    generatorOperator μ hμ c * generatorOperator μ hμ c = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  exact koopmanL2_involutive _ _ (reflection_involutive c) f

variable [IsFiniteMeasure μ]

def centeredAverage : centeredL2 μ →L[ℝ] centeredL2 μ :=
  centeredKoopmanAverage (fun c : Fin d => reflection c)
    (fun c => hμ (prefixTreeAut c)) reflection_involutive

@[simp] theorem centeredAverage_apply_coe (f : centeredL2 μ) :
    (centeredAverage μ hμ f : Lp ℝ 2 μ) = average μ hμ f := rfl

end Problem367.TreeLawKoopman

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
open IsingObservationInnovation IsingObservationFactor PlantedSymmetry

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def cavityObservable (hbeta : 0 ≤ beta) (t : ℝ≥0) (v w : TreeVertex d)
    (x : Paths d) : ℝ :=
  CavityArray.field (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
    (fun i => field beta i t x) v w

end Problem367.IsingCopySpectral

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

open IsingObservationInnovation IsingObservationFactor
open IsingCopySpectral

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def siteVariance (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (o : TreeVertex d) (t : ℝ≥0) : ℝ :=
  ∫ q, (IsingConditionalCopyBounds.fieldDifference beta o t q) ^ 2 ∂copies beta μ

end Problem367.IsingCopySmallLogLoss

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_OrbitAverage
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem367.TreeOrbitAverage

def Extension {d : ℕ} (stem : List (Fin d)) (n : ℕ) :=
  {s : List (Fin d) // s.length = n ∧ (stem ++ s).IsChain (· ≠ ·)}

instance extensionFinite {d : ℕ} (stem : List (Fin d)) (n : ℕ) :
    Finite (Extension stem n) :=
  Finite.of_injective (β := List.Vector (Fin d) n)
    (fun s : Extension stem n => (⟨s.1, s.2.1⟩ : List.Vector (Fin d) n))
    (fun _ _ h => Subtype.ext (congrArg (fun s : List.Vector (Fin d) n => s.1) h))

instance extensionFintype {d : ℕ} (stem : List (Fin d)) (n : ℕ) :
    Fintype (Extension stem n) := Fintype.ofFinite _

def extensionNilEquivTreeShell (d n : ℕ) :
    Extension ([] : List (Fin d)) n ≃ TreeShell d n where
  toFun s := ⟨⟨s.1, by
    change s.1.IsChain (· ≠ ·)
    exact s.2.2⟩, s.2.1⟩
  invFun s := ⟨s.1.1, s.2, by
    change s.1.1.IsChain (· ≠ ·)
    exact s.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem card_extension_nil_zero (d : ℕ) :
    Fintype.card (Extension ([] : List (Fin d)) 0) = 1 := by
  rw [Fintype.card_congr (extensionNilEquivTreeShell d 0), card_treeShell_zero]

@[simp] theorem card_extension_nil_succ (d n : ℕ) :
    Fintype.card (Extension ([] : List (Fin d)) (n + 1)) = d * (d - 1) ^ n := by
  rw [Fintype.card_congr (extensionNilEquivTreeShell d (n + 1)), card_treeShell_succ]

def endpoint {d : ℕ} {stem : List (Fin d)} {n : ℕ}
    (s : Extension stem n) : TreeVertex d := ⟨stem ++ s.1, s.2.2⟩

end Problem367.TreeOrbitAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_RootAttenuation
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal BigOperators

namespace Problem367.IsingRootAttenuation

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds
open TreeOrbitAverage

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def rootAttenuation (hbeta : 0 ≤ beta) (t : ℝ≥0) (v : TreeVertex d)
    (x : Paths d) : ℝ :=
  ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
    (CavityArray.field (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (fun w => field beta w t x) (ConnectedHull.takeVertex v (i + 1))
        (ConnectedHull.takeVertex v i))

end Problem367.IsingRootAttenuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathRerooting
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def dropVertex {d : ℕ} (v : TreeVertex d) (i : ℕ) : TreeVertex d :=
  ⟨v.1.drop i, v.2.drop i⟩

@[simp] theorem dropVertex_val {d : ℕ} (v : TreeVertex d) (i : ℕ) :
    (dropVertex v i).1 = v.1.drop i := rfl

@[simp] theorem dropVertex_length {d : ℕ} (v : TreeVertex d) (i : ℕ) :
    (dropVertex v i).1.length = v.1.length - i := by simp

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_WordCancellation
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.TreeKoopman

def reverseVertex {d : ℕ} (v : TreeVertex d) : TreeVertex d :=
  ⟨v.1.reverse, by
    change List.IsChain (fun a b => a ≠ b) v.1.reverse
    rw [List.isChain_reverse]
    exact v.2.imp (fun _ _ h => Ne.symm h)⟩

@[simp] theorem reverseVertex_twice {d : ℕ} (v : TreeVertex d) :
    reverseVertex (reverseVertex v) = v := by
  apply Subtype.ext
  exact List.reverse_reverse v.1

end Problem367.TreeKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_OrientedPath
attribute [-simp] _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.tsum_treeShell_radial
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
open ConnectedHull

def edge {d : ℕ} (inward : Bool) (v : TreeVertex d) (i : ℕ) :
    TreeVertex d × TreeVertex d :=
  if inward then (takeVertex v i, takeVertex v (i + 1))
  else (takeVertex v (i + 1), takeVertex v i)

def attenuation {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta) (t : ℝ≥0)
    (inward : Bool) (v : TreeVertex d) (x : Paths d) : ℝ :=
  ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
    (cavityObservable hb t (edge inward v i).1 (edge inward v i).2 x)

@[simp] theorem attenuation_outward {d : ℕ} {beta : ℝ}
    (hb : 0 ≤ beta) (t : ℝ≥0) (v : TreeVertex d) :
    attenuation hb t false v = IsingRootAttenuation.rootAttenuation hb t v := rfl

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_OrientedPrefixWeights
attribute [-simp] _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.tsum_treeShell_radial
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
open TreeOrbitAverage ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def extensionAt (v : TreeVertex d) (p : ℕ) :
    Extension (v.1.take p) (v.1.length - p) :=
  ⟨v.1.drop p, List.length_drop, by rw [List.take_append_drop]; exact v.2⟩

@[simp] theorem endpoint_extensionAt (v : TreeVertex d) (p : ℕ) :
    endpoint (extensionAt v p) = v := by
  apply Subtype.ext
  exact List.take_append_drop p v.1

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RestrictedCutCardinality
attribute [-simp] _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def restrictedTreeCut {d : ℕ} (allowed : Finset (Fin d)) (k : ℕ) :
    Finset (TreeShell d (k + 1)) :=
  (allowed.sigma (fun c => (Finset.univ : Finset (ReducedTail c k)))).map
    (treeShellSuccEquiv d k).symm.toEmbedding

@[simp] theorem mem_restrictedTreeCut {d k : ℕ} (allowed : Finset (Fin d))
    (v : TreeShell d (k + 1)) :
    v ∈ restrictedTreeCut allowed k ↔ (treeShellSuccEquiv d k v).1 ∈ allowed := by
  classical
  simp [restrictedTreeCut]

@[simp] theorem card_restrictedTreeCut {d : ℕ} (allowed : Finset (Fin d)) (k : ℕ) :
    (restrictedTreeCut allowed k).card = allowed.card * (d - 1) ^ k := by
  classical
  simp [restrictedTreeCut, Finset.card_sigma]

def avoidingTreeCut {d : ℕ} (forbidden : Finset (Fin d)) (k : ℕ) :
    Finset (TreeShell d (k + 1)) :=
  restrictedTreeCut (Finset.univ \ forbidden) k

@[simp] theorem mem_avoidingTreeCut {d k : ℕ} (forbidden : Finset (Fin d))
    (v : TreeShell d (k + 1)) :
    v ∈ avoidingTreeCut forbidden k ↔ (treeShellSuccEquiv d k v).1 ∉ forbidden := by
  classical
  simp [avoidingTreeCut]

@[simp] theorem card_avoidingTreeCut {d : ℕ} (forbidden : Finset (Fin d)) (k : ℕ) :
    (avoidingTreeCut forbidden k).card = (d - forbidden.card) * (d - 1) ^ k := by
  classical
  simp [avoidingTreeCut, Finset.card_sdiff]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CutContinuations
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem isChain_append_iff_last {α : Type*} {R : α → α → Prop}
    (p q : List α) (hp : p ≠ []) :
    List.IsChain R (p ++ q) ↔
      List.IsChain R p ∧ List.IsChain R (p.getLast hp :: q) := by
  induction p with
  | nil => exact False.elim (hp rfl)
  | cons a p ih =>
    cases p with
    | nil => simp
    | cons b p =>
      simpa only [List.cons_append, List.isChain_cons_cons, List.getLast_cons_cons,
        and_assoc] using and_congr_right (fun _ : R a b => ih (by simp))

def cutLastColor {d k : ℕ} (v : TreeShell d (k + 1)) : Fin d :=
  v.1.1.getLast (by intro h; have hv := v.2; simp [h] at hv)

def appendCutContinuation {d k L : ℕ} (v : TreeShell d (k + 1))
    (w : ReducedTail (cutLastColor v) L) : TreeShell d (k + 1 + L) :=
  ⟨⟨v.1.1 ++ w.1,
    (isChain_append_iff_last v.1.1 w.1 (by intro h; have hv := v.2; simp [h] at hv)).mpr
      ⟨v.1.2, w.2.2⟩⟩, by simp [v.2, w.2.1]⟩

def cutPrefix {d k L : ℕ} (v : TreeShell d (k + 1 + L)) : TreeShell d (k + 1) :=
  ⟨⟨v.1.1.take (k + 1), v.1.2.take _⟩, by simp [List.length_take, v.2]⟩

@[simp] theorem cutPrefix_appendCutContinuation {d k L : ℕ}
    (v : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor v) L) :
    cutPrefix (appendCutContinuation v w) = v := by
  apply Subtype.ext
  apply Subtype.ext
  simp [cutPrefix, appendCutContinuation, v.2]

def cutSuffix {d k L : ℕ} (v : TreeShell d (k + 1 + L)) :
    ReducedTail (cutLastColor (cutPrefix v)) L := by
  refine ⟨v.1.1.drop (k + 1), ?_, ?_⟩
  · simp [List.length_drop, v.2]
  · have h : List.IsChain (fun a b : Fin d => a ≠ b)
        (v.1.1.take (k + 1) ++ v.1.1.drop (k + 1)) := by
      rw [List.take_append_drop]
      exact v.1.2
    exact ((isChain_append_iff_last _ _
      (by intro heq; have := (cutPrefix v).2; simp [cutPrefix, heq] at this)).mp h).2

@[simp] theorem appendCutContinuation_prefix_suffix {d k L : ℕ}
    (v : TreeShell d (k + 1 + L)) :
    appendCutContinuation (cutPrefix v) (cutSuffix v) = v := by
  apply Subtype.ext
  apply Subtype.ext
  exact List.take_append_drop _ _

def cutDescendants {d k : ℕ} (I : Finset (TreeShell d (k + 1))) (L : ℕ) :
    Finset (TreeShell d (k + 1 + L)) := by
  classical
  exact Finset.univ.filter (fun v => cutPrefix v ∈ I)

@[simp] theorem mem_cutDescendants {d k L : ℕ}
    (I : Finset (TreeShell d (k + 1))) (v : TreeShell d (k + 1 + L)) :
    v ∈ cutDescendants I L ↔ cutPrefix v ∈ I := by
  classical
  simp [cutDescendants]

def rootPathVertex {d : ℕ} (v : TreeVertex d) (i : ℕ) : TreeVertex d :=
  ⟨v.1.take i, v.2.take i⟩

def cutContinuationProduct {d k L : ℕ} (a : TreeVertex d → ℝ)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) : ℝ :=
  ∏ j ∈ Finset.range L,
    a (rootPathVertex (appendCutContinuation p w).1 (k + 1 + (j + 1)))

theorem cutContinuation_vertex_descendant {d k L : ℕ}
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) (j : ℕ) :
    p.1.1 <+:
      (rootPathVertex (appendCutContinuation p w).1 (k + 1 + (j + 1))).1 := by
  change p.1.1 <+: (p.1.1 ++ w.1).take (k + 1 + (j + 1))
  have htake : p.1.1.take (k + 1 + (j + 1)) = p.1.1 :=
    List.take_of_length_le (by rw [p.2]; omega)
  rw [List.take_append, htake]
  exact List.prefix_append _ _

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CutContinuationChannels
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367.CutContinuationChannels
open RootedBroadcast

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

abbrev ConeSample (A : Type*) (v : TreeVertex d) :=
  (DescendantVertex v → IsingSpin) × (DescendantVertex v → A)

def globalCone (v : TreeVertex d)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) : ConeSample A v :=
  ((fun u => z.1 u.1), fun u => z.2 u.1)

def restrictCone {u v : TreeVertex d} (h : u.1 <+: v.1)
    (z : ConeSample A u) : ConeSample A v :=
  ((fun w => z.1 ⟨w.1, h.trans w.2⟩), fun w => z.2 ⟨w.1, h.trans w.2⟩)

def globalFactors (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) (v : TreeVertex d) : ℝ :=
  F v (globalCone v z)

def continuationChannel (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    {k L : ℕ} (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L)
    (z : ConeSample A p.1) : ℝ :=
  ∏ j ∈ Finset.range L,
    F (rootPathVertex (appendCutContinuation p w).1 (k + 1 + (j + 1)))
      (restrictCone (cutContinuation_vertex_descendant p w j) z)

omit [MeasurableSpace A] in
@[simp] theorem continuationChannel_globalCone
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    {k L : ℕ} (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    continuationChannel F p w (globalCone p.1 z) =
      cutContinuationProduct (globalFactors F z) p w := rfl

def averageChannel (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    {k : ℕ} (p : TreeShell d (k + 1)) (L : ℕ) (z : ConeSample A p.1) : ℝ :=
  (∑ w : ReducedTail (cutLastColor p) L, continuationChannel F p w z) /
    (Fintype.card (ReducedTail (cutLastColor p) L) : ℝ)

omit [MeasurableSpace A] in
@[simp] theorem averageChannel_globalCone
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    {k : ℕ} (p : TreeShell d (k + 1)) (L : ℕ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    averageChannel F p L (globalCone p.1 z) =
      (∑ w : ReducedTail (cutLastColor p) L,
        cutContinuationProduct (globalFactors F z) p w) / (((d - 1) ^ L : ℕ) : ℝ) := by
  simp [averageChannel]

end Problem367.CutContinuationChannels

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BranchFlipGeometry
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace RootedBroadcast

def branchRoot {d : ℕ} (c : Fin d) : TreeVertex d :=
  ⟨[c], List.IsChain.singleton c⟩

@[simp] theorem branchRoot_val {d : ℕ} (c : Fin d) : (branchRoot c).val = [c] := rfl

@[simp] theorem prefixFlip_root {d : ℕ} (c : Fin d) :
    prefixFlip c (root d) = branchRoot c := rfl

@[simp] theorem prefixFlip_branchRoot {d : ℕ} (c : Fin d) :
    prefixFlip c (branchRoot c) = root d := by
  apply Subtype.ext
  simp [prefixFlip, prefixFlipWord, branchRoot, root]

theorem not_prefix_flip_of_prefix {d : ℕ} (c : Fin d) (v : TreeVertex d)
    (hv : [c] <+: v.val) : ¬ [c] <+: (prefixFlip c v).val := by
  rcases v with ⟨w, hw⟩
  rcases hv with ⟨t, ht⟩
  have heq : w = c :: t := by simpa using ht.symm
  subst w
  simp only [prefixFlip, prefixFlipWord]
  cases t with
  | nil => simp
  | cons b t =>
    have hcb : c ≠ b := (List.isChain_cons_cons.mp hw).1
    intro hprefix
    have heq : [c] = [b] :=
      (List.prefix_of_prefix_length_le hprefix (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eq_of_length (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    exact hcb (by simpa using heq)

def flipBranchToComplement {d : ℕ} (c : Fin d) (v : BranchVertex c) :
    {w : TreeVertex d // ¬ [c] <+: w.val} :=
  ⟨prefixFlip c v.val, not_prefix_flip_of_prefix c v.val v.property⟩

@[simp] theorem flipBranchToComplement_val {d : ℕ} (c : Fin d) (v : BranchVertex c) :
    (flipBranchToComplement c v).val = prefixFlip c v.val := rfl

@[simp] theorem prefixTreeAut_symm_root {d : ℕ} (c : Fin d) :
    (prefixTreeAut c).toEquiv.symm (root d) = branchRoot c := rfl

@[simp] theorem prefixTreeAut_symm_branchRoot {d : ℕ} (c : Fin d) :
    (prefixTreeAut c).toEquiv.symm (branchRoot c) = root d :=
  prefixFlip_branchRoot c

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ConeCoding
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeConeCoding

def encode {b : ℕ} (c : Fin (b + 1)) : List (Fin b) → List (Fin (b + 1))
  | [] => []
  | i :: w => (finSuccAboveEquiv c i).1 :: encode (finSuccAboveEquiv c i).1 w

@[simp] theorem encode_nil {b : ℕ} (c : Fin (b + 1)) : encode c [] = [] := rfl

@[simp] theorem length_encode {b : ℕ} (c : Fin (b + 1)) (w : List (Fin b)) :
    (encode c w).length = w.length := by
  induction w generalizing c with
  | nil => rfl
  | cons i w ih => simp only [encode, List.length_cons, ih]

theorem chain_encode {b : ℕ} (c : Fin (b + 1)) (w : List (Fin b)) :
    List.IsChain (fun a b => a ≠ b) (c :: encode c w) := by
  induction w generalizing c with
  | nil => exact List.IsChain.singleton c
  | cons i w ih =>
      exact List.isChain_cons_cons.mpr ⟨(finSuccAboveEquiv c i).2.symm, ih _⟩

@[simp] theorem encode_take {b : ℕ} (c : Fin (b + 1)) (w : List (Fin b)) (n : ℕ) :
    encode c (w.take n) = (encode c w).take n := by
  induction n generalizing c w with
  | zero => simp
  | succ n ih =>
      cases w with
      | nil => rfl
      | cons i w => simp only [List.take_succ_cons, encode, ih]

theorem chain_append_iff {α : Type*} (R : α → α → Prop) (r w : List α) (hr : r ≠ []) :
    List.IsChain R (r ++ w) ↔ List.IsChain R r ∧ List.IsChain R (r.getLast hr :: w) := by
  conv_lhs => rw [← List.dropLast_append_getLast hr]
  simp only [List.append_assoc, List.singleton_append]
  rw [List.isChain_split, List.dropLast_append_getLast]

def vertex {b : ℕ} (r : TreeVertex (b + 1)) (hr : r.1 ≠ [])
    (w : List (Fin b)) : TreeVertex (b + 1) :=
  ⟨r.1 ++ encode (r.1.getLast hr) w,
    (chain_append_iff _ _ _ hr).mpr ⟨r.2, chain_encode _ _⟩⟩

@[simp] theorem vertex_val {b : ℕ} (r : TreeVertex (b + 1)) (hr : r.1 ≠ [])
    (w : List (Fin b)) :
    (vertex r hr w).1 = r.1 ++ encode (r.1.getLast hr) w := rfl

@[simp] theorem vertex_nil {b : ℕ} (r : TreeVertex (b + 1)) (hr : r.1 ≠ []) :
    vertex r hr [] = r := by
  apply Subtype.ext
  simp

@[simp] theorem length_vertex {b : ℕ} (r : TreeVertex (b + 1)) (hr : r.1 ≠ [])
    (w : List (Fin b)) : (vertex r hr w).1.length = r.1.length + w.length := by
  simp

end Problem367.TreeConeCoding

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathSideBranches
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.PathSideBranches

def sideColor {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : Fin d :=
  Classical.choose (Fin.exists_ne_and_ne_of_two_lt v.1[i]
    (v.1.getD (i.1 + 1) v.1[i]) (by omega))

theorem sideColor_ne_incoming {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : sideColor hd v i ≠ v.1[i] :=
  (Classical.choose_spec (Fin.exists_ne_and_ne_of_two_lt v.1[i]
    (v.1.getD (i.1 + 1) v.1[i]) (by omega))).1

theorem take_target_ne_nil {d : ℕ} (v : TreeVertex d)
    (i : Fin v.1.length) : v.1.take (i.1 + 1) ≠ [] := by
  have hlen : (v.1.take (i.1 + 1)).length = i.1 + 1 := by
    simp only [List.length_take, Nat.min_eq_left (by omega : i.1 + 1 ≤ v.1.length)]
  intro h
  rw [h] at hlen
  simp at hlen

def sideVertex {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : TreeVertex d :=
  ⟨v.1.take (i.1 + 1) ++ [sideColor hd v i], by
    apply (TreeConeCoding.chain_append_iff _ _ _ (take_target_ne_nil v i)).mpr
    refine ⟨v.2.take _, ?_⟩
    simp only [List.take_succ_eq_append_getElem i.2, List.getLast_append_singleton]
    exact List.isChain_cons_cons.mpr
      ⟨(sideColor_ne_incoming hd v i).symm, List.IsChain.singleton _⟩⟩

@[simp] theorem sideVertex_val {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) :
    (sideVertex hd v i).1 = v.1.take (i.1 + 1) ++ [sideColor hd v i] := rfl

@[simp] theorem sideVertex_length {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : (sideVertex hd v i).1.length = i.1 + 2 := by
  simp only [sideVertex_val, List.length_append, List.length_take,
    Nat.min_eq_left (by omega : i.1 + 1 ≤ v.1.length), List.length_singleton]

@[simp] theorem parent_sideVertex {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) :
    parentVertex (sideVertex hd v i) = ConnectedHull.takeVertex v (i.1 + 1) := by
  apply Subtype.ext
  simp [parentVertex, sideVertex, ConnectedHull.takeVertex]

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

def noisyRegionArray {d : ℕ} {A : Type*} (S : Set (TreeVertex d))
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    (S → IsingSpin) × (S → A) :=
  (S.domRestrict z.1, S.domRestrict z.2)

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyPathLocality
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.PathSideBranches

@[implicit_reducible] def noisyRegionSigma {d : ℕ} {A : Type*}
    [MeasurableSpace A] (S : Set (TreeVertex d)) :
    MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) :=
  MeasurableSpace.comap (noisyRegionArray (A := A) S) inferInstance

def restrictNoisyRegion {d : ℕ} {A : Type*} {S T : Set (TreeVertex d)}
    (hST : S ⊆ T) (p : (T → IsingSpin) × (T → A)) :
    (S → IsingSpin) × (S → A) :=
  ((fun u => p.1 ⟨u.1, hST u.2⟩), fun u => p.2 ⟨u.1, hST u.2⟩)

@[simp] theorem restrictNoisyRegion_array {d : ℕ} {A : Type*}
    {S T : Set (TreeVertex d)} (hST : S ⊆ T)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    restrictNoisyRegion hST (noisyRegionArray T z) = noisyRegionArray S z := rfl

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_SharpVarianceRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367
open IsingObservationInnovation IsingObservationFactor IsingCopySmallLogLoss
open ConnectedHull

def ActualRootVarianceIdentity {d : ℕ} (beta : ℝ)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] : Prop :=
  ∀ T : ℝ≥0,
    AbsolutelyContinuousOnInterval
      (fun t : ℝ => siteVariance beta μ (root d) t.toNNReal) 0 (T : ℝ) ∧
    (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (T : ℝ)),
      deriv (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) t =
        ∫ q, IsingCopyEnergy.density beta (root d) t q ∂copies beta μ)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_ArtanhMartingaleFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem367.ArtanhMartingaleFormula

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def secondWeight (x : ℝ) : ℝ := x / (1 - x ^ 2) ^ 2

end Problem367.ArtanhMartingaleFormula

end

end OAI
end


