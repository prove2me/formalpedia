-- Prove2me | Definitions.Def_Q243FI003
-- name    : Q243FI003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T01:40:53.87743+00:00
-- url     : https://prove2.me/theorems/0628a1d1-d8f6-47ce-b7c6-a7a5461559ba
-- title:
--   Definitions bundle Q243FI003 of the split of OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 228 declarations of OpenAI's Lean: 84 definitions and 144 theorems. The definitions and types are `OAI.Problem367.ArrayPosteriorStationarity.filtration`, `OAI.Problem367.ArrayPosteriorStationarity.plantedRelabel`, `OAI.Problem367.ArrayPosteriorStationarity.posterior`, `OAI.Problem367.ArtanhMartingaleFormula.compensatorSum`, `OAI.Problem367.ArtanhMartingaleFormula.quadraticSum`, `OAI.Problem367.CavityArray.SitePair`, `OAI.Problem367.CavityArray.pairRelabel`, `OAI.Problem367.CavityFieldLimit.finiteCavityField`, `OAI.Problem367.CavityFieldLimit.finiteSiteField`, `OAI.Problem367.CavityFieldLimit.infiniteCavityField`, `OAI.Problem367.CavityFieldLimit.rootResponseProduct`, `OAI.Problem367.ColoredEdgeLifts.centeredKoopmanEquiv`, `OAI.Problem367.ColoredEdgeLifts.centeredKoopmanIsometry`, `OAI.Problem367.ColoredEdgeLifts.koopmanEquiv`, `OAI.Problem367.ColoredPathAverage.headVertex`, `OAI.Problem367.ColoredPathAverage.pathReducedTailEquiv`, `OAI.Problem367.ColoredPathAverage.tailVertex`, `OAI.Problem367.ComponentSignalAttenuation.posteriorLaw`, `OAI.Problem367.ComponentSignalAttenuation.posteriorMean`, `OAI.Problem367.ConnectedHull.pathEdge`, `OAI.Problem367.ContinuousCopyBrownian.history`, `OAI.Problem367.ContinuousCopyBrownian.joinedFiltration`, `OAI.Problem367.ContinuousCopyBrownian.pastSpace`, `OAI.Problem367.ContinuousNoiseSplit.futureArray`, `OAI.Problem367.ContinuousObservationHistory.stoppedArray`, `OAI.Problem367.CopyDifference.averageOnDifferences`, `OAI.Problem367.CopyDifference.differenceKoopmanEquiv`, `OAI.Problem367.CopyDifference.differenceKoopmanIsometry`, `OAI.Problem367.FilteringCrossEnergy.innovation`, `OAI.Problem367.FiniteIsingFiltering.State`, `OAI.Problem367.FiniteIsingFiltering.covariance`, `OAI.Problem367.FiniteIsingFiltering.innovation`, `OAI.Problem367.FiniteIsingFiltering.mean`, `OAI.Problem367.FiniteIsingFiltering.observationFiltration`, `OAI.Problem367.FiniteIsingFiltering.quadraticCompensator`, `OAI.Problem367.FiniteIsingFiltering.signal`, `OAI.Problem367.FiniteIsingSplit.field`, `OAI.Problem367.FiniteIsingSplit.mean`, `OAI.Problem367.FiniteIsingSplit.observedEnergy`, `OAI.Problem367.FinitePathGibbs.backwardField` and 44 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `FreeIsing_Brownian_ArrayInnovation`, `FreeIsing_Brownian_ArrayLaw`, `FreeIsing_Brownian_ArrayMoments`, `FreeIsing_Brownian_ArrayObservation`, `FreeIsing_Brownian_Characterization`, `FreeIsing_Brownian_Innovation`, `FreeIsing_Brownian_LinearCombination`, `FreeIsing_Cavity_Array`, `FreeIsing_Cavity_FieldL2Limit`, `FreeIsing_Cavity_Homeomorph`, `FreeIsing_Conditioning_CenteredCopyDifference`, `FreeIsing_Conditioning_Characteristic`, `FreeIsing_Conditioning_GaussianVector`, `FreeIsing_Estimates_ArrayInnovationLaw`, `FreeIsing_Estimates_ArrayInnovationProjection`, `FreeIsing_Estimates_CharacteristicRecurrence`, `FreeIsing_Estimates_FiniteGibbsField`, `FreeIsing_Estimates_FiniteIsingCompensatedSquare`, `FreeIsing_Estimates_FiniteIsingInnovation`, `FreeIsing_Estimates_FiniteIsingSplit`, `FreeIsing_Estimates_FiniteMarginals`, `FreeIsing_Estimates_FiniteSpinCoupling`, `FreeIsing_Estimates_FreeLawStationarity`, `FreeIsing_Estimates_FreeLawUnique`, `FreeIsing_Estimates_InnovationCharacteristic`, `FreeIsing_Estimates_MessageFunction`, `FreeIsing_Estimates_PairedFiniteField`, `FreeIsing_Estimates_ProgressiveArrayInnovation`, `FreeIsing_Estimates_ProgressivePrimitive`, `FreeIsing_Estimates_ProgressivePrimitiveFubini`, `FreeIsing_Factors_CoordinateNaturality`, `FreeIsing_Gaussian_ArrayCharacterization`, `FreeIsing_Gaussian_ComponentSignalAttenuation`, `FreeIsing_Gaussian_ContinuousNoiseSplit`, `FreeIsing_Gaussian_FiniteFieldGaussianEnergy`, `FreeIsing_Gaussian_FiniteGaussianPlanted`, `FreeIsing_Gaussian_TreeResponse`, `FreeIsing_Gaussian_TreeResponseEnergy`, `FreeIsing_Gaussian_TreeResponseMixture`, `FreeIsing_Gaussian_TreeResponseNaturality`, `FreeIsing_Gaussian_TreeResponsePlanted`, `FreeIsing_Gibbs_Leaf`, `FreeIsing_Gibbs_LeafMessage`, `FreeIsing_Gibbs_Weights`, `FreeIsing_Ising_GaussianPosterior`, `FreeIsing_Martingales_ArtanhMartingaleFormula`, `FreeIsing_Martingales_GaussianCriterion`, `FreeIsing_Martingales_InnovationMartingale`, `FreeIsing_Posterior_ArrayPosteriorStationarity`, `FreeIsing_Posterior_ContinuousObservationHistory`, `FreeIsing_Posterior_FieldCalculus`, `FreeIsing_Posterior_Fields`, `FreeIsing_Posterior_FilteringCrossEnergy`, `FreeIsing_Posterior_FiniteIsingFilteringRepresentation`, `FreeIsing_Posterior_GaussianGradient`, `FreeIsing_Posterior_InfinitePosteriorField`, `FreeIsing_Posterior_PlantedBridgeInfinite`, `FreeIsing_Posterior_PlantedBridgeVector`, `FreeIsing_Posterior_PlantedStationarity`, `FreeIsing_Posterior_PlantedSymmetry`, `FreeIsing_Spectral_ColoredKoopman`, `FreeIsing_Spectral_DifferenceKoopman`, `FreeIsing_Stochastic_ContinuousCopyBrownian`, `FreeIsing_Stochastic_FiniteIsingBrownianEnergy`, `FreeIsing_Stochastic_PlantedBrownianLinearCombination`, `FreeIsing_Stochastic_WienerSampler`, `FreeIsing_Trees_BroadcastOutsideCone`, `FreeIsing_Trees_ColoredPathCount`, `FreeIsing_Trees_ColoredPathEndpoints`, `FreeIsing_Trees_ConnectedExhaustion`, `FreeIsing_Trees_ConnectedHull`, `FreeIsing_Trees_Escape`, `FreeIsing_Trees_FinitePathGibbs`, `FreeIsing_Trees_GibbsField`, `FreeIsing_Trees_IncidentEdges`, `FreeIsing_Trees_InfiniteCanonicalPathResponse`, `FreeIsing_Trees_PathCylinders`, `FreeIsing_Trees_PathResponse`.
--
--   **Imports.** It imports the published bundle `Def_FreeIsing`; the bundles `Q243FI000` and `Q243FI001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q243FI005`; the statements `OAI.Problem367.ComponentSignalAttenuation.condDistrib_posteriorMean_root`, `OAI.Problem367.ComponentSignalAttenuation.condExp_attenuation_le_critical_of_condIndep`, `OAI.Problem367.FiniteIsingFiltering.exists_innovation_integral_representation`, `OAI.Problem367.FiniteIsingFiltering.mean_compensatedSquare_martingale`, `OAI.Problem367.FiniteIsingFiltering.tendsto_cross_uniformSum`, `OAI.Problem367.IsingInnovation.exists_continuous_covariance_integral`, `OAI.Problem367.IsingInnovation.exists_continuous_posterior`, `OAI.Problem367.IsingInnovation.exists_posterior_integral_representation` and `OAI.Problem367.IsingInnovation.tendsto_trial_cross_uniformSum`; the proofs of `OAI.Problem367.BrownianArrayFiltration.compensatedSquare_of_spatial_integral_limits`, `OAI.Problem367.ComponentSignalAttenuation.condDistrib_posteriorMean_root`, `OAI.Problem367.ComponentSignalAttenuation.condExp_attenuation_le_critical_of_condIndep`, `OAI.Problem367.ConstructedArtanhFormula.exists_artanh_decomposition`, `OAI.Problem367.HasFreeIsingLaw.selectedPosterior_root_component`, `OAI.Problem367.HasFreeIsingLaw.selected_child_parent_abs_le`, `OAI.Problem367.HasFreeIsingLaw.selected_child_parent_secondMoment`, `OAI.Problem367.LocalizedArtanhFormula.exists_jointExit_artanh_decomposition` and `OAI.Problem367.free_ising_factor_iff_threshold`.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI000
import Definitions.Def_Q243FI001

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_InnovationMartingale
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.innovationPath_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

theorem nnrealTimePrimitive_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {m : ℝ≥0 → Ω → ℝ} {t : ℝ≥0}
    (hInt : Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))).prod P)) :
    Integrable (nnrealTimePrimitive m t) P := by
  change Integrable (fun ω => ∫ u in (0 : ℝ)..(t : ℝ), m u.toNNReal ω) P
  simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using hInt.integral_prod_right

theorem nnrealTimePrimitive_increment_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {m : ℝ≥0 → Ω → ℝ} {s t : ℝ≥0} (hst : s ≤ t)
    (h0s : Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) (s : ℝ))).prod P))
    (hstInt : Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))).prod P)) :
    nnrealTimePrimitive m t - nnrealTimePrimitive m s =ᵐ[P]
      fun ω => ∫ u in (s : ℝ)..(t : ℝ), m u.toNNReal ω := by
  filter_upwards [h0s.prod_left_ae, hstInt.prod_left_ae] with ω h0sω hstω
  have hi0s := (intervalIntegrable_iff_integrableOn_Ioc_of_le s.coe_nonneg).mpr h0sω
  have hist := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show (s : ℝ) ≤ (t : ℝ) from hst)).mpr hstω
  have h := intervalIntegral.integral_add_adjacent_intervals hi0s hist
  dsimp [nnrealTimePrimitive]
  linarith

theorem nnrealTimePrimitive_increment_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℝ≥0 mΩ) {m : ℝ≥0 → Ω → ℝ} (hm : Martingale m F P)
    {s t : ℝ≥0} (hst : s ≤ t)
    (h0s : Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) (s : ℝ))).prod P))
    (hstInt : Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))).prod P)) :
    P[nnrealTimePrimitive m t - nnrealTimePrimitive m s | F s] =ᵐ[P]
      fun ω => ((t : ℝ) - (s : ℝ)) * m s ω :=
  (condExp_congr_ae (nnrealTimePrimitive_increment_ae hst h0s hstInt)).trans
    (condExp_nnrealIntervalIntegral_martingale P F hm hst hstInt)

theorem compensated_observation_martingale_of_posterior_version
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ t, F t ≤ G t) (hσ : Integrable σ P)
    (hXad : StronglyAdapted F (fun t ω => B t ω + (t : ℝ) * σ ω))
    (hmAd : StronglyAdapted F m)
    (hposterior : ∀ t, m t =ᵐ[P] P[σ | F t])
    (hAad : StronglyAdapted F (nnrealTimePrimitive m))
    (hInt : ∀ s t : ℝ≥0, s ≤ t →
      Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
        ((volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))).prod P)) :
    Martingale (fun t ω => B t ω + (t : ℝ) * σ ω -
      nnrealTimePrimitive m t ω) F P := by
  let X : ℝ≥0 → Ω → ℝ := fun t ω => B t ω + (t : ℝ) * σ ω
  let A := nnrealTimePrimitive m
  have hXint (t : ℝ≥0) : Integrable (X t) P :=
    (hB.integrable t).add (hσ.const_mul (t : ℝ))
  have hAint (t : ℝ≥0) : Integrable (A t) P :=
    nnrealTimePrimitive_integrable (hInt 0 t (by positivity))
  apply martingale_of_conditional_increment_zero (hXad.sub hAad)
    (fun t => (hXint t).sub (hAint t))
  intro s t hst
  have hXce := observation_increment_condExp hB hFG hσ hst
  have hm : Martingale m F P := (martingale_condExp σ F P).congr hmAd
    (fun t => (hposterior t).symm)
  have hAce := nnrealTimePrimitive_increment_condExp P F hm hst
    (hInt 0 s (by positivity)) (hInt s t hst)
  have hfun :
      ((fun ω => X t ω - A t ω) - (fun ω => X s ω - A s ω)) =
      (X t - X s) - (A t - A s) := by
    funext ω
    simp only [Pi.sub_apply]
    ring
  change P[(fun ω => X t ω - A t ω) - (fun ω => X s ω - A s ω) | F s] =ᵐ[P] _
  rw [hfun]
  have hd := condExp_sub ((hXint t).sub (hXint s)) ((hAint t).sub (hAint s)) (F s)
  filter_upwards [hd, hXce, hAce, hposterior s] with ω hd hx ha hmω
  change P[X t - X s | F s] ω = ((t : ℝ) - (s : ℝ)) * P[σ | F s] ω at hx
  change P[A t - A s | F s] ω = ((t : ℝ) - (s : ℝ)) * m s ω at ha
  rw [hmω] at ha
  simpa only [Pi.sub_apply, hx, ha, sub_self] using hd

end Problem367

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

lemma indepFun_pi_of_coordinate_indepFun
    {ι Omega E F : Type*} [Fintype ι] [MeasurableSpace Omega]
    [MeasurableSpace E] [MeasurableSpace F]
    (mu : ι → Measure Omega) [∀ i, IsProbabilityMeasure (mu i)]
    {f : ι → Omega → E} {g : ι → Omega → F}
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hfg : ∀ i, IndepFun (f i) (g i) (mu i)) :
    IndepFun (fun w : ι → Omega => fun i => f i (w i))
      (fun w => fun i => g i (w i)) (Measure.pi mu) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (Measurable.of_eval (fun index => (hf index).comp (measurable_pi_apply index))).aemeasurable
    (Measurable.of_eval (fun index => (hg index).comp (measurable_pi_apply index))).aemeasurable).2
  simp only [Function.comp_def]
  rw [Measure.pi_map_pi (fun i => (hf i).aemeasurable),
    Measure.pi_map_pi (fun i => (hg i).aemeasurable)]
  calc
    _ = ((Measure.pi mu).map (fun w i => (f i (w i), g i (w i)))).map
        (MeasurableEquiv.arrowProdEquivProdArrow E F ι) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (Measure.pi (fun i => (mu i).map (fun w => (f i w, g i w)))).map
        (MeasurableEquiv.arrowProdEquivProdArrow E F ι) := by
      rw [Measure.pi_map_pi (fun i => ((hf i).prodMk (hg i)).aemeasurable)]
    _ = (Measure.pi (fun i => ((mu i).map (f i)).prod ((mu i).map (g i)))).map
        (MeasurableEquiv.arrowProdEquivProdArrow E F ι) := by
      congr 2
      funext i
      exact (hfg i).map_prod_eq_prod_map_map (hf i).aemeasurable (hg i).aemeasurable
    _ = _ := (measurePreserving_arrowProdEquivProdArrow E F ι
      (fun i => (mu i).map (f i)) (fun i => (mu i).map (g i))).map_eq

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PlantedBridgeInfinite
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

lemma indepFun_infinitePi_of_coordinate_indepFun
    {ι Omega E F : Type*} [MeasurableSpace Omega]
    [MeasurableSpace E] [MeasurableSpace F]
    (mu : ι → Measure Omega) [∀ i, IsProbabilityMeasure (mu i)]
    {f : ι → Omega → E} {g : ι → Omega → F}
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hfg : ∀ i, IndepFun (f i) (g i) (mu i)) :
    IndepFun (fun w : ι → Omega => fun i => f i (w i))
      (fun w => fun i => g i (w i)) (Measure.infinitePi mu) := by
  classical
  apply IndepFun.process_indepFun_process
    (fun i => (hf i).comp (measurable_pi_apply i))
    (fun i => (hg i).comp (measurable_pi_apply i))
  intro I J
  let K := I ∪ J
  have hi := indepFun_pi_of_coordinate_indepFun (fun i : K => mu i)
    (fun i => hf i) (fun i => hg i) (fun i => hfg i)
  have hr : MeasurePreserving (K.restrict : (ι → Omega) → K → Omega)
      (Measure.infinitePi mu) (Measure.pi fun i : K => mu i) :=
    ⟨by fun_prop, Measure.infinitePi_map_restrict mu⟩
  have hp := indepFun_comp_measurePreserving hr
    (Measurable.of_eval (fun index : K => (hf index).comp (measurable_pi_apply index)))
    (Measurable.of_eval (fun index : K => (hg index).comp (measurable_pi_apply index))) hi
  let eI : I → K := fun i => ⟨i, Finset.mem_union_left J i.property⟩
  let eJ : J → K := fun j => ⟨j, Finset.mem_union_right I j.property⟩
  have h := hp.comp
    (by fun_prop : Measurable (fun x : K → E => fun i : I => x (eI i)))
    (by fun_prop : Measurable (fun x : K → F => fun j : J => x (eJ j)))
  simpa only [Function.comp_def, Finset.restrict, eI, eJ] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ArrayObservation
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

lemma arrayNaturalFiltration_eq_comap {ι Ω : Type*} [MeasurableSpace Ω]
    (X : ι → ℝ≥0 → Ω → ℝ) (hm : ∀ i t, Measurable (X i t)) (t : ℝ≥0) :
    arrayNaturalFiltration X hm t =
      MeasurableSpace.comap (fun ω i (s : Set.Iic t) => X i s ω) inferInstance := by
  simp only [arrayNaturalFiltration, MeasurableSpace.comap_process_pi,
    Filtration.natural_eq_comap]

lemma arrayNaturalFiltration_le {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    (X : ι → ℝ≥0 → Ω → ℝ) (hm : ∀ i t, Measurable (X i t))
    {F : Filtration ℝ≥0 mΩ} (had : ∀ i, StronglyAdapted F (X i)) :
    arrayNaturalFiltration X hm ≤ F := by
  intro t
  exact iSup_le fun i => naturalFiltration_le_of_stronglyAdapted
    (fun t => (hm i t).stronglyMeasurable) (had i) t

def signalArrayFiltration {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t)) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (S × (ι → Ω))) :=
  Filtration.const ℝ≥0 (MeasurableSpace.comap Prod.fst inferInstance)
    measurable_fst.comap_le ⊔
    arrayNaturalFiltration (fun i t (q : S × (ι → Ω)) => B i t (q.2 i))
      (fun i t => (hmB i t).comp ((measurable_pi_apply i).comp measurable_snd))

lemma signalArrayFiltration_eq_comap {ι S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) :
    signalArrayFiltration (S := S) B hmB t =
      MeasurableSpace.comap
        (fun q : S × (ι → Ω) => (q.1, fun i (s : Set.Iic t) => B i s (q.2 i)))
        inferInstance := by
  change MeasurableSpace.comap Prod.fst inferInstance ⊔
    arrayNaturalFiltration _ _ t = _
  rw [arrayNaturalFiltration_eq_comap]
  exact (MeasurableSpace.comap_prodMk Prod.fst
    (fun q : S × (ι → Ω) => fun i (s : Set.Iic t) => B i s (q.2 i))).symm

theorem planted_array_increments_indep_signal_past
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) {s t : ℝ≥0} (hst : s ≤ t) :
    IndepFun
      (fun q : S × (ι → Ω) => fun i => B i t (q.2 i) - B i s (q.2 i))
      (fun q : S × (ι → Ω) => (q.1, fun i (u : Set.Iic s) => B i u (q.2 i)))
      (ν.prod (Measure.infinitePi μ)) := by
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hmPast (i : ι) : Measurable (fun ω (u : Set.Iic s) => B i u ω) :=
    Measurable.of_eval fun u => hmB i u
  have hmInc (i : ι) : Measurable (fun ω => B i t ω - B i s ω) :=
    (hmB i t).sub (hmB i s)
  have hind := indepFun_infinitePi_of_coordinate_indepFun μ hmPast hmInc
    (fun i => (preBrownian_increment_indep_past (hB i) hst).symm)
  exact (indepFun_prod_left_of_indepFun ν (Measure.infinitePi μ)
    (Measurable.of_eval fun i => (hmPast i).comp (measurable_pi_apply i))
    (Measurable.of_eval fun i => (hmInc i).comp (measurable_pi_apply i)) hind).symm

theorem preBrownian_martingale_signalArrayFiltration
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) (i : ι) :
    Martingale (fun t (q : S × (ι → Ω)) => B i t (q.2 i))
      (signalArrayFiltration B hmB) (ν.prod (Measure.infinitePi μ)) := by
  have (j : ι) : IsProbabilityMeasure (μ j) :=
    (hB j).isGaussianProcess.isProbabilityMeasure
  let P := ν.prod (Measure.infinitePi μ)
  let F := signalArrayFiltration (S := S) B hmB
  have hproj := planted_noise_coordinate_measurePreserving ν μ i
  have hint (t : ℝ≥0) : Integrable (fun q : S × (ι → Ω) => B i t (q.2 i)) P :=
    hproj.integrable_comp_of_integrable ((hB i).integrable_eval t)
  have had : StronglyAdapted F (fun t (q : S × (ι → Ω)) => B i t (q.2 i)) := by
    intro t
    exact (arrayNaturalFiltration_stronglyAdapted
      (fun j u (q : S × (ι → Ω)) => B j u (q.2 j))
      (fun j u => (hmB j u).comp ((measurable_pi_apply j).comp measurable_snd)) i t).mono
      le_sup_right
  apply martingale_of_conditional_increment_zero had hint
  intro s t hst
  have hind := (planted_array_increments_indep_signal_past ν μ hB hmB hst).comp
    (measurable_pi_apply i) measurable_id
  have hn := signalArrayFiltration_eq_comap (S := S) B hmB s
  have hcond : P[(fun q : S × (ι → Ω) => B i t (q.2 i) - B i s (q.2 i)) | F s] =ᵐ[P]
      fun _ => ∫ q : S × (ι → Ω), B i t (q.2 i) - B i s (q.2 i) ∂P := by
    change P[_ | signalArrayFiltration B hmB s] =ᵐ[P] _
    rw [hn]
    exact condExp_indep_eq
      (((hmB i t).sub (hmB i s)).comp hproj.measurable).comap_le
      (hn ▸ F.le s) (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable hind
  have hzero : (∫ q : S × (ι → Ω), B i t (q.2 i) - B i s (q.2 i) ∂P) = 0 := by
    have hi := integral_map (μ := P) hproj.measurable.aemeasurable
      (((hmB i t).sub (hmB i s)).aestronglyMeasurable)
    rw [hproj.map_eq] at hi
    simp only [Pi.sub_apply] at hi
    rw [← hi, integral_sub ((hB i).integrable_eval t) ((hB i).integrable_eval s),
      (hB i).integral_eval, (hB i).integral_eval, sub_self]
  simpa only [hzero, Pi.sub_def] using hcond

lemma arrayObservationFiltration_le_signalArrayFiltration {ι S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (σ : S → ι → ℝ) (hσ : Measurable σ) :
    arrayObservationFiltration B hmB σ hσ ≤ signalArrayFiltration B hmB := by
  apply arrayNaturalFiltration_le
  intro i t
  have hnoise : StronglyMeasurable[signalArrayFiltration (S := S) B hmB t]
      (fun q : S × (ι → Ω) => B i t (q.2 i)) :=
    (arrayNaturalFiltration_stronglyAdapted
      (fun j u (q : S × (ι → Ω)) => B j u (q.2 j))
      (fun j u => (hmB j u).comp ((measurable_pi_apply j).comp measurable_snd)) i t).mono
      le_sup_right
  have hsignal : StronglyMeasurable[MeasurableSpace.comap
      (Prod.fst : S × (ι → Ω) → S) inferInstance]
      (fun q : S × (ι → Ω) => σ q.1 i) :=
    (((measurable_pi_apply i).comp hσ).comp (comap_measurable Prod.fst)).stronglyMeasurable
  exact hnoise.add (stronglyMeasurable_const.mul (hsignal.mono le_sup_left))

theorem preBrownian_array_observation_innovation_martingale
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ) (i : ι)
    (hσint : Integrable (fun s => σ s i) ν)
    {m : ℝ≥0 → S × (ι → Ω) → ℝ}
    (hmAd : StronglyAdapted (arrayObservationFiltration B hmB σ hσ) m)
    (hposterior : ∀ t, m t =ᵐ[ν.prod (Measure.infinitePi μ)]
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ t])
    (hAad : StronglyAdapted (arrayObservationFiltration B hmB σ hσ)
      (nnrealTimePrimitive m))
    (hInt : ∀ s t : ℝ≥0, s ≤ t →
      Integrable (fun p : ℝ × (S × (ι → Ω)) => m p.1.toNNReal p.2)
        ((volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))).prod
          (ν.prod (Measure.infinitePi μ)))) :
    Martingale
      (fun t q => plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q)
      (arrayObservationFiltration B hmB σ hσ) (ν.prod (Measure.infinitePi μ)) := by
  have (j : ι) : IsProbabilityMeasure (μ j) :=
    (hB j).isGaussianProcess.isProbabilityMeasure
  exact compensated_observation_martingale_of_posterior_version
    (preBrownian_martingale_signalArrayFiltration ν μ hB hmB i)
    (arrayObservationFiltration_le_signalArrayFiltration B hmB σ hσ)
    (hσint.comp_fst (Measure.infinitePi μ))
    (arrayNaturalFiltration_stronglyAdapted (plantedArrayObservation B σ)
      (plantedArrayObservation_measurable hmB hσ) i)
    hmAd hposterior hAad hInt

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ArrayMoments
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

theorem planted_weighted_increment_integral_sq
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) {s t : ℝ≥0} (hst : s ≤ t)
    (I : Finset ι) (a : ι → ℝ) :
    (∫ q : S × (ι → Ω),
      (∑ i ∈ I, a i * (B i t (q.2 i) - B i s (q.2 i))) ^ 2
        ∂ν.prod (Measure.infinitePi μ)) =
      ((t : ℝ) - (s : ℝ)) * ∑ i ∈ I, a i ^ 2 := by
  classical
  have (k : ι) : IsProbabilityMeasure (μ k) :=
    (hB k).isGaussianProcess.isProbabilityMeasure
  let P := ν.prod (Measure.infinitePi μ)
  let D : ι → S × (ι → Ω) → ℝ := fun i q => B i t (q.2 i) - B i s (q.2 i)
  have hC (i : ι) := planted_coordinate_preBrownian ν μ hB i
  have hD2 (i : ι) : MemLp (D i) 2 P :=
    ((hC i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two.sub
      ((hC i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hY2 (i : ι) : MemLp (fun q => a i * D i q) 2 P := (hD2 i).const_mul (a i)
  have hzero (i : ι) : (∫ q, D i q ∂P) = 0 := by
    change (∫ q : S × (ι → Ω), B i t (q.2 i) - B i s (q.2 i) ∂P) = 0
    rw [integral_sub ((hC i).integrable_eval t) ((hC i).integrable_eval s),
      (hC i).integral_eval, (hC i).integral_eval, sub_self]
  have hsq (i : ι) : (∫ q, D i q ^ 2 ∂P) = (t : ℝ) - (s : ℝ) := by
    have h := preBrownian_integral_sq ((hC i).shift s) (t - s)
    simpa only [D, add_tsub_cancel_of_le hst, NNReal.coe_sub hst] using h
  have horth (i : ι) (_hi : i ∈ I) (j : ι) (_hj : j ∈ I) (hij : i ≠ j) :
      (∫ q, (a i * D i q) * (a j * D j q) ∂P) = 0 := by
    have hind := (planted_coordinate_increments_indep ν μ hB hmB s t hij).comp
      (measurable_id.const_mul (a i)) (measurable_id.const_mul (a j))
    have heq := hind.integral_mul_eq_mul_integral
      (hY2 i).aestronglyMeasurable (hY2 j).aestronglyMeasurable
    change (∫ q, (a i * D i q) * (a j * D j q) ∂P) =
      (∫ q, a i * D i q ∂P) * (∫ q, a j * D j q ∂P) at heq
    simpa only [integral_const_mul, hzero, mul_zero, zero_mul] using heq
  rw [SimpleIntegral.integral_sq_sum_of_orthogonal I (fun i q => a i * D i q)
    (fun i _ j _ => (hY2 i).integrable_mul (hY2 j)) horth]
  simp only [mul_pow, integral_const_mul, hsq]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem planted_weighted_increment_sq_condExp
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) {s t : ℝ≥0} (hst : s ≤ t)
    (I : Finset ι) (a : ι → ℝ) :
    (ν.prod (Measure.infinitePi μ))[
      (fun q : S × (ι → Ω) =>
        (∑ i ∈ I, a i * (B i t (q.2 i) - B i s (q.2 i))) ^ 2) |
      signalArrayFiltration B hmB s] =ᵐ[ν.prod (Measure.infinitePi μ)]
        fun _ => ((t : ℝ) - (s : ℝ)) * ∑ i ∈ I, a i ^ 2 := by
  classical
  have (k : ι) : IsProbabilityMeasure (μ k) :=
    (hB k).isGaussianProcess.isProbabilityMeasure
  have hm : Measurable (fun x : ι → ℝ => (∑ i ∈ I, a i * x i) ^ 2) := by
    fun_prop
  have hind := (planted_array_increments_indep_signal_past ν μ hB hmB hst).comp
    hm measurable_id
  have hf : Measurable (fun q : S × (ι → Ω) =>
      (∑ i ∈ I, a i * (B i t (q.2 i) - B i s (q.2 i))) ^ 2) := by
    apply hm.comp
    exact Measurable.of_eval fun i =>
      ((hmB i t).sub (hmB i s)).comp ((measurable_pi_apply i).comp measurable_snd)
  have hn := signalArrayFiltration_eq_comap (S := S) B hmB s
  have hc := condExp_indep_eq hf.comap_le
    (hn ▸ (signalArrayFiltration (S := S) B hmB).le s)
    (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable hind
  simp only [Function.id_comp] at hc
  rw [← hn] at hc
  simpa only [Function.comp_def, id_eq,
    planted_weighted_increment_integral_sq ν μ hB hmB hst I a] using hc

theorem planted_weighted_increment_sq_condExp_subfield
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) {s t : ℝ≥0} (hst : s ≤ t)
    (I : Finset ι) (a : ι → ℝ)
    {m : MeasurableSpace (S × (ι → Ω))} (hm : m ≤ signalArrayFiltration B hmB s) :
    (ν.prod (Measure.infinitePi μ))[
      (fun q : S × (ι → Ω) =>
        (∑ i ∈ I, a i * (B i t (q.2 i) - B i s (q.2 i))) ^ 2) | m]
      =ᵐ[ν.prod (Measure.infinitePi μ)]
        fun _ => ((t : ℝ) - (s : ℝ)) * ∑ i ∈ I, a i ^ 2 := by
  have (k : ι) : IsProbabilityMeasure (μ k) :=
    (hB k).isGaussianProcess.isProbabilityMeasure
  exact ((condExp_condExp_of_le hm (signalArrayFiltration (S := S) B hmB |>.le s)).symm.trans
    (condExp_congr_ae (planted_weighted_increment_sq_condExp ν μ hB hmB hst I a))).trans
      (Filter.EventuallyEq.of_eq (condExp_const (hm.trans
        (signalArrayFiltration (S := S) B hmB |>.le s)) _))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Characteristic
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
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

theorem map_restrict_eq_smul_of_condExp_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable[mΩ] X)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hchar : ∀ t : ℝ, P[character X t | m] =ᵐ[P] fun _ => charFun ν t)
    {s : Set Ω} (hs : MeasurableSet[m] s) :
    Measure.map X (P.restrict s) = P s • ν := by
  let : IsFiniteMeasure (P s • ν) := ν.smul_finite (measure_ne_top P s)
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply_real, integral_map hX.aemeasurable (by fun_prop),
    charFun_apply_real, integral_smul_measure]
  change (∫ ω in s, character X t ω ∂P) = _
  rw [← setIntegral_condExp hm (integrable_character hX t) hs]
  calc
    (∫ ω in s, P[character X t | m] ω ∂P) =
        ∫ _ in s, charFun ν t ∂P :=
      integral_congr_ae (ae_restrict_of_ae (hchar t))
    _ = _ := by simp [charFun_apply_real, measureReal_def]

theorem map_eq_of_condExp_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable[mΩ] X)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hchar : ∀ t : ℝ, P[character X t | m] =ᵐ[P] fun _ => charFun ν t) :
    Measure.map X P = ν := by
  simpa using map_restrict_eq_smul_of_condExp_character hm hX ν hchar
    (MeasurableSet.univ : MeasurableSet[m] Set.univ)

theorem indepFun_of_condExp_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable[mΩ] X)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hchar : ∀ t : ℝ, P[character X t | m] =ᵐ[P] fun _ => charFun ν t)
    {E : Type*} [MeasurableSpace E] {Y : Ω → E} (hY : Measurable[m] Y) :
    IndepFun X Y P := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro a b ha hb
  have hrestrict := congrArg (fun μ : Measure ℝ => μ a)
    (map_restrict_eq_smul_of_condExp_character hm hX ν hchar (hY hb))
  have hlaw := map_eq_of_condExp_character hm hX ν hchar
  rw [Measure.map_apply hX ha, Measure.restrict_apply (hX ha),
    Measure.smul_apply, smul_eq_mul, ← hlaw, Measure.map_apply hX ha] at hrestrict
  exact hrestrict.trans (mul_comm _ _)

theorem hasLaw_of_condExp_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable[mΩ] X)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hchar : ∀ t : ℝ, P[character X t | m] =ᵐ[P] fun _ => charFun ν t) :
    HasLaw X ν P :=
  ⟨hX.aemeasurable, map_eq_of_condExp_character hm hX ν hchar⟩

end Problem367.ConditionalCharacteristic

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_Characterization
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
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

theorem isPreBrownianReal_of_conditional_charFun
    {B : ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : StronglyAdapted F B) (hzero : ∀ᵐ ω ∂μ, B 0 ω = 0)
    (hchar : ∀ s t : ℝ≥0, s ≤ t → ∀ u : ℝ,
      μ[character (fun ω => B t ω - B s ω) u | F s]
        =ᵐ[μ] fun _ => charFun (gaussianReal 0 (t - s)) u) :
    IsPreBrownianReal B μ := by
  have hm (t : ℝ≥0) : Measurable (B t) := ((hB t).mono (F.le t)).measurable
  have hlaw (s t : ℝ≥0) (hst : s ≤ t) :
      HasLaw (fun ω => B t ω - B s ω) (gaussianReal 0 (t - s)) μ :=
    hasLaw_of_condExp_character (F.le s) ((hm t).sub (hm s)) _ (hchar s t hst)
  apply HasIndepIncrements.isPreBrownianReal_of_hasLaw
  · intro t
    have h := hlaw 0 t (by positivity)
    simp only [tsub_zero] at h
    apply h.congr
    filter_upwards [hzero] with ω hω
    simp [hω]
  · apply hasIndepIncrements_of_past_events F hB
    intro s t hst A hA S hS
    have hmap := map_restrict_eq_smul_of_condExp_character (F.le s)
      ((hm t).sub (hm s)) (gaussianReal 0 (t - s)) (hchar s t hst) hA
    have h := congrArg (fun κ : Measure ℝ => κ S) hmap
    rw [Measure.map_apply ((hm t).sub (hm s)) hS,
      Measure.restrict_apply (((hm t).sub (hm s)) hS),
      Measure.smul_apply, smul_eq_mul] at h
    have hmass : μ ((fun ω => B t ω - B s ω) ⁻¹' S) = gaussianReal 0 (t - s) S := by
      rw [← (hlaw s t hst).map_eq]
      exact (Measure.map_apply (show Measurable (fun ω => B t ω - B s ω) from
        (hm t).sub (hm s)) hS).symm
    rw [hmass, Set.inter_comm]
    exact h

theorem isPreBrownianReal_of_conditional_exponential
    {B : ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : StronglyAdapted F B) (hzero : ∀ᵐ ω ∂μ, B 0 ω = 0)
    (hchar : ∀ s t : ℝ≥0, s ≤ t → ∀ u : ℝ,
      μ[character (fun ω => B t ω - B s ω) u | F s] =ᵐ[μ]
        fun _ => Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * (u : ℂ)^2 / 2)) :
    IsPreBrownianReal B μ := by
  apply isPreBrownianReal_of_conditional_charFun F hB hzero
  intro s t hst u
  simpa only [charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul,
    zero_sub, neg_mul, neg_div] using hchar s t hst u

theorem isPreBrownianReal_of_setIntegral_character
    {B : ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : StronglyAdapted F B) (hzero : ∀ᵐ ω ∂μ, B 0 ω = 0)
    (hchar : ∀ s t : ℝ≥0, s ≤ t → ∀ A : Set Ω, MeasurableSet[F s] A →
      ∀ u : ℝ, (∫ ω in A, character (fun ω => B t ω - B s ω) u ω ∂μ) =
        μ.real A * Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * (u : ℂ)^2 / 2)) :
    IsPreBrownianReal B μ := by
  apply isPreBrownianReal_of_conditional_exponential F hB hzero
  intro s t hst u
  exact condExp_character_of_setIntegral (F.le s)
    (((hB t).mono (F.le t)).measurable.sub ((hB s).mono (F.le s)).measurable)
    _ u (fun A hA => hchar s t hst A hA u)

end Problem367.BrownianCharacterization

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

theorem tendsto_sum_brownian_drift_errors
    {ι : Type*} {l : Filter ι}
    (dt : ι → ℕ → ℝ) (N : ι → ℕ) (mesh : ι → ℝ)
    {T A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hdt : ∀ i k, k < N i → 0 ≤ dt i k)
    (hmesh : ∀ i k, k < N i → dt i k ≤ mesh i)
    (htotal : ∀ i, ∑ k ∈ Finset.range (N i), dt i k = T)
    (hlim : Tendsto mesh l (𝓝 0)) :
    Tendsto (fun i => ∑ k ∈ Finset.range (N i),
      (A * (dt i k * Real.sqrt (dt i k)) + B * (dt i k) ^ 2 + C * (dt i k) ^ 3))
      l (𝓝 0) := by
  have hupper (i) : (∑ k ∈ Finset.range (N i),
      (A * (dt i k * Real.sqrt (dt i k)) + B * (dt i k) ^ 2 + C * (dt i k) ^ 3)) ≤
      A * (T * Real.sqrt (mesh i)) + B * (T * mesh i) + C * (T * (mesh i) ^ 2) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    apply add_le_add
    · apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (by simpa only [htotal i] using (sum_mul_sqrt_le_total_mul_sqrt_mesh
            (dt i) (N i) (hdt i) (hmesh i))) hA
      · exact mul_le_mul_of_nonneg_left
          (by simpa only [htotal i] using (sum_sq_le_total_mul_mesh
            (dt i) (N i) (hdt i) (hmesh i))) hB
    · exact mul_le_mul_of_nonneg_left
        (by simpa only [htotal i] using (sum_cube_le_total_mul_mesh_sq
          (dt i) (N i) (hdt i) (hmesh i))) hC
  have hright : Tendsto (fun i => A * (T * Real.sqrt (mesh i)) +
      B * (T * mesh i) + C * (T * (mesh i) ^ 2)) l (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] using
      (((Real.continuous_sqrt.tendsto 0).comp hlim).const_mul T |>.const_mul A).add
        ((hlim.const_mul T).const_mul B) |>.add (((hlim.pow 2).const_mul T).const_mul C)
  apply squeeze_zero (fun i => ?_) hupper hright
  apply Finset.sum_nonneg
  intro k hk
  have := hdt i k (Finset.mem_range.mp hk)
  positivity

theorem eq_gaussian_mul_of_local_error
    (z : ℝ → ℂ) {c T A B C : ℝ}
    (hc : 0 ≤ c) (hT : 0 ≤ T)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hstep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      ‖z t - Complex.exp ((-c * (t - s) : ℝ) : ℂ) * z s‖ ≤
        A * ((t - s) * Real.sqrt (t - s)) + B * (t - s) ^ 2 + C * (t - s) ^ 3) :
    z T = Complex.exp ((-c * T : ℝ) : ℂ) * z 0 := by
  let mesh : ℕ → ℝ := fun n => T / ((n : ℝ) + 1)
  let grid : ℕ → ℕ → ℝ := fun n k => (k : ℝ) * mesh n
  let e : ℕ → ℕ → ℝ := fun n _ =>
    A * (mesh n * Real.sqrt (mesh n)) + B * (mesh n) ^ 2 + C * (mesh n) ^ 3
  have hm (n : ℕ) : 0 ≤ mesh n := by dsimp [mesh] <;> positivity
  have htotal (n : ℕ) : (∑ _k ∈ Finset.range (n + 1), mesh n) = T := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    dsimp [mesh]
    field_simp
  have hmeshlim : Tendsto mesh atTop (𝓝 0) := by
    simpa only [mesh, div_eq_mul_inv, one_div, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul T
  have herrlim : Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), e n k) atTop (𝓝 0) :=
    tendsto_sum_brownian_drift_errors (fun n _ => mesh n) (fun n => n + 1) mesh
      hA hB hC (fun n _ _ => hm n) (fun _ _ _ => le_rfl) htotal hmeshlim
  apply eq_gaussian_mul_of_recurrence_errors_tendsto_zero
    (fun n k => z (grid n k)) (fun n _ => mesh n) e (fun n => n + 1) hc
    (fun n _ _ => hm n) htotal (fun n => by simp [grid])
    (fun n => ?_) (fun n k hk => ?_) herrlim
  · congr 1
    dsimp [grid, mesh]
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  · have hkn : (k : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast (Nat.succ_le_of_lt hk)
    have hstart : 0 ≤ grid n k := mul_nonneg (Nat.cast_nonneg k) (hm n)
    have hdiff : grid n (k + 1) - grid n k = mesh n := by
      simp only [grid, Nat.cast_add, Nat.cast_one]
      ring
    have horder : grid n k ≤ grid n (k + 1) := by linarith [hm n]
    have hend : grid n (k + 1) ≤ T := by
      calc
        grid n (k + 1) = ((k : ℝ) + 1) * mesh n := by simp [grid]
        _ ≤ ((n : ℝ) + 1) * mesh n := mul_le_mul_of_nonneg_right hkn (hm n)
        _ = T := by dsimp [mesh]; field_simp
    simpa only [hdiff, e] using hstep (grid n k) (grid n (k + 1)) hstart horder hend

end Problem367.ExponentialTaylor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_GaussianCriterion
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

theorem integral_complex_test_martingale_increment_eq_zero
    {Ω ι : Type*} [Preorder ι] [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {W : ι → Ω → ℝ} (hW : Martingale W F P)
    {s t : ι} (hst : s ≤ t) {Z : Ω → ℂ}
    (hZ : StronglyMeasurable[F s] Z) (hbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1) :
    (∫ ω, Z ω * ((W t ω - W s ω : ℝ) : ℂ) ∂P) = 0 := by
  have hi := InnovationConditionalMoments.integral_smul_eq_integral_condExp_smul
    (F.le s) ((hW.integrable t).sub (hW.integrable s)) hZ hbound
  have hz := martingale_increment_condExp_subfiltration hW (fun _ => le_rfl) hst
  have he : (∫ ω, (W t ω - W s ω) • Z ω ∂P) = 0 := by
    change (∫ ω, (W t - W s) ω • Z ω ∂P) = 0
    rw [hi]
    calc
      _ = ∫ _ω : Ω, (0 : ℂ) ∂P := by
        apply integral_congr_ae
        filter_upwards [hz] with ω hω
        rw [hω, zero_smul]
      _ = 0 := by simp
  simpa only [Complex.real_smul, mul_comm] using he

theorem integral_characteristic_eq_gaussian_of_martingale_moments_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} (hW : Martingale W F P) (q : ℝ) (hq : 0 ≤ q)
    {M : ℝ} (hM : 0 ≤ M)
    (hD2 : ∀ a b : ℝ≥0, a ≤ b →
      Integrable (fun ω => (W b ω - W a ω) ^ 2) P)
    (hD3 : ∀ a b : ℝ≥0, a ≤ b →
      Integrable (fun ω => |W b ω - W a ω| ^ 3) P)
    (hthird : ∀ a b : ℝ≥0, a ≤ b →
      (∫ ω, |W b ω - W a ω| ^ 3 ∂P) ≤
        M * (((b : ℝ) - a) * Real.sqrt ((b : ℝ) - a) + ((b : ℝ) - a) ^ 3))
    (hvariance : ∀ a b : ℝ≥0, a ≤ b → ∀ Y : Ω → ℂ,
      StronglyMeasurable[F a] Y → (∀ᵐ ω ∂P, ‖Y ω‖ ≤ 1) →
      ‖∫ ω, Y ω * (((W b ω - W a ω : ℝ) : ℂ) ^ 2 - ((q * ((b : ℝ) - (a : ℝ)) : ℝ) : ℂ)) ∂P‖ ≤
        M * (((b : ℝ) - a) * Real.sqrt ((b : ℝ) - a) + ((b : ℝ) - a) ^ 2))
    (s T : ℝ≥0) (u : ℝ) (Z : Ω → ℂ)
    (hZ : StronglyMeasurable[F s] Z) (hbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1) :
    (∫ ω, Z ω * Complex.exp (((u * (W (s + T) ω - W s ω) : ℝ) : ℂ) * Complex.I) ∂P) =
      Complex.exp ((-(u ^ 2 / 2 * q) * (T : ℝ) : ℝ) : ℂ) * ∫ ω, Z ω ∂P := by
  let z : ℝ → ℂ := fun r => ∫ ω, Z ω *
    Complex.exp (((u * (W (s + r.toNNReal) ω - W s ω) : ℝ) : ℂ) * Complex.I) ∂P
  have hz0 : z 0 = ∫ ω, Z ω ∂P := by simp [z]
  have hzT : z (T : ℝ) = ∫ ω, Z ω *
      Complex.exp (((u * (W (s + T) ω - W s ω) : ℝ) : ℂ) * Complex.I) ∂P := by simp [z]
  have hfinal := ExponentialTaylor.eq_gaussian_mul_of_local_error z
    (c := u ^ 2 / 2 * q) (T := (T : ℝ))
    (A := (4 * |u| ^ 3 + u ^ 2 / 2) * M)
    (B := u ^ 2 / 2 * M + u ^ 4 * q ^ 2 / 4) (C := 4 * |u| ^ 3 * M)
    (by positivity) T.coe_nonneg (by positivity) (by positivity) (by positivity) ?_
  · simpa only [hz0, hzT] using hfinal
  intro a b ha hab hb
  let ta : ℝ≥0 := s + a.toNNReal
  let tb : ℝ≥0 := s + b.toNNReal
  have hb0 : 0 ≤ b := ha.trans hab
  have hst : s ≤ ta := le_add_of_nonneg_right (bot_le : 0 ≤ a.toNNReal)
  have hatb : ta ≤ tb := add_le_add le_rfl (Real.toNNReal_mono hab)
  have hreal : (ta : ℝ) ≤ (tb : ℝ) := hatb
  have hdiff : (tb : ℝ) - ta = b - a := by
    simp [ta, tb, Real.toNNReal_of_nonneg ha, Real.toNNReal_of_nonneg hb0]
  let Y : Ω → ℂ := fun ω => Z ω *
    Complex.exp (((u * (W ta ω - W s ω) : ℝ) : ℂ) * Complex.I)
  have hYm : StronglyMeasurable[F ta] Y := by
    let : MeasurableSpace Ω := F ta
    have hZm : Measurable Z := (hZ.mono (F.mono hst)).measurable
    have hWam : Measurable (W ta) := (hW.stronglyMeasurable ta).measurable
    have hWsm : Measurable (W s) := ((hW.stronglyMeasurable s).mono (F.mono hst)).measurable
    apply Measurable.stronglyMeasurable
    dsimp [Y]
    fun_prop
  have hYbound : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ 1 := by
    filter_upwards [hbound] with ω hω
    simpa only [Y, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using hω
  have hstep := norm_integral_weighted_characteristic_gaussian_step_all_mul P Y
    (fun ω => W tb ω - W ta ω) u (v := q * ((tb : ℝ) - (ta : ℝ))) (mul_nonneg hq (sub_nonneg.mpr hreal))
    ((hYm.mono (F.le ta)).aestronglyMeasurable) hYbound
    (((hW.stronglyMeasurable tb).mono (F.le tb)).measurable.sub
      (((hW.stronglyMeasurable ta).mono (F.le ta)).measurable))
    ((hW.integrable tb).sub (hW.integrable ta)) (hD2 ta tb hatb) (hD3 ta tb hatb)
    (integral_complex_test_martingale_increment_eq_zero P hW hatb hYm hYbound)
  have hphase : (∫ ω, Y ω *
      Complex.exp (((u * (W tb ω - W ta ω) : ℝ) : ℂ) * Complex.I) ∂P) = z b :=
    integral_phase_increment_identity P Z (W s) (W ta) (W tb) u
  have hya : (∫ ω, Y ω ∂P) = z a := rfl
  rw [hphase, hya, hdiff] at hstep
  have hexp : -((u ^ 2 * (q * (b - a)) : ℝ) : ℂ) / 2 =
      ((-(u ^ 2 / 2 * q) * (b - a) : ℝ) : ℂ) := by push_cast <;> ring
  rw [hexp] at hstep
  apply hstep.trans
  have ht := hthird ta tb hatb
  have hv := hvariance ta tb hatb Y hYm hYbound
  rw [hdiff] at ht hv
  calc
    _ ≤ 4 * |u| ^ 3 * (M * ((b - a) * Real.sqrt (b - a) + (b - a) ^ 3)) +
        (u ^ 2 / 2) * (M * ((b - a) * Real.sqrt (b - a) + (b - a) ^ 2)) +
        u ^ 4 * (q * (b - a)) ^ 2 / 4 := by gcongr
    _ = _ := by ring

theorem integral_characteristic_eq_gaussian_of_martingale_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} (hW : Martingale W F P)
    {M : ℝ} (hM : 0 ≤ M)
    (hD2 : ∀ a b : ℝ≥0, a ≤ b →
      Integrable (fun ω => (W b ω - W a ω) ^ 2) P)
    (hD3 : ∀ a b : ℝ≥0, a ≤ b →
      Integrable (fun ω => |W b ω - W a ω| ^ 3) P)
    (hthird : ∀ a b : ℝ≥0, a ≤ b →
      (∫ ω, |W b ω - W a ω| ^ 3 ∂P) ≤
        M * (((b : ℝ) - a) * Real.sqrt ((b : ℝ) - a) + ((b : ℝ) - a) ^ 3))
    (hvariance : ∀ a b : ℝ≥0, a ≤ b → ∀ Y : Ω → ℂ,
      StronglyMeasurable[F a] Y → (∀ᵐ ω ∂P, ‖Y ω‖ ≤ 1) →
      ‖∫ ω, Y ω * (((W b ω - W a ω : ℝ) : ℂ) ^ 2 - (((b : ℝ) - (a : ℝ) : ℝ) : ℂ)) ∂P‖ ≤
        M * (((b : ℝ) - a) * Real.sqrt ((b : ℝ) - a) + ((b : ℝ) - a) ^ 2))
    (s T : ℝ≥0) (u : ℝ) (Z : Ω → ℂ)
    (hZ : StronglyMeasurable[F s] Z) (hbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1) :
    (∫ ω, Z ω * Complex.exp (((u * (W (s + T) ω - W s ω) : ℝ) : ℂ) * Complex.I) ∂P) =
      Complex.exp ((-(u ^ 2 / 2) * (T : ℝ) : ℝ) : ℂ) * ∫ ω, Z ω ∂P := by
  simpa only [mul_one, one_mul] using
    integral_characteristic_eq_gaussian_of_martingale_moments_rate P hW 1
      (by norm_num) hM hD2 hD3 hthird
      (by simpa only [one_mul] using hvariance) s T u Z hZ hbound

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InnovationCharacteristic
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
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

theorem norm_integral_test_increment_sq_error_le
    {B W : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hW : ∀ t, AEMeasurable (W t) P) {s t : ℝ≥0} (hst : s ≤ t)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hvariance : P[(fun ω => (B t ω - B s ω)^2) | m] =ᵐ[P]
      fun _ => (t : ℝ) - (s : ℝ))
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ᵐ ω ∂P,
      |(W t ω - W s ω) - (B t ω - B s ω)| ≤ L * ((t : ℝ) - (s : ℝ)))
    {Z : Ω → ℂ} (hZ : StronglyMeasurable[m] Z)
    (hZbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1) :
    ‖∫ ω, Z ω * (((W t ω - W s ω : ℝ) : ℂ)^2 -
      (((t : ℝ) - (s : ℝ)) : ℂ)) ∂P‖ ≤
      2 * (L * ((t : ℝ) - (s : ℝ))) * Real.sqrt ((t : ℝ) - (s : ℝ)) +
        (L * ((t : ℝ) - (s : ℝ))) ^ 2 := by
  let : MeasurableSpace Ω := mΩ
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hD2 := integrable_increment_sq_of_bounded_drift hB hW hst hL hbound
  have hB2 : Integrable (fun ω => (B t ω - B s ω)^2) P := by
    simpa only [sq_abs] using
      integrable_abs_pow_of_gaussianLaw (preBrownian_hasLaw_increment hB hst) 2
  have htest := InnovationConditionalMoments.norm_integral_test_sub_const_le
    hm hD2 hB2 hvariance hZ (by norm_num : (0 : ℝ) ≤ 1) hZbound
  have hmoment := (preBrownian_bounded_drift_increment_moments hB hW hst hL hbound).2.1
  have heq : (fun ω => Z ω * (((W t ω - W s ω : ℝ) : ℂ)^2 -
      (((t : ℝ) - (s : ℝ)) : ℂ))) =
      (fun ω => ((W t ω - W s ω)^2 - ((t : ℝ) - (s : ℝ))) • Z ω) := by
    funext ω
    rw [Complex.real_smul]
    push_cast
    ring
  rw [heq]
  exact htest.trans (by simpa only [one_mul] using hmoment)

theorem norm_integral_test_increment_sq_error_le_common_constant
    {B W : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hW : ∀ t, AEMeasurable (W t) P) {s t : ℝ≥0} (hst : s ≤ t)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hvariance : P[(fun ω => (B t ω - B s ω)^2) | m] =ᵐ[P]
      fun _ => (t : ℝ) - (s : ℝ))
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ᵐ ω ∂P,
      |(W t ω - W s ω) - (B t ω - B s ω)| ≤ L * ((t : ℝ) - (s : ℝ)))
    {Z : Ω → ℂ} (hZ : StronglyMeasurable[m] Z)
    (hZbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1) :
    ‖∫ ω, Z ω * (((W t ω - W s ω : ℝ) : ℂ)^2 -
      (((t : ℝ) - (s : ℝ)) : ℂ)) ∂P‖ ≤ driftMomentConstant L *
      (((t : ℝ) - (s : ℝ)) * Real.sqrt ((t : ℝ) - (s : ℝ)) +
        ((t : ℝ) - (s : ℝ)) ^ 2) := by
  let : MeasurableSpace Ω := mΩ
  have hp := standardGaussianThirdMoment_nonneg
  have h1 : 2 * L ≤ driftMomentConstant L := by unfold driftMomentConstant; nlinarith [pow_nonneg hL 3, sq_nonneg L]
  have h2 : L ^ 2 ≤ driftMomentConstant L := by unfold driftMomentConstant; nlinarith [pow_nonneg hL 3, sq_nonneg L]
  have htime : 0 ≤ (t : ℝ) - (s : ℝ) := sub_nonneg.mpr hst
  calc
    _ ≤ 2 * (L * ((t : ℝ) - (s : ℝ))) * Real.sqrt ((t : ℝ) - (s : ℝ)) +
        (L * ((t : ℝ) - (s : ℝ))) ^ 2 :=
      norm_integral_test_increment_sq_error_le hB hW hst hm hvariance hL hbound hZ hZbound
    _ = (2 * L) * (((t : ℝ) - (s : ℝ)) * Real.sqrt ((t : ℝ) - (s : ℝ))) +
        L ^ 2 * ((t : ℝ) - (s : ℝ)) ^ 2 := by ring
    _ ≤ driftMomentConstant L * (((t : ℝ) - (s : ℝ)) * Real.sqrt ((t : ℝ) - (s : ℝ))) +
        driftMomentConstant L * ((t : ℝ) - (s : ℝ)) ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_right h1 (by positivity))
        (mul_le_mul_of_nonneg_right h2 (by positivity))
    _ = _ := by ring

theorem integral_characteristic_eq_gaussian_of_bounded_drift
    {F : Filtration ℝ≥0 mΩ} {B W : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hW : Martingale W F P)
    (hvariance : ∀ a b : ℝ≥0, a ≤ b →
      P[(fun ω => (B b ω - B a ω)^2) | F a] =ᵐ[P]
        fun _ => (b : ℝ) - (a : ℝ))
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ a b : ℝ≥0, a ≤ b → ∀ᵐ ω ∂P,
      |(W b ω - W a ω) - (B b ω - B a ω)| ≤ L * ((b : ℝ) - (a : ℝ)))
    (s T : ℝ≥0) (u : ℝ) (Z : Ω → ℂ)
    (hZ : StronglyMeasurable[F s] Z) (hZbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1) :
    (∫ ω, Z ω * Complex.exp (((u * (W (s + T) ω - W s ω) : ℝ) : ℂ) * Complex.I) ∂P) =
      Complex.exp ((-(u ^ 2 / 2) * (T : ℝ) : ℝ) : ℂ) * ∫ ω, Z ω ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hWm (t : ℝ≥0) : AEMeasurable (W t) P :=
    ((hW.stronglyMeasurable t).mono (F.le t)).measurable.aemeasurable
  apply integral_characteristic_eq_gaussian_of_martingale_moments P hW
    (driftMomentConstant_nonneg hL)
    (fun a b hab => integrable_increment_sq_of_bounded_drift hB hWm hab hL (hbound a b hab))
    (fun a b hab => (preBrownian_bounded_drift_increment_moments
      hB hWm hab hL (hbound a b hab)).2.2.1)
    (fun a b hab => integral_increment_cube_le_common_constant hB hWm hab hL (hbound a b hab))
    (fun a b hab Y hY hbY => by
      simpa only [Complex.ofReal_sub] using
        (norm_integral_test_increment_sq_error_le_common_constant
          hB hWm hab (F.le a) (hvariance a b hab) hL (hbound a b hab) hY hbY))
    s T u Z hZ hZbound

end Problem367.InnovationCharacteristic

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_Innovation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Problem367.ConditionalCharacteristic

namespace Problem367.BrownianInnovation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem setIntegral_character_of_bounded_drift
    {F : Filtration ℝ≥0 mΩ} {B W : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hW : Martingale W F P)
    (hvariance : ∀ a b : ℝ≥0, a ≤ b →
      P[(fun ω => (B b ω - B a ω)^2) | F a] =ᵐ[P]
        fun _ => (b : ℝ) - (a : ℝ))
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ a b : ℝ≥0, a ≤ b → ∀ᵐ ω ∂P,
      |(W b ω - W a ω) - (B b ω - B a ω)| ≤ L * ((b : ℝ) - (a : ℝ)))
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[F s] A) (u : ℝ) :
    (∫ ω in A, character (fun ω => W t ω - W s ω) u ω ∂P) =
      P.real A * Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * (u : ℂ)^2 / 2) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let Z : Ω → ℂ := A.indicator (fun _ => 1)
  have hZ : StronglyMeasurable[F s] Z := stronglyMeasurable_const.indicator hA
  have hZbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro ω
    by_cases hω : ω ∈ A <;> simp [Z, hω]
  have h := InnovationCharacteristic.integral_characteristic_eq_gaussian_of_bounded_drift
    hB hW hvariance hL hbound s (t - s) u Z hZ hZbound
  rw [add_tsub_cancel_of_le hst] at h
  have heq : (fun ω => Z ω *
      Complex.exp (((u * (W t ω - W s ω) : ℝ) : ℂ) * Complex.I)) =
      A.indicator (character (fun ω => W t ω - W s ω) u) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [Z, character, hω, Complex.ofReal_mul]
  have hZint : (∫ ω, Z ω ∂P) = (P.real A : ℂ) := by
    simp [Z, integral_indicator ((F.le s) A hA)]
  have hexp : ((-(u ^ 2 / 2) * ((t - s : ℝ≥0) : ℝ) : ℝ) : ℂ) =
      -(((t - s : ℝ≥0) : ℝ) : ℂ) * (u : ℂ)^2 / 2 := by
    push_cast
    ring
  rw [heq, integral_indicator ((F.le s) A hA), hZint, hexp] at h
  exact h.trans (mul_comm _ _)

theorem isPreBrownianReal_of_bounded_drift
    {F : Filtration ℝ≥0 mΩ} {B W : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hW : Martingale W F P)
    (hvariance : ∀ a b : ℝ≥0, a ≤ b →
      P[(fun ω => (B b ω - B a ω)^2) | F a] =ᵐ[P]
        fun _ => (b : ℝ) - (a : ℝ))
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ a b : ℝ≥0, a ≤ b → ∀ᵐ ω ∂P,
      |(W b ω - W a ω) - (B b ω - B a ω)| ≤ L * ((b : ℝ) - (a : ℝ)))
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) :
    IsPreBrownianReal W P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  apply BrownianCharacterization.isPreBrownianReal_of_setIntegral_character
    F hW.stronglyAdapted hzero
  intro s t hst A hA u
  exact setIntegral_character_of_bounded_drift hB hW hvariance hL hbound hst hA u

end Problem367.BrownianInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressivePrimitive
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.innovationPath_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem stronglyAdapted_nnrealTimePrimitive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {F : Filtration ℝ≥0 mΩ}
    {m : ℝ≥0 → Ω → ℝ} (hm : IsStronglyProgressive F m) :
    StronglyAdapted F (nnrealTimePrimitive m) := by
  intro t
  have hcl := stronglyMeasurable_clipped_nnreal_process hm t
  have hi : StronglyMeasurable[F t]
      (fun ω => ∫ r in Set.Ioc (0 : ℝ) (t : ℝ), m (min r.toNNReal t) ω) := by
    let : MeasurableSpace Ω := F t
    exact hcl.integral_prod_left'
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  rw [nnrealTimePrimitive, intervalIntegral.integral_of_le t.coe_nonneg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  have hrt : r.toNNReal ≤ t := by simpa using Real.toNNReal_mono hr.2
  simp only [min_eq_left hrt]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressivePrimitiveFubini
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367

theorem lipschitzWith_nnrealTimePrimitive_of_local_bounds
    {Ω : Type*} {m : ℝ≥0 → Ω → ℝ} {ω : Ω} {C : ℝ≥0}
    (hint : ∀ n : ℕ,
      IntegrableOn (fun u : ℝ => m u.toNNReal ω) (Ioc 0 (n : ℝ)))
    (hbound : ∀ n : ℕ, ∀ᵐ u ∂volume.restrict (Ioc 0 (n : ℝ)),
      |m u.toNNReal ω| ≤ (C : ℝ)) :
    LipschitzWith C (fun t => nnrealTimePrimitive m t ω) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  obtain ⟨n, hn⟩ := exists_nat_gt (max (s : ℝ) (t : ℝ))
  have hsn : (s : ℝ) ≤ n := (le_max_left _ _).trans hn.le
  have htn : (t : ℝ) ≤ n := (le_max_right _ _).trans hn.le
  have his : IntervalIntegrable (fun u : ℝ => m u.toNNReal ω) volume 0 s :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le s.coe_nonneg).mpr
      ((hint n).mono_set (Ioc_subset_Ioc le_rfl hsn))
  have hit : IntervalIntegrable (fun u : ℝ => m u.toNNReal ω) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mpr
      ((hint n).mono_set (Ioc_subset_Ioc le_rfl htn))
  have hsub : uIoc (t : ℝ) (s : ℝ) ⊆ Ioc 0 (n : ℝ) := by
    intro u hu
    exact ⟨lt_of_le_of_lt (le_min t.coe_nonneg s.coe_nonneg) hu.1,
      hu.2.trans (max_le htn hsn)⟩
  have hb : ∀ᵐ u ∂volume, u ∈ uIoc (t : ℝ) (s : ℝ) →
      ‖m u.toNNReal ω‖ ≤ (C : ℝ) := by
    apply ae_imp_of_ae_restrict
    simpa only [Real.norm_eq_abs] using
      ae_restrict_of_ae_restrict_of_subset hsub (hbound n)
  simp only [Real.dist_eq, NNReal.dist_eq, nnrealTimePrimitive]
  rw [intervalIntegral.integral_interval_sub_left his hit]
  simpa only [Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_of_norm_le_const_ae hb

theorem ae_lipschitzWith_nnrealTimePrimitive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) {C : ℝ≥0}
    (hbound : ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ (C : ℝ)) :
    ∀ᵐ ω ∂P, LipschitzWith C (fun t => nnrealTimePrimitive m t ω) := by
  filter_upwards [ae_locally_integrable_bounded_progressive hm hbound] with ω hω
  exact lipschitzWith_nnrealTimePrimitive_of_local_bounds
    (fun n => (hω n).1) (fun n => (hω n).2)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressiveArrayInnovation
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

theorem preBrownian_array_innovation_martingale_of_progressive_posterior
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ) (i : ι)
    {C : ℝ} (hσbound : ∀ᵐ s ∂ν, |σ s i| ≤ C)
    {m : ℝ≥0 → S × (ι → Ω) → ℝ}
    (hm : IsStronglyProgressive (arrayObservationFiltration B hmB σ hσ) m)
    (hposterior : ∀ t, m t =ᵐ[ν.prod (Measure.infinitePi μ)]
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ t]) :
    Martingale
      (fun t q => plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q)
      (arrayObservationFiltration B hmB σ hσ) (ν.prod (Measure.infinitePi μ)) := by
  have (j : ι) : IsProbabilityMeasure (μ j) :=
    (hB j).isGaussianProcess.isProbabilityMeasure
  have hσint : Integrable (fun s => σ s i) ν :=
    (integrable_const C).mono'
      (((measurable_pi_apply i).comp hσ).aestronglyMeasurable)
      (by simpa only [Real.norm_eq_abs] using hσbound)
  have hbound : ∀ t, ∀ᵐ q ∂ν.prod (Measure.infinitePi μ), |m t q| ≤ C :=
    posterior_version_ae_abs_le hposterior
      (Measure.quasiMeasurePreserving_fst.ae hσbound)
  exact preBrownian_array_observation_innovation_martingale ν μ hB hmB hσ i hσint
    hm.stronglyAdapted hposterior
    (stronglyAdapted_nnrealTimePrimitive hm)
    (fun s t _ => integrable_nnreal_process_interval_of_progressive_bounded hm C hbound s t)

theorem ae_lipschitzWith_array_posterior_primitive
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    [∀ j, IsProbabilityMeasure (μ j)]
    {B : ι → ℝ≥0 → Ω → ℝ} (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ) (i : ι)
    {C : ℝ≥0} (hσbound : ∀ᵐ s ∂ν, |σ s i| ≤ (C : ℝ))
    {m : ℝ≥0 → S × (ι → Ω) → ℝ}
    (hm : IsStronglyProgressive (arrayObservationFiltration B hmB σ hσ) m)
    (hposterior : ∀ t, m t =ᵐ[ν.prod (Measure.infinitePi μ)]
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ t]) :
    ∀ᵐ q ∂ν.prod (Measure.infinitePi μ),
      LipschitzWith C (fun t => nnrealTimePrimitive m t q) :=
  ae_lipschitzWith_nnrealTimePrimitive hm
    (posterior_version_ae_abs_le hposterior
      (Measure.quasiMeasurePreserving_fst.ae hσbound))

theorem brownian_array_innovation_regular_martingale
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ) (i : ι)
    {C : ℝ≥0} (hσbound : ∀ᵐ s ∂ν, |σ s i| ≤ (C : ℝ))
    {m : ℝ≥0 → S × (ι → Ω) → ℝ}
    (hm : IsStronglyProgressive (arrayObservationFiltration B hmB σ hσ) m)
    (hposterior : ∀ t, m t =ᵐ[ν.prod (Measure.infinitePi μ)]
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ t]) :
    Martingale
      (fun t q => plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q)
      (arrayObservationFiltration B hmB σ hσ) (ν.prod (Measure.infinitePi μ)) ∧
    (∀ᵐ q ∂ν.prod (Measure.infinitePi μ),
      Continuous (fun t => plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q)) ∧
    (∀ᵐ q ∂ν.prod (Measure.infinitePi μ),
      plantedArrayObservation B σ i 0 q - nnrealTimePrimitive m 0 q = 0) := by
  have (j : ι) : IsProbabilityMeasure (μ j) :=
    (hB j).toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  refine ⟨preBrownian_array_innovation_martingale_of_progressive_posterior
    ν μ (fun j => (hB j).toIsPreBrownianReal) hmB hσ i hσbound hm hposterior, ?_, ?_⟩
  · have hcont := (planted_noise_coordinate_measurePreserving ν μ i).quasiMeasurePreserving.ae
      (hB i).cont
    filter_upwards [hcont,
      ae_lipschitzWith_array_posterior_primitive ν μ hmB hσ i hσbound hm hposterior]
      with q hcontq hA
    change Continuous (fun t => B i t (q.2 i) + (t : ℝ) * σ q.1 i -
      nnrealTimePrimitive m t q)
    exact (hcontq.add (continuous_subtype_val.mul continuous_const)).sub hA.continuous
  · have hzero := (planted_noise_coordinate_measurePreserving ν μ i).quasiMeasurePreserving.ae
      (hB i).eval_zero_ae_eq_zero
    filter_upwards [hzero] with q hq
    simpa only [plantedArrayObservation, nnrealTimePrimitive, NNReal.coe_zero,
      zero_mul, add_zero, intervalIntegral.integral_same, sub_zero] using hq

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ArrayInnovation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.innovationPath_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem ae_array_innovation_increment_drift_bound
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    [∀ j, IsProbabilityMeasure (μ j)]
    {B : ι → ℝ≥0 → Ω → ℝ} (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ) (i : ι)
    {C : ℝ≥0} (hσbound : ∀ᵐ s ∂ν, |σ s i| ≤ (C : ℝ))
    {m : ℝ≥0 → S × (ι → Ω) → ℝ}
    (hm : IsStronglyProgressive (arrayObservationFiltration B hmB σ hσ) m)
    (hposterior : ∀ t, m t =ᵐ[ν.prod (Measure.infinitePi μ)]
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ t])
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∀ᵐ q ∂ν.prod (Measure.infinitePi μ),
      |((plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q) -
          (plantedArrayObservation B σ i s q - nnrealTimePrimitive m s q)) -
        (B i t (q.2 i) - B i s (q.2 i))| ≤
        (2 * (C : ℝ)) * ((t : ℝ) - (s : ℝ)) := by
  have hsignal : ∀ᵐ q ∂ν.prod (Measure.infinitePi μ), |σ q.1 i| ≤ (C : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae hσbound
  filter_upwards [hsignal,
    ae_lipschitzWith_array_posterior_primitive ν μ hmB hσ i hσbound hm hposterior]
    with q hsq hlip
  have htime : 0 ≤ (t : ℝ) - (s : ℝ) := sub_nonneg.mpr hst
  have hprim : |nnrealTimePrimitive m t q - nnrealTimePrimitive m s q| ≤
      (C : ℝ) * ((t : ℝ) - (s : ℝ)) := by
    simpa only [Real.dist_eq, NNReal.dist_eq, abs_of_nonneg htime] using
      hlip.dist_le_mul t s
  have heq : ((plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q) -
      (plantedArrayObservation B σ i s q - nnrealTimePrimitive m s q)) -
      (B i t (q.2 i) - B i s (q.2 i)) =
      ((t : ℝ) - (s : ℝ)) * σ q.1 i -
        (nnrealTimePrimitive m t q - nnrealTimePrimitive m s q) := by
    unfold plantedArrayObservation
    ring
  rw [heq]
  calc
    _ ≤ |((t : ℝ) - (s : ℝ)) * σ q.1 i| +
        |nnrealTimePrimitive m t q - nnrealTimePrimitive m s q| := abs_sub _ _
    _ ≤ ((t : ℝ) - (s : ℝ)) * (C : ℝ) +
        (C : ℝ) * ((t : ℝ) - (s : ℝ)) := by
      rw [abs_mul, abs_of_nonneg htime]
      exact add_le_add (mul_le_mul_of_nonneg_left hsq htime) hprim
    _ = _ := by ring

theorem preBrownian_array_innovation_of_progressive_posterior
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ) (i : ι)
    {C : ℝ≥0} (hσbound : ∀ᵐ s ∂ν, |σ s i| ≤ (C : ℝ))
    {m : ℝ≥0 → S × (ι → Ω) → ℝ}
    (hm : IsStronglyProgressive (arrayObservationFiltration B hmB σ hσ) m)
    (hposterior : ∀ t, m t =ᵐ[ν.prod (Measure.infinitePi μ)]
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ t]) :
    IsPreBrownianReal
      (fun t q => plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q)
      (ν.prod (Measure.infinitePi μ)) := by
  classical
  have (j : ι) : IsProbabilityMeasure (μ j) :=
    (hB j).isGaussianProcess.isProbabilityMeasure
  apply BrownianInnovation.isPreBrownianReal_of_bounded_drift
    (planted_coordinate_preBrownian ν μ hB i)
    (preBrownian_array_innovation_martingale_of_progressive_posterior
      ν μ hB hmB hσ i hσbound hm hposterior)
    (L := 2 * (C : ℝ))
  · intro s t hst
    have hv := planted_weighted_increment_sq_condExp_subfield ν μ hB hmB hst
      ({i} : Finset ι) (fun _ => (1 : ℝ))
      (arrayObservationFiltration_le_signalArrayFiltration B hmB σ hσ s)
    simpa using hv
  · positivity
  · intro s t hst
    exact ae_array_innovation_increment_drift_bound ν μ hmB hσ i hσbound hm hposterior hst
  · have hzero := (planted_noise_coordinate_measurePreserving ν μ i).quasiMeasurePreserving.ae
      (hB i).eval_zero_ae_eq_zero
    filter_upwards [hzero] with q hq
    simpa only [plantedArrayObservation, nnrealTimePrimitive, NNReal.coe_zero,
      zero_mul, add_zero, intervalIntegral.integral_same, sub_zero] using hq

theorem brownian_array_innovation_of_progressive_posterior
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ) (i : ι)
    {C : ℝ≥0} (hσbound : ∀ᵐ s ∂ν, |σ s i| ≤ (C : ℝ))
    {m : ℝ≥0 → S × (ι → Ω) → ℝ}
    (hm : IsStronglyProgressive (arrayObservationFiltration B hmB σ hσ) m)
    (hposterior : ∀ t, m t =ᵐ[ν.prod (Measure.infinitePi μ)]
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ t]) :
    IsBrownianReal
      (fun t q => plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q)
      (ν.prod (Measure.infinitePi μ)) :=
  ⟨preBrownian_array_innovation_of_progressive_posterior
      ν μ (fun j => (hB j).toIsPreBrownianReal) hmB hσ i hσbound hm hposterior,
    (brownian_array_innovation_regular_martingale ν μ hB hmB hσ i hσbound hm hposterior).2.1⟩

end Problem367

end

end OAI
end

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

theorem map_preBrownian_process_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'}
    {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ω' → ℝ}
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q)
    (hmB : ∀ t, Measurable (B t)) (hmC : ∀ t, Measurable (C t)) :
    P.map (fun ω t => B t ω) = Q.map (fun ω t => C t ω) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have : IsProbabilityMeasure Q := hC.isGaussianProcess.isProbabilityMeasure
  have hp : IsProjectiveLimit (P.map (fun ω t => B t ω))
      ProbabilityTheory.BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I)
      (Measurable.of_eval hmB)]
    exact (hB.hasLaw I).map_eq
  have hq : IsProjectiveLimit (Q.map (fun ω t => C t ω))
      ProbabilityTheory.BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I)
      (Measurable.of_eval hmC)]
    exact (hC.hasLaw I).map_eq
  exact hp.unique hq

section ContinuousPaths

variable {T : Type*} [TopologicalSpace T] [TopologicalSpace.SeparableSpace T]
  [Nonempty T] [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]
  [StandardBorelSpace C(T, ℝ)]

theorem measurableEmbedding_continuousPath_denseSeq :
    MeasurableEmbedding
      (fun (f : C(T, ℝ)) n => f (TopologicalSpace.denseSeq T n)) := by
  apply Measurable.measurableEmbedding
  · exact Measurable.of_eval (fun _ => (continuous_eval_const _).measurable)
  · intro f g h
    apply ContinuousMap.coe_injective
    exact (TopologicalSpace.denseRange_denseSeq T).equalizer f.continuous g.continuous h

theorem iIndepFun_continuousPaths_of_evaluations
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ι → Ω → C(T, ℝ)}
    (h : iIndepFun (fun i ω t => X i ω t) P) : iIndepFun X P := by
  apply iIndepFun_of_measurableEmbedding measurableEmbedding_continuousPath_denseSeq
  exact h.comp (fun _ f n => f (TopologicalSpace.denseSeq T n))
    (fun _ => Measurable.of_eval (fun _ => measurable_pi_apply _))

theorem map_continuousPaths_eq_of_evaluations
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'}
    {X : Ω → C(T, ℝ)} {Y : Ω' → C(T, ℝ)}
    (hmX : Measurable X) (hmY : Measurable Y)
    (h : P.map (fun ω t => X ω t) = Q.map (fun ω t => Y ω t)) :
    P.map X = Q.map Y := by
  apply measurableEmbedding_continuousPath_denseSeq.map_injective
  rw [Measure.map_map measurableEmbedding_continuousPath_denseSeq.measurable hmX,
    Measure.map_map measurableEmbedding_continuousPath_denseSeq.measurable hmY]
  have hs : Measurable (fun f : T → ℝ => fun n => f (TopologicalSpace.denseSeq T n)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  have hX : Measurable (fun ω t => X ω t) :=
    Measurable.of_eval (fun time => (continuous_eval_const time).measurable.comp hmX)
  have hY : Measurable (fun ω t => Y ω t) :=
    Measurable.of_eval (fun time => (continuous_eval_const time).measurable.comp hmY)
  have hh := congrArg
    (Measure.map (fun f : T → ℝ => fun n => f (TopologicalSpace.denseSeq T n))) h
  simpa only [Measure.map_map hs hX, Measure.map_map hs hY, Function.comp_def] using hh

end ContinuousPaths

section ContinuousBrownianPaths

variable [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]
  [StandardBorelSpace C(ℝ≥0, ℝ)]

theorem map_continuousPreBrownian_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'}
    {X : Ω → C(ℝ≥0, ℝ)} {Y : Ω' → C(ℝ≥0, ℝ)}
    (hmX : Measurable X) (hmY : Measurable Y)
    (hX : IsPreBrownianReal (fun t ω => X ω t) P)
    (hY : IsPreBrownianReal (fun t ω => Y ω t) Q) :
    P.map X = Q.map Y := by
  apply map_continuousPaths_eq_of_evaluations hmX hmY
  exact map_preBrownian_process_eq hX hY
    (fun t => (continuous_eval_const t).measurable.comp hmX)
    (fun t => (continuous_eval_const t).measurable.comp hmY)

end ContinuousBrownianPaths

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_LinearCombination
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianLinearCombination

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ι → ℝ≥0 → Ω → ℝ}

theorem covariance_sum
    (hB : ∀ i, IsPreBrownianReal (B i) μ)
    (hind : iIndepFun (fun i ω t => B i t ω) μ) (a : ι → ℝ)
    (s t : ℝ≥0) :
    cov[fun ω => ∑ i, a i * B i s ω, fun ω => ∑ i, a i * B i t ω; μ] =
      (∑ i, (a i) ^ 2) * (min s t : ℝ≥0) := by
  classical
  rw [covariance_fun_sum_fun_sum
    (fun i => ((hB i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two.const_mul (a i))
    (fun i => ((hB i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two.const_mul (a i))]
  have heq (i j : ι) : cov[fun ω => a i * B i s ω, fun ω => a j * B j t ω; μ] =
      if i = j then (a i) ^ 2 * (min s t : ℝ≥0) else 0 := by
    rw [covariance_const_mul_left, covariance_const_mul_right]
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, (hB i).covariance_eval]
      ring
    · rw [ite_eq_right hij, covariance_channel_ne hB hind hij, mul_zero, mul_zero]
  simp_rw [heq]
  simp [Finset.sum_mul]

theorem isPreBrownianReal_sum
    (hB : ∀ i, IsPreBrownianReal (B i) μ)
    (hind : iIndepFun (fun i ω t => B i t ω) μ) (a : ι → ℝ)
    (ha : ∑ i, (a i) ^ 2 = 1) :
    IsPreBrownianReal (fun t ω => ∑ i, a i * B i t ω) μ := by
  apply (isGaussianProcess_sum (fun i => (hB i).isGaussianProcess) hind a).isPreBrownianReal_of_covariance
  · intro t
    rw [integral_finsetSum _ (fun i _ => ((hB i).integrable_eval t).const_mul (a i))]
    simp_rw [integral_const_mul, IsPreBrownianReal.integral_eval (hB _), mul_zero]
    simp
  · intro s t hst
    rw [covariance_sum hB hind a, ha, one_mul, min_eq_left hst]

end Problem367.BrownianLinearCombination

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

lemma cavityMessage_neg {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    cavityMessage theta (-z) = -cavityMessage theta z := by
  simp only [cavityMessage, Real.tanh_neg, mul_neg]
  exact artanh_neg_of_mem (cavityMessage_argument_mem hθ z)

lemma cavityMessage_le_artanh {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (z : ℝ) :
    cavityMessage theta z ≤ Real.artanh theta := by
  have hsq : theta ^ 2 ≤ 1 := by nlinarith
  apply Real.artanh_le_artanh (cavityMessage_argument_mem hsq z).1 hθ1
  simpa using mul_le_mul_of_nonneg_left (Real.tanh_lt_one z).le hθ0

lemma cavityMessage_abs_le_artanh {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (z : ℝ) :
    |cavityMessage theta z| ≤ Real.artanh theta := by
  have hsq : theta ^ 2 ≤ 1 := by nlinarith
  apply abs_le.mpr
  constructor
  · have h := cavityMessage_le_artanh hθ0 hθ1 (-z)
    rw [cavityMessage_neg hsq z] at h
    linarith
  · exact cavityMessage_le_artanh hθ0 hθ1 z

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

theorem cavityFromSites_spec {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (z : ℝ × ℝ) :
    (cavityFromSites h0 h1 z).1 + cavityMessage theta (cavityFromSites h0 h1 z).2 = z.1 ∧
    (cavityFromSites h0 h1 z).2 + cavityMessage theta (cavityFromSites h0 h1 z).1 = z.2 :=
  CavityPair.solve_spec (lipschitzWith_cavityMessage h0 h1.le) h1 z

theorem continuous_cavityFromSites {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1) :
    Continuous (cavityFromSites h0 h1) := (cavityHomeomorph h0 h1).symm.continuous

theorem cavityFromSites_bound {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (z : ℝ × ℝ) :
    |(cavityFromSites h0 h1 z).1 - z.1| ≤ Real.artanh theta ∧
    |(cavityFromSites h0 h1 z).2 - z.2| ≤ Real.artanh theta := by
  have h := cavityFromSites_spec h0 h1 z
  constructor
  · rw [show (cavityFromSites h0 h1 z).1 - z.1 =
        -cavityMessage theta (cavityFromSites h0 h1 z).2 by linarith [h.1], abs_neg]
    exact cavityMessage_abs_le_artanh h0 h1 _
  · rw [show (cavityFromSites h0 h1 z).2 - z.2 =
        -cavityMessage theta (cavityFromSites h0 h1 z).1 by linarith [h.2], abs_neg]
    exact cavityMessage_abs_le_artanh h0 h1 _

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Array
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.CavityArray

variable {d : ℕ} {theta : ℝ}

theorem continuous_field (h0 : 0 ≤ theta) (h1 : theta < 1) :
    Continuous (field (d := d) h0 h1) := by
  apply continuous_pi
  intro v
  apply continuous_pi
  intro w
  exact continuous_fst.comp ((continuous_cavityFromSites h0 h1).comp
    ((continuous_apply v).prodMk (continuous_apply w)))

theorem measurable_field (h0 : 0 ≤ theta) (h1 : theta < 1) :
    Measurable (field (d := d) h0 h1) :=
  (continuous_field h0 h1).measurable

theorem measurable_field_apply (h0 : 0 ≤ theta) (h1 : theta < 1)
    (v w : TreeVertex d) : Measurable (fun H => field h0 h1 H v w) :=
  (measurable_pi_apply w).comp ((measurable_pi_apply v).comp
    (measurable_field h0 h1))

theorem field_site_bound (h0 : 0 ≤ theta) (h1 : theta < 1)
    (H : TreeVertex d → ℝ) (v w : TreeVertex d) :
    |field h0 h1 H v w - H v| ≤ Real.artanh theta :=
  (cavityFromSites_bound h0 h1 (H v, H w)).1

section Joining

abbrev SitePair (d : ℕ) := (TreeVertex d → ℝ) × (TreeVertex d → ℝ)

def pairRelabel (g : TreeAut d) : SitePair d → SitePair d :=
  Prod.map (relabel g) (relabel g)

end Joining

end Problem367.CavityArray

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_FiniteGaussianPlanted
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeShellFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace Problem367

theorem finiteGaussianPlanted_joint_law
    {A I : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype I] (μ : Measure A) [IsProbabilityMeasure μ]
    (t : ℝ≥0) (s : A → I → ℝ) :
    (μ.prod (Measure.pi (fun _ : I => gaussianReal 0 t))).map
      (fun z : A × (I → ℝ) => (z.1, fun i => (t : ℝ) * s z.1 i + z.2 i)) =
        μ ⊗ₘ finiteGaussianObservationKernel t s := by
  apply map_planted_eq_compProd μ (Measure.pi (fun _ : I => gaussianReal 0 t))
    (finiteGaussianObservationKernel t s) (fun a x i => (t : ℝ) * s a i + x i)
  · exact Measurable.of_eval (fun index =>
      (measurable_const.mul
        ((measurable_of_finite (fun state => s state index)).comp measurable_fst)).add
        ((measurable_pi_apply index).comp measurable_snd))
  · intro a
    exact gaussianPi_map_signal t (s a)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteMarginals
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.restrict_atom {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (eta : D → IsingSpin) :
    (mu.map D.restrict) {eta} = freeCylinderWeight theta D (extendFiniteSpin D eta) := by
  classical
  rw [Measure.map_apply D.measurable_restrict (measurableSet_singleton eta)]
  convert hmu D hD (extendFiniteSpin D eta) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext x
  change D.restrict x = eta ↔ ∀ v ∈ D, x v = extendFiniteSpin D eta v
  constructor
  · intro hx v hv
    have h := congrFun hx ⟨v, hv⟩
    simpa [Finset.restrict_def, extendFiniteSpin, hv] using h
  · intro hx
    funext v
    simpa [Finset.restrict_def, extendFiniteSpin] using hx v v.property

theorem HasFreeIsingLaw.restrict_finset {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (A : Finset (D → IsingSpin)) :
    (mu.map D.restrict) A =
      ∑ eta ∈ A, freeCylinderWeight theta D (extendFiniteSpin D eta) := by
  rw [← sum_measure_singleton]
  exact Finset.sum_congr rfl (fun eta _ => hmu.restrict_atom D hD eta)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_Weights
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem transitionKernel_tanh_eq_exp (beta : ℝ) (a b : IsingSpin) :
    transitionKernel (Real.tanh beta) a b =
      Real.exp (beta * spinSign a * spinSign b) / (2 * Real.cosh beta) := by
  have hc : Real.cosh beta ≠ 0 := ne_of_gt (Real.cosh_pos beta)
  cases a <;> cases b <;>
    simp only [transitionKernel, spinSign_neg, spinSign_pos, mul_neg, mul_one,
      neg_neg] <;>
    rw [Real.tanh_eq_sinh_div_cosh] <;>
    field_simp <;>
    nlinarith [Real.cosh_add_sinh beta, Real.cosh_sub_sinh beta]

theorem prod_transitionKernel_tanh_eq_exp
    {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d))
    (eta : TreeVertex d → IsingSpin) :
    (∏ e ∈ inducedEdges D, transitionKernel (Real.tanh beta) (eta e.1) (eta e.2)) =
      Real.exp (beta * ∑ e ∈ inducedEdges D, spinSign (eta e.1) * spinSign (eta e.2)) /
        (2 * Real.cosh beta) ^ (inducedEdges D).card := by
  simp_rw [transitionKernel_tanh_eq_exp]
  rw [Finset.prod_div_distrib, Finset.prod_const, ← Real.exp_sum]
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem freeCylinderWeight_tanh_eq_exp
    {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d))
    (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight (Real.tanh beta) D eta = ENNReal.ofReal
      (Real.exp (beta * ∑ e ∈ inducedEdges D, spinSign (eta e.1) * spinSign (eta e.2)) /
        (2 * (2 * Real.cosh beta) ^ (inducedEdges D).card)) := by
  rw [freeCylinderWeight_eq_transitionKernel, prod_transitionKernel_tanh_eq_exp]
  congr 1
  ring

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

lemma mean_fieldEnergy_zero (energy : S → ℝ) (spin : S → V → ℝ)
    (signal observable : S → ℝ) (x : V → ℝ) :
    mean (fieldEnergy energy spin x) signal observable 0 =
      fieldMean energy spin observable x := by
  simp only [mean, partition, weight, zero_mul, add_zero, fieldMean]

lemma fieldMean_spin_mem_Ioo [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hs : ∀ s, observable s = -1 ∨ observable s = 1)
    (hn : ∃ s, observable s = -1) (hp : ∃ s, observable s = 1) :
    fieldMean energy spin observable x ∈ Set.Ioo (-1 : ℝ) 1 := by
  rw [← mean_fieldEnergy_zero energy spin (fun _ => 0)]
  exact spin_mean_mem_Ioo _ _ _ _ hs hn hp

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_GaussianPosterior
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace Problem367

local instance gaussianPosteriorNonemptyIsingSpin : Nonempty IsingSpin := ⟨.neg⟩

theorem HasFreeIsingLaw.gaussian_restrict_posterior_mean
    {d : ℕ} {beta : ℝ} {mu : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure mu]
    (hmu : HasFreeIsingLaw (Real.tanh beta) mu)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (t : ℝ≥0) (observable : (D → IsingSpin) → ℝ) :
    ∀ᵐ x ∂finiteGaussianObservationKernel t (fun (eta : D → IsingSpin) (v : D) => spinSign (eta v)) ∘ₘ
        (mu.map D.restrict),
      (∫ eta, observable eta ∂(posterior
        (finiteGaussianObservationKernel t (fun (eta : D → IsingSpin) (v : D) => spinSign (eta v)))
        (mu.map D.restrict)) x) =
      FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) (v : D) => spinSign (eta v)) observable x := by
  classical
  let : IsProbabilityMeasure mu := hmu.isProbabilityMeasure
  let : IsProbabilityMeasure (mu.map D.restrict) := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : Nonempty (D → IsingSpin) := ⟨fun _ => .neg⟩
  let c : ℝ := (2 * (2 * Real.cosh beta) ^ (inducedEdges D).card)⁻¹
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hprior (eta : D → IsingSpin) :
      (mu.map D.restrict).real {eta} = c * Real.exp (finiteIsingEnergy beta D eta) := by
    rw [Measure.real, hmu.restrict_atom D hD eta, freeCylinderWeight_tanh_eq_exp]
    rw [ENNReal.toReal_ofReal (by positivity)]
    dsimp [c, finiteIsingEnergy]
    ring
  have hpost := finiteGaussianObservation_posterior_mean (mu.map D.restrict) t
    (fun (eta : D → IsingSpin) (v : D) => spinSign (eta v)) (fun eta v => spinSign_sq (eta v)) observable
  filter_upwards [hpost] with x hx
  rw [hx]
  simp_rw [hprior]
  have heq (eta : D → IsingSpin) :
      c * Real.exp (finiteIsingEnergy beta D eta) *
          Real.exp (∑ v, spinSign (eta v) * x v) =
      c * Real.exp (FinitePosterior.fieldEnergy (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) (v : D) => spinSign (eta v)) x eta) := by
    have hd : (∑ v, spinSign (eta v) * x v) = ∑ v, x v * spinSign (eta v) := by
      apply Finset.sum_congr rfl
      intro v _
      ring
    rw [hd, FinitePosterior.fieldEnergy, Real.exp_add]
    ring
  simp_rw [heq]
  have hnum : (∑ eta, c * Real.exp (FinitePosterior.fieldEnergy
        (finiteIsingEnergy beta D) (fun (eta : D → IsingSpin) (v : D) => spinSign (eta v)) x eta) * observable eta) =
      c * ∑ eta, observable eta * Real.exp (FinitePosterior.fieldEnergy
        (finiteIsingEnergy beta D) (fun (eta : D → IsingSpin) (v : D) => spinSign (eta v)) x eta) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro eta _
    ring
  rw [hnum, ← Finset.mul_sum, mul_div_mul_left _ _ (ne_of_gt hc)]
  rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ConnectedHull
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

namespace ConnectedHull

theorem prefix_adj {d : ℕ} (v : TreeVertex d) {n : ℕ} (hn : n < v.1.length) :
    treeAdj (takeVertex v n) (takeVertex v (n + 1)) := by
  left
  exact ⟨v.1[n], List.take_succ_eq_append_getElem hn⟩

theorem prefix_paths {d : ℕ} (E : Finset (TreeVertex d)) (v : TreeVertex d)
    (hE : ∀ n ≤ v.1.length, takeVertex v n ∈ E) {n : ℕ} (hn : n ≤ v.1.length) :
    Relation.ReflTransGen (fun x y : TreeVertex d => x ∈ E ∧ y ∈ E ∧ treeAdj x y)
      (root d) (takeVertex v n) ∧
    Relation.ReflTransGen (fun x y : TreeVertex d => x ∈ E ∧ y ∈ E ∧ treeAdj x y)
      (takeVertex v n) (root d) := by
  induction n with
  | zero => simp only [prefix_zero]; exact ⟨.refl, .refl⟩
  | succ n ih =>
    have hn' : n ≤ v.1.length := by omega
    have hlt : n < v.1.length := by omega
    have hadj := prefix_adj v hlt
    have hrev : treeAdj (takeVertex v (n + 1)) (takeVertex v n) := by
      rcases hadj with h | h
      · exact Or.inr h
      · exact Or.inl h
    obtain ⟨hforward, hbackward⟩ := ih hn'
    exact ⟨hforward.trans (.single ⟨hE n hn', hE (n + 1) hn, hadj⟩),
      (Relation.ReflTransGen.single ⟨hE (n + 1) hn, hE n hn', hrev⟩).trans hbackward⟩

theorem hull_paths {d : ℕ} (D : Finset (TreeVertex d)) {v : TreeVertex d}
    (hv : v ∈ hull D) :
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ∈ hull D ∧ y ∈ hull D ∧ treeAdj x y)
      (root d) v ∧
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ∈ hull D ∧ y ∈ hull D ∧ treeAdj x y)
      v (root d) := by
  classical
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact ⟨.refl, .refl⟩
  rcases Finset.mem_biUnion.mp hv with ⟨w, hw, hv⟩
  rcases Finset.mem_image.mp hv with ⟨n, hn, rfl⟩
  apply prefix_paths
  · intro k hk
    exact prefix_mem_hull hw hk
  · have := Finset.mem_range.mp hn
    omega

theorem connected_hull {d : ℕ} (D : Finset (TreeVertex d)) :
    ConnectedFinset (hull D) := by
  classical
  refine ⟨⟨root d, Finset.mem_insert_self _ _⟩, ?_⟩
  intro u hu v hv
  exact (hull_paths D hu).2.trans (hull_paths D hv).1

end ConnectedHull

theorem exists_connectedFinset_superset {d : ℕ} (D : Finset (TreeVertex d)) :
    ∃ E : Finset (TreeVertex d), D ⊆ E ∧ ConnectedFinset E :=
  ⟨ConnectedHull.hull D, ConnectedHull.subset_hull D, ConnectedHull.connected_hull D⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FreeLawUnique
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.finite_of_connected {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) : IsFiniteMeasure mu := by
  classical
  constructor
  have hmass := hmu.restrict_finset D hD Finset.univ
  rw [Finset.coe_univ, Measure.map_apply D.measurable_restrict MeasurableSet.univ,
    Set.preimage_univ] at hmass
  rw [hmass]
  exact ENNReal.sum_lt_top.mpr (fun eta _ => ENNReal.ofReal_lt_top)

theorem HasFreeIsingLaw.unique {d : ℕ} {theta : ℝ}
    {mu nu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hnu : HasFreeIsingLaw theta nu) : mu = nu := by
  let : Nonempty IsingSpin := ⟨IsingSpin.neg⟩
  let : IsFiniteMeasure mu :=
    hmu.finite_of_connected (ConnectedHull.hull ∅) (ConnectedHull.connected_hull ∅)
  apply measure_eq_of_cofinal_cylinders ConnectedFinset exists_connectedFinset_superset
  intro D hD eta
  exact (hmu D hD eta).trans (hnu D hD eta).symm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PlantedSymmetry
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.PlantedSymmetry

theorem measurable_observation {ι : Type*} (t : ℝ) :
    Measurable (observation (ι := ι) t) := by
  have hsign : Measurable spinSign := by intro s hs; trivial
  exact Measurable.of_eval (fun vertex =>
    ((hsign.comp ((measurable_pi_apply vertex).comp measurable_fst)).const_mul t).add
      ((measurable_pi_apply vertex).comp measurable_snd))

end Problem367.PlantedSymmetry

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

namespace ConnectedHull

theorem hull_mono {d : ℕ} : Monotone (@hull d) := by
  classical
  intro D E hDE v hv
  rcases Finset.mem_insert.mp hv with hroot | hv
  · exact Finset.mem_insert.mpr (Or.inl hroot)
  · obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨w, hDE hw, hvw⟩))

end ConnectedHull

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_PairedFiniteField
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

variable {I : Type*} [Fintype I] [Nonempty I]

def pairedEnergy (E F : I → ℝ) (s : IsingSpin × I) : ℝ :=
  match s.1 with
  | .neg => F s.2
  | .pos => E s.2

omit [Nonempty I] in

theorem paired_posterior_mean (E F : I → ℝ) (x : ℝ) :
    FinitePosterior.mean (pairedEnergy E F) (fun s => spinSign s.1)
      (fun s => spinSign s.1) x =
      (pairedFieldWeight E x - pairedFieldWeight F (-x)) /
        (pairedFieldWeight E x + pairedFieldWeight F (-x)) := by
  simp only [FinitePosterior.mean, FinitePosterior.partition, FinitePosterior.weight,
    Fintype.sum_prod_type, sum_isingSpin, pairedEnergy, spinSign_neg, spinSign_pos,
    mul_neg_one, mul_one, neg_one_mul, one_mul, Real.exp_add, Finset.sum_neg_distrib,
    ← Finset.sum_mul, pairedFieldWeight]
  ring

theorem paired_posterior_field_bound (E F : I → ℝ) (x K : ℝ)
    (h : ∀ i, |E i - F i| ≤ 2 * K) :
    |Real.artanh (FinitePosterior.mean (pairedEnergy E F) (fun s => spinSign s.1)
      (fun s => spinSign s.1) x) - x| ≤ K := by
  rw [paired_posterior_mean]
  exact paired_field_difference_bound E F x K h

end Problem367

namespace Problem367

theorem paired_posterior_field_bound_equiv {S I : Type*} [Fintype S] [Fintype I]
    [Nonempty I] (e : S ≃ IsingSpin × I) (energy : S → ℝ) (x K : ℝ)
    (h : ∀ i, |energy (e.symm (.pos, i)) - energy (e.symm (.neg, i))| ≤ 2 * K) :
    |Real.artanh (FinitePosterior.mean energy (fun s => spinSign (e s).1)
      (fun s => spinSign (e s).1) x) - x| ≤ K := by
  have hm := finitePosterior_mean_equiv e.symm energy
    (fun s => spinSign (e s).1) (fun s => spinSign (e s).1) x
  simp only [Function.comp_def, e.apply_symm_apply] at hm
  rw [← hm]
  have he : (fun s => energy (e.symm s)) =
      pairedEnergy (fun i => energy (e.symm (.pos, i)))
        (fun i => energy (e.symm (.neg, i))) := by
    funext s
    rcases s with ⟨s, i⟩
    cases s <;> rfl
  rw [he]
  exact paired_posterior_field_bound _ _ x K h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteGibbsField
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

variable {V : Type*} [Fintype V] [DecidableEq V]

def finiteInteractionEnergy (edges : Finset (V × V)) (beta : ℝ)
    (s : V → IsingSpin) : ℝ :=
  beta * ∑ e ∈ edges, spinSign (s e.1) * spinSign (s e.2)

def siteResidualEnergy (edges : Finset (V × V)) (beta : ℝ) (y : V → ℝ)
    (v : V) (s : V → IsingSpin) : ℝ :=
  finiteInteractionEnergy edges beta s +
    ∑ w ∈ Finset.univ.erase v, y w * spinSign (s w)

theorem finite_gibbs_fieldMean_eq (edges : Finset (V × V)) (beta : ℝ)
    (y : V → ℝ) (v : V) :
    FinitePosterior.fieldMean (finiteInteractionEnergy edges beta)
      (fun s w => spinSign (s w)) (fun s => spinSign (s v)) y =
      FinitePosterior.mean (siteResidualEnergy edges beta y v)
        (fun s => spinSign (s v)) (fun s => spinSign (s v)) (y v) := by
  have he (s : V → IsingSpin) :
      FinitePosterior.fieldEnergy (finiteInteractionEnergy edges beta)
        (fun s w => spinSign (s w)) y s =
        siteResidualEnergy edges beta y v s + y v * spinSign (s v) := by
    unfold FinitePosterior.fieldEnergy siteResidualEnergy
    rw [← Finset.sum_erase_add Finset.univ (fun w => y w * spinSign (s w))
      (Finset.mem_univ v)]
    ring
  simp only [FinitePosterior.fieldMean, FinitePosterior.mean, FinitePosterior.partition,
    FinitePosterior.weight, he]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_IncidentEdges
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem367

theorem card_incident_inducedEdges_le {d : ℕ} (D : Finset (TreeVertex d))
    (v : TreeVertex d) :
    ((inducedEdges D).filter (fun e => e.1 = v ∨ e.2 = v)).card ≤ d := by
  classical
  let f : TreeVertex d × TreeVertex d → TreeVertex d :=
    fun e => if e.1 = v then e.2 else e.1
  have hdata {e : TreeVertex d × TreeVertex d}
      (he : e ∈ (inducedEdges D).filter (fun e => e.1 = v ∨ e.2 = v)) :
      (treeAdj e.1 e.2 ∧ e.1.1.length < e.2.1.length) ∧
        (e.1 = v ∨ e.2 = v) := by
    obtain ⟨he, hv⟩ := Finset.mem_filter.mp he
    exact ⟨(Finset.mem_filter.mp he).2, hv⟩
  refine le_trans ?_ (Nat.le_of_eq (card_treeNeighborFinset v))
  apply Finset.card_le_card_of_injOn f
  · intro e he
    obtain ⟨⟨hadj, _⟩, hinc⟩ := hdata he
    change f e ∈ treeNeighborFinset v
    rw [mem_treeNeighborFinset]
    by_cases h : e.1 = v
    · simpa [f, h] using hadj
    · have h2 : e.2 = v := hinc.resolve_left h
      simpa [f, h, h2, treeAdj] using Or.symm hadj
  · rintro ⟨a, b⟩ he ⟨c, z⟩ he' h
    obtain ⟨⟨_, hab⟩, habv⟩ := hdata he
    obtain ⟨⟨_, hcz⟩, hczv⟩ := hdata he'
    change a.1.length < b.1.length at hab
    change c.1.length < z.1.length at hcz
    change a = v ∨ b = v at habv
    change c = v ∨ z = v at hczv
    by_cases ha : a = v
    · subst a
      by_cases hc : c = v
      · subst c
        have hbz : b = z := by simpa [f] using h
        exact Prod.ext rfl hbz
      · have hz : z = v := hczv.resolve_left hc
        subst z
        have hbc : b = c := by simpa [f, hc] using h
        subst c
        omega
    · have hb : b = v := habv.resolve_left ha
      subst b
      by_cases hc : c = v
      · subst c
        have haz : a = z := by simpa [f, ha] using h
        subst z
        omega
      · have hz : z = v := hczv.resolve_left hc
        subst z
        have hac : a = c := by simpa [f, ha, hc] using h
        exact Prod.ext hac rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_GibbsField
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def finiteTreeEdges {d : ℕ} (D : Finset (TreeVertex d)) : Finset (D × D) := by
  classical
  exact Finset.univ.filter (fun e => (e.1.1, e.2.1) ∈ inducedEdges D)

theorem pair_val_injective {d : ℕ} (D : Finset (TreeVertex d)) :
    Function.Injective (fun e : D × D => (e.1.1, e.2.1)) := by
  intro e f h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

theorem finiteTreeEdges_image {d : ℕ} (D : Finset (TreeVertex d)) :
    (finiteTreeEdges D).image (fun e => (e.1.1, e.2.1)) = inducedEdges D := by
  classical
  ext e
  constructor
  · rintro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    simpa [finiteTreeEdges] using hf
  · intro he
    have heD : e.1 ∈ D ∧ e.2 ∈ D := by
      have hm := (Finset.mem_filter.mp he).1
      exact Finset.mem_product.mp hm
    refine Finset.mem_image.mpr ⟨(⟨e.1, heD.1⟩, ⟨e.2, heD.2⟩), ?_, rfl⟩
    simpa [finiteTreeEdges] using he

theorem finiteTreeEdges_incident_card {d : ℕ} (D : Finset (TreeVertex d)) (v : D) :
    ((finiteTreeEdges D).filter (fun e => e.1 = v ∨ e.2 = v)).card =
      ((inducedEdges D).filter (fun e => e.1 = v.1 ∨ e.2 = v.1)).card := by
  classical
  have he : (inducedEdges D).filter (fun e => e.1 = v.1 ∨ e.2 = v.1) =
      ((finiteTreeEdges D).filter (fun e => e.1 = v ∨ e.2 = v)).image
        (fun e => (e.1.1, e.2.1)) := by
    rw [← finiteTreeEdges_image D, Finset.filter_image]
    congr 1
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, h | h⟩
      · exact ⟨he, Or.inl (Subtype.ext h)⟩
      · exact ⟨he, Or.inr (Subtype.ext h)⟩
    · rintro ⟨he, h | h⟩
      · exact ⟨he, Or.inl (congrArg Subtype.val h)⟩
      · exact ⟨he, Or.inr (congrArg Subtype.val h)⟩
  rw [he, Finset.card_image_of_injective _ (pair_val_injective D)]

theorem finiteInteractionEnergy_tree {d : ℕ} (D : Finset (TreeVertex d))
    (beta : ℝ) (eta : D → IsingSpin) :
    finiteInteractionEnergy (finiteTreeEdges D) beta eta =
      beta * ∑ e ∈ inducedEdges D,
        spinSign (extendFiniteSpin D eta e.1) * spinSign (extendFiniteSpin D eta e.2) := by
  classical
  rw [finiteInteractionEnergy, ← finiteTreeEdges_image D,
    Finset.sum_image (pair_val_injective D).injOn]
  simp

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_InfinitePosteriorField
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
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

local instance infinitePosteriorFieldNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

def finiteObservation {d : ℕ} (D : Finset (TreeVertex d)) (t : ℝ≥0)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) : D → ℝ :=
  D.restrict (observation t p)

theorem measurable_finiteObservation {d : ℕ} (D : Finset (TreeVertex d)) (t : ℝ≥0) :
    Measurable (finiteObservation D t) :=
  D.measurable_restrict.comp (measurable_observation t)

theorem gaussianPlanted_restrict_joint_law {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (D : Finset (TreeVertex d)) (t : ℝ≥0) :
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map
      (fun p => (D.restrict p.1, finiteObservation D t p)) =
      (μ.map D.restrict) ⊗ₘ finiteGaussianObservationKernel t
        (fun (eta : D → IsingSpin) v => spinSign (eta v)) := by
  let R : ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) →
      (D → IsingSpin) × (D → ℝ) := Prod.map D.restrict D.restrict
  have hR : Measurable R := D.measurable_restrict.prodMap D.measurable_restrict
  have hRlaw : (μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map R =
      (μ.map D.restrict).prod (Measure.pi (fun _ : D => gaussianReal 0 t)) := by
    simpa only [R, gaussianNoiseLaw, Measure.infinitePi_map_restrict] using
      (Measure.map_prod_map μ (gaussianNoiseLaw (TreeVertex d) t)
        D.measurable_restrict D.measurable_restrict).symm
  let F : (D → IsingSpin) × (D → ℝ) → (D → IsingSpin) × (D → ℝ) :=
    fun p => (p.1, fun v => (t : ℝ) * spinSign (p.1 v) + p.2 v)
  have hF : Measurable F := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro v
    exact (measurable_const.mul
      ((measurable_of_finite spinSign).comp ((measurable_pi_apply v).comp measurable_fst))).add
      ((measurable_pi_apply v).comp measurable_snd)
  have : IsProbabilityMeasure (μ.map D.restrict) := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  calc
    _ = ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map R).map F := by
      rw [Measure.map_map hF hR]
      rfl
    _ = _ := by
      rw [hRlaw]
      exact finiteGaussianPlanted_joint_law (μ.map D.restrict) t
        (fun (eta : D → IsingSpin) v => spinSign (eta v))

theorem HasFreeIsingLaw.finiteObservation_condExp {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0)
    (q : (D → IsingSpin) → ℝ) :
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
      fun p => q (D.restrict p.1) |
      MeasurableSpace.comap (finiteObservation D t) inferInstance] =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) v => spinSign (eta v)) q (finiteObservation D t p) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure (μ.map D.restrict) := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact FiniteBayes.condExp_state_eq_of_posterior_integral
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (μ.map D.restrict)
    (finiteGaussianObservationKernel t (fun (eta : D → IsingSpin) v => spinSign (eta v)))
    (fun p => D.restrict p.1) (finiteObservation D t)
    (D.measurable_restrict.comp measurable_fst) (measurable_finiteObservation D t)
    (gaussianPlanted_restrict_joint_law μ D t) q _
    (hμ.gaussian_restrict_posterior_mean D hD t q)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_FieldL2Limit
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367

open PlantedSymmetry

namespace CavityFieldLimit

local instance instNonemptyIsingSpin_rbb8cb6_1 : Nonempty IsingSpin := ⟨.neg⟩
def finiteSiteField {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d))
    (v : D) (y : TreeVertex d → ℝ) : ℝ :=
  Real.artanh (FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta v)) (D.restrict y))

def finiteCavityField {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (v w : D) (y : TreeVertex d → ℝ) : ℝ :=
  (cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
    (finiteSiteField beta D v y, finiteSiteField beta D w y)).1

def infiniteCavityField {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (v w : TreeVertex d) (y : TreeVertex d → ℝ) : ℝ :=
  CavityArray.field (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
    (fun u => Real.artanh (infiniteGibbsSpinMean beta u y)) v w

end CavityFieldLimit

open CavityFieldLimit

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CenteredCopyDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.CopyDifference

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ]
variable {p q : B → A}

section Averaging

variable {ι : Type*} [Fintype ι]

omit [IsProbabilityMeasure μ] in

lemma average_intertwines_apply
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (τ : ι → A → A) (σ : ι → B → B)
    (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hσ : ∀ i, MeasurePreserving (σ i) ν ν)
    (hpc : ∀ i, p ∘ σ i = τ i ∘ p) (hqc : ∀ i, q ∘ σ i = τ i ∘ q)
    (f : Lp ℝ 2 μ) :
    koopmanAverage σ hσ (operator hp hq f) = operator hp hq (koopmanAverage τ hτ f) := by
  simp only [koopmanAverage, smul_apply, sum_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν => L f)
    (intertwines hp hq (hτ i) (hσ i) (hpc i) (hqc i))

def averageOnDifferences
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (τ : ι → A → A) (σ : ι → B → B)
    (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hσ : ∀ i, MeasurePreserving (σ i) ν ν)
    (hpc : ∀ i, p ∘ σ i = τ i ∘ p) (hqc : ∀ i, q ∘ σ i = τ i ∘ q) :
    rangeClosure (operator hp hq) →L[ℝ] rangeClosure (operator hp hq) :=
  restrictToRangeClosure (operator hp hq) (koopmanAverage τ hτ) (koopmanAverage σ hσ)
    (average_intertwines_apply hp hq τ σ hτ hσ hpc hqc)

end Averaging

end Problem367.CopyDifference

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_GaussianVector
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeShellFinite
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

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem map_restrict_eq_smul_of_condExp_inner_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → H} (hX : Measurable[mΩ] X)
    (ν : Measure H) [IsProbabilityMeasure ν]
    (hchar : ∀ t : H,
      P[(fun ω => Complex.exp ((⟪X ω, t⟫ : ℝ) * Complex.I)) | m] =ᵐ[P]
        fun _ => charFun ν t)
    {s : Set Ω} (hs : MeasurableSet[m] s) :
    Measure.map X (P.restrict s) = P s • ν := by
  let : IsFiniteMeasure (P s • ν) := ν.smul_finite (measure_ne_top P s)
  apply Measure.ext_of_charFun
  funext t
  have hi : Integrable (fun ω => Complex.exp ((⟪X ω, t⟫ : ℝ) * Complex.I)) P := by
    have hi := ConditionalCharacteristic.integrable_character (P := P)
      (show Measurable (fun ω => ⟪X ω, t⟫) by fun_prop) 1
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    simp [ConditionalCharacteristic.character]
  rw [charFun_apply, integral_map hX.aemeasurable (by fun_prop),
    charFun_apply, integral_smul_measure]
  rw [← setIntegral_condExp hm hi hs]
  calc
    (∫ ω in s, P[(fun ω => Complex.exp ((⟪X ω, t⟫ : ℝ) * Complex.I)) | m] ω ∂P) =
        ∫ _ in s, charFun ν t ∂P :=
      integral_congr_ae (ae_restrict_of_ae (hchar t))
    _ = _ := by simp [charFun_apply, measureReal_def]

theorem law_and_indep_of_condExp_inner_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → H} (hX : Measurable[mΩ] X)
    (ν : Measure H) [IsProbabilityMeasure ν]
    (hchar : ∀ t : H,
      P[(fun ω => Complex.exp ((⟪X ω, t⟫ : ℝ) * Complex.I)) | m] =ᵐ[P]
        fun _ => charFun ν t)
    {E : Type*} [MeasurableSpace E] {Y : Ω → E} (hY : Measurable[m] Y) :
    HasLaw X ν P ∧ IndepFun X Y P := by
  have hlaw : Measure.map X P = ν := by
    simpa using map_restrict_eq_smul_of_condExp_inner_character hm hX ν hchar
      (MeasurableSet.univ : MeasurableSet[m] Set.univ)
  refine ⟨⟨hX.aemeasurable, hlaw⟩, ?_⟩
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro a b ha hb
  have hrestrict := congrArg (fun μ : Measure H => μ a)
    (map_restrict_eq_smul_of_condExp_inner_character hm hX ν hchar (hY hb))
  rw [Measure.map_apply hX ha, Measure.restrict_apply (hX ha),
    Measure.smul_apply, smul_eq_mul, ← hlaw, Measure.map_apply hX ha] at hrestrict
  exact hrestrict.trans (mul_comm _ _)

end Hilbert

section FiniteVector

variable {ι : Type*} [Fintype ι]

theorem product_gaussian_law_and_indep_of_condExp_linear_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → ι → ℝ} (hX : Measurable[mΩ] X)
    (v : ι → ℝ≥0)
    (hchar : ∀ a : ι → ℝ,
      P[(fun ω => Complex.exp (((∑ i, a i * X ω i : ℝ) : ℂ) * Complex.I)) | m] =ᵐ[P]
        fun _ => Complex.exp (-((∑ i, (v i : ℝ) * (a i) ^ 2 : ℝ) : ℂ) / 2))
    {E : Type*} [MeasurableSpace E] {Y : Ω → E} (hY : Measurable[m] Y) :
    HasLaw X (Measure.pi (fun i => gaussianReal 0 (v i))) P ∧ IndepFun X Y P := by
  let Z : Ω → EuclideanSpace ℝ ι := fun ω => WithLp.toLp 2 (X ω)
  let ν : Measure (EuclideanSpace ℝ ι) :=
    (Measure.pi (fun i => gaussianReal 0 (v i))).map (WithLp.toLp 2)
  have hZ : Measurable Z := (WithLp.measurable_toLp 2 _).comp hX
  have hν : IsProbabilityMeasure ν := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hc : ∀ t : EuclideanSpace ℝ ι,
      P[(fun ω => Complex.exp ((⟪Z ω, t⟫ : ℝ) * Complex.I)) | m] =ᵐ[P]
        fun _ => charFun ν t := by
    intro t
    simpa only [Z, ν, PiLp.inner_apply, WithLp.ofLp_toLp, Real.inner_apply, mul_comm,
      charFun_product_gaussian] using hchar t.ofLp
  obtain ⟨hlaw, hind⟩ := law_and_indep_of_condExp_inner_character hm hZ ν hc hY
  constructor
  · refine ⟨hX.aemeasurable, ?_⟩
    apply (MeasurableEquiv.toLp 2 (ι → ℝ)).map_measurableEquiv_injective
    change (P.map X).map (WithLp.toLp 2) = ν
    rw [Measure.map_map (WithLp.measurable_toLp 2 _) hX]
    exact hlaw.map_eq
  · simpa only [Function.comp_def, Z, WithLp.ofLp_toLp, id_eq] using
      hind.comp (WithLp.measurable_ofLp 2 (ι → ℝ)) measurable_id

end FiniteVector

end Problem367.ConditionalGaussianVector

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_PlantedBrownianLinearCombination
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

lemma iIndepFun_comp_measurePreserving
    {ι Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {r : Ω → Ω'} (hr : MeasurePreserving r μ ν)
    {f : ι → Ω' → E} (hf : ∀ i, Measurable (f i)) (hind : iIndepFun f ν) :
    iIndepFun (fun i => f i ∘ r) μ := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i => (hf i).comp hr.measurable)).2
  have h := hind.map_fun_eq_infinitePi_map hf
  rw [← hr.map_eq] at h
  simpa only [Measure.map_map (Measurable.of_eval hf) hr.measurable,
    Measure.map_map (hf _) hr.measurable, Function.comp_def] using h

theorem planted_coordinate_paths_iIndepFun
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    [∀ i, IsProbabilityMeasure (μ i)]
    {B : ι → ℝ≥0 → Ω → ℝ} (hmB : ∀ i t, Measurable (B i t)) :
    iIndepFun (fun i (q : S × (ι → Ω)) t => B i t (q.2 i))
      (ν.prod (Measure.infinitePi μ)) := by
  have hm (i : ι) : Measurable (fun ω t => B i t ω) :=
    Measurable.of_eval (hmB i)
  exact iIndepFun_comp_measurePreserving measurePreserving_snd
    (fun i => (hm i).comp (measurable_pi_apply i)) (iIndepFun_infinitePi hm)

theorem planted_finite_projection_preBrownian
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) (I : Finset ι) (a : ι → ℝ)
    (ha : ∑ i ∈ I, a i ^ 2 = 1) :
    IsPreBrownianReal (fun t (q : S × (ι → Ω)) => ∑ i ∈ I, a i * B i t (q.2 i))
      (ν.prod (Measure.infinitePi μ)) := by
  classical
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hind := (planted_coordinate_paths_iIndepFun ν μ hmB).precomp
    (show Function.Injective (fun i : I => (i : ι)) from Subtype.val_injective)
  have h := BrownianLinearCombination.isPreBrownianReal_sum
    (fun i : I => planted_coordinate_preBrownian ν μ hB i) hind
    (fun i : I => a i) (by rw [Finset.sum_coe_sort I (fun i => a i ^ 2)]; exact ha)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext t q
  exact (Finset.sum_coe_sort I (fun i => a i * B i t (q.2 i))).symm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ArrayInnovationProjection
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Problem367.ConditionalCharacteristic

namespace Problem367

theorem array_innovation_unit_projection_setIntegral_character
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ)
    {C : ℝ≥0} (hσbound : ∀ i, ∀ᵐ s ∂ν, |σ s i| ≤ (C : ℝ))
    {m : ι → ℝ≥0 → S × (ι → Ω) → ℝ}
    (hm : ∀ i, IsStronglyProgressive (arrayObservationFiltration B hmB σ hσ) (m i))
    (hposterior : ∀ i t, m i t =ᵐ[ν.prod (Measure.infinitePi μ)]
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ t])
    (I : Finset ι) (a : ι → ℝ) (ha : ∑ i ∈ I, a i ^ 2 = 1)
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set (S × (ι → Ω))}
    (hA : MeasurableSet[arrayObservationFiltration B hmB σ hσ s] A) (u : ℝ) :
    (∫ q in A, character (fun q => ∑ i ∈ I, a i *
      ((plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q) -
        (plantedArrayObservation B σ i s q - nnrealTimePrimitive (m i) s q))) u q
          ∂ν.prod (Measure.infinitePi μ)) =
      (ν.prod (Measure.infinitePi μ)).real A *
        Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * (u : ℂ)^2 / 2) := by
  classical
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := ν.prod (Measure.infinitePi μ)
  let F := arrayObservationFiltration B hmB σ hσ
  let W : ℝ≥0 → S × (ι → Ω) → ℝ := fun t q => ∑ i ∈ I, a i *
    (plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q)
  let N : ℝ≥0 → S × (ι → Ω) → ℝ := fun t q => ∑ i ∈ I, a i * B i t (q.2 i)
  have hN : IsPreBrownianReal N P :=
    planted_finite_projection_preBrownian ν μ hB hmB I a ha
  have hW : Martingale W F P := by
    have h := BrownianLinearCombination.martingale_sum F
      (fun i : I => preBrownian_array_innovation_martingale_of_progressive_posterior
        ν μ hB hmB hσ i (hσbound i) (hm i) (hposterior i)) (fun i : I => a i)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext t q
    exact (Finset.sum_coe_sort I (fun i => a i *
      (plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q))).symm
  have hvariance : ∀ r v : ℝ≥0, r ≤ v →
      P[(fun q => (N v q - N r q)^2) | F r] =ᵐ[P]
        fun _ => (v : ℝ) - (r : ℝ) := by
    intro r v hrv
    have h := planted_weighted_increment_sq_condExp_subfield ν μ hB hmB hrv I a
      (arrayObservationFiltration_le_signalArrayFiltration B hmB σ hσ r)
    simpa only [N, P, F, mul_sub, Finset.sum_sub_distrib, ha, mul_one] using h
  have hbound : ∀ r v : ℝ≥0, r ≤ v → ∀ᵐ q ∂P,
      |(W v q - W r q) - (N v q - N r q)| ≤
        (2 * (C : ℝ) * ∑ i ∈ I, |a i|) * ((v : ℝ) - (r : ℝ)) := by
    intro r v hrv
    have hcoords : ∀ᵐ q ∂P, ∀ i : I,
        |((plantedArrayObservation B σ i v q - nnrealTimePrimitive (m i) v q) -
            (plantedArrayObservation B σ i r q - nnrealTimePrimitive (m i) r q)) -
          (B i v (q.2 i) - B i r (q.2 i))| ≤
          (2 * (C : ℝ)) * ((v : ℝ) - (r : ℝ)) :=
      ae_all_iff.mpr fun i => ae_array_innovation_increment_drift_bound
        ν μ hmB hσ i (hσbound i) (hm i) (hposterior i) hrv
    filter_upwards [hcoords] with q hq
    let D : ι → ℝ := fun i =>
      ((plantedArrayObservation B σ i v q - nnrealTimePrimitive (m i) v q) -
        (plantedArrayObservation B σ i r q - nnrealTimePrimitive (m i) r q)) -
          (B i v (q.2 i) - B i r (q.2 i))
    have heq : (W v q - W r q) - (N v q - N r q) = ∑ i ∈ I, a i * D i := by
      simp only [W, N, D, mul_sub, Finset.sum_sub_distrib]
    rw [heq]
    calc
      |∑ i ∈ I, a i * D i| ≤ ∑ i ∈ I, |a i * D i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ I, |a i| * |D i| := by simp only [abs_mul]
      _ ≤ ∑ i ∈ I, |a i| * ((2 * (C : ℝ)) * ((v : ℝ) - (r : ℝ))) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hq ⟨i, hi⟩) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have h := BrownianInnovation.setIntegral_character_of_bounded_drift hN hW hvariance
    (by positivity : 0 ≤ 2 * (C : ℝ) * ∑ i ∈ I, |a i|) hbound hst hA u
  simpa only [W, mul_sub, Finset.sum_sub_distrib] using h

theorem array_innovation_unit_projection_condExp_character
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ)
    {C : ℝ≥0} (hσbound : ∀ i, ∀ᵐ s ∂ν, |σ s i| ≤ (C : ℝ))
    {m : ι → ℝ≥0 → S × (ι → Ω) → ℝ}
    (hm : ∀ i, IsStronglyProgressive (arrayObservationFiltration B hmB σ hσ) (m i))
    (hposterior : ∀ i t, m i t =ᵐ[ν.prod (Measure.infinitePi μ)]
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ t])
    (I : Finset ι) (a : ι → ℝ) (ha : ∑ i ∈ I, a i ^ 2 = 1)
    {s t : ℝ≥0} (hst : s ≤ t) (u : ℝ) :
    (ν.prod (Measure.infinitePi μ))[character (fun q => ∑ i ∈ I, a i *
      ((plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q) -
        (plantedArrayObservation B σ i s q - nnrealTimePrimitive (m i) s q))) u |
          arrayObservationFiltration B hmB σ hσ s] =ᵐ[ν.prod (Measure.infinitePi μ)]
      fun _ => Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * (u : ℂ)^2 / 2) := by
  classical
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hW (i : ι) (r : ℝ≥0) : Measurable (fun q =>
      plantedArrayObservation B σ i r q - nnrealTimePrimitive (m i) r q) :=
    ((preBrownian_array_innovation_martingale_of_progressive_posterior
      ν μ hB hmB hσ i (hσbound i) (hm i) (hposterior i)).stronglyMeasurable r).mono
        ((arrayObservationFiltration B hmB σ hσ).le r) |>.measurable
  apply BrownianCharacterization.condExp_character_of_setIntegral
    ((arrayObservationFiltration B hmB σ hσ).le s)
  · exact Finset.measurable_sum I fun i _ => ((hW i t).sub (hW i s)).const_mul (a i)
  · intro A hA
    exact array_innovation_unit_projection_setIntegral_character
      ν μ hB hmB hσ hσbound hm hposterior I a ha hst hA u

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_ArrayCharacterization
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianArrayCharacterization

open ConditionalCharacteristic ConditionalGaussianVector

theorem gaussianPi_law_and_indep_of_weighted_characters
    {ι Ω : Type*} [Fintype ι] {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    {X : Ω → ι → ℝ} (hX : Measurable X) (v : ι → ℝ≥0)
    (hchar : ∀ a : ι → ℝ,
      P[character (fun ω => ∑ i, a i * X ω i) 1 | m] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i, ((v i : ℝ) : ℂ) * (a i : ℂ)^2) / 2))
    {E : Type*} [MeasurableSpace E] {Y : Ω → E} (hY : Measurable[m] Y) :
    HasLaw X (Measure.pi (fun i => gaussianReal 0 (v i))) P ∧ IndepFun X Y P := by
  apply product_gaussian_law_and_indep_of_condExp_linear_character hm hX v _ hY
  intro a
  have hc : character (fun ω => ∑ i, a i * X ω i) 1 =
      fun ω => Complex.exp (((∑ i, a i * X ω i : ℝ) : ℂ) * Complex.I) := by
    funext ω
    simp [character]
  have h := hchar a
  rw [hc] at h
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow] using h

theorem isGaussianProcess_vector_of_conditional_weighted_characters
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ι → ℝ} (F : Filtration ℝ≥0 mΩ) (hX : Adapted F X)
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hchar : ∀ s t : ℝ≥0, s ≤ t → ∀ a : ι → ℝ,
      P[character (fun ω => ∑ i, a i * (X t ω i - X s ω i)) 1 | F s] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2)) :
    IsGaussianProcess X P := by
  have hm (s t : ℝ≥0) : Measurable (fun ω => X t ω - X s ω) :=
    hX.measurable.sub hX.measurable
  have hlaw (s t : ℝ≥0) (hst : s ≤ t) :
      HasLaw (fun ω => X t ω - X s ω)
        (Measure.pi (fun _ : ι => gaussianReal 0 (t - s))) P :=
    (gaussianPi_law_and_indep_of_weighted_characters (F.le s) (hm s t)
      (fun _ : ι => t - s) (hchar s t hst)
      (measurable_const : Measurable[F s] (fun _ : Ω => ()))).1
  have hi : HasIndepIncrements X P := by
    apply BrownianCharacterization.hasIndepIncrements_of_past_events_general F hX
    intro s t hst A hA S hS
    let Y : Ω → ℝ := A.indicator (fun _ => 1)
    have hY : Measurable[F s] Y := measurable_const.indicator hA
    have hind := (gaussianPi_law_and_indep_of_weighted_characters
      (F.le s) (hm s t) (fun _ : ι => t - s) (hchar s t hst) hY).2
    have hAe : Y ⁻¹' {1} = A := by
      ext ω
      by_cases hω : ω ∈ A <;> simp [Y, hω]
    have hh := (indepFun_iff_measure_inter_preimage_eq_mul.mp hind)
      S {1} hS (measurableSet_singleton 1)
    simpa only [hAe, Set.inter_comm, mul_comm] using hh
  apply hi.isGaussianProcess _ hzero
  change ∀ t : ℝ≥0, HasGaussianLaw (X t) P
  intro t
  have hg : HasGaussianLaw (id : (ι → ℝ) → (ι → ℝ))
      (Measure.pi (fun _ : ι => gaussianReal 0 (t - 0))) :=
    (iIndepFun_pi (X := fun _ : ι => id) (fun _ => aemeasurable_id)).hasGaussianLaw
      (fun i => (measurePreserving_eval (fun _ : ι => gaussianReal 0 (t - 0)) i).hasLaw.hasGaussianLaw)
  have : IsGaussian (Measure.pi (fun _ : ι => gaussianReal 0 (t - 0))) := by
    simpa only [Measure.map_id] using hg.isGaussian_map
  apply (hlaw 0 t bot_le).hasGaussianLaw.congr
  filter_upwards [hzero] with ω hω
  simp [hω]

theorem isGaussianProcess_array_of_conditional_finite_characters
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ι → ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : ∀ i, Adapted F (B i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, B i 0 ω = 0)
    (hchar : ∀ (I : Finset ι) (s t : ℝ≥0), s ≤ t → ∀ a : I → ℝ,
      P[character (fun ω => ∑ i : I, a i * (B i t ω - B i s ω)) 1 | F s] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i : I, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2)) :
    IsGaussianProcess (fun p : (_ : ι) × ℝ≥0 => B p.1 p.2) P := by
  classical
  apply isGaussianProcess_array_of_finite_coordinate_processes
  intro I
  apply isGaussianProcess_vector_of_conditional_weighted_characters F
  · intro t
    let : MeasurableSpace Ω := F t
    exact Measurable.of_eval (fun index : I => hB index t)
  · have hz : ∀ᵐ ω ∂P, ∀ i : I, B i 0 ω = 0 := ae_all_iff.mpr (fun i => hzero i)
    filter_upwards [hz] with ω hω
    exact funext hω
  · exact hchar I

theorem conditional_character_coordinate
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ι → ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hchar : ∀ (I : Finset ι) (s t : ℝ≥0), s ≤ t → ∀ a : I → ℝ,
      P[character (fun ω => ∑ i : I, a i * (B i t ω - B i s ω)) 1 | F s] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i : I, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2))
    (i : ι) (s t : ℝ≥0) (hst : s ≤ t) (u : ℝ) :
    P[character (fun ω => B i t ω - B i s ω) u | F s] =ᵐ[P]
      fun _ => charFun (gaussianReal 0 (t - s)) u := by
  classical
  have h := hchar {i} s t hst (fun _ => u)
  have hc : character (fun ω => u * (B i t ω - B i s ω)) 1 =
      character (fun ω => B i t ω - B i s ω) u := by
    funext ω
    simp [character, Complex.ofReal_mul]
  simpa [hc, charFun_gaussianReal, neg_div] using h

theorem preBrownian_coordinate_of_conditional_finite_characters
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ι → ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : ∀ i, Adapted F (B i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, B i 0 ω = 0)
    (hchar : ∀ (I : Finset ι) (s t : ℝ≥0), s ≤ t → ∀ a : I → ℝ,
      P[character (fun ω => ∑ i : I, a i * (B i t ω - B i s ω)) 1 | F s] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i : I, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2))
    (i : ι) : IsPreBrownianReal (B i) P := by
  classical
  exact BrownianCharacterization.isPreBrownianReal_of_conditional_charFun
    F (hB i).stronglyAdapted (hzero i) (conditional_character_coordinate F hchar i)

theorem law_finite_coordinates_of_conditional_finite_characters
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ι → ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : ∀ i, Adapted F (B i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, B i 0 ω = 0)
    (hchar : ∀ (I : Finset ι) (s t : ℝ≥0), s ≤ t → ∀ a : I → ℝ,
      P[character (fun ω => ∑ i : I, a i * (B i t ω - B i s ω)) 1 | F s] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i : I, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2))
    (I : Finset ι) (t : ℝ≥0) :
    HasLaw (fun ω (i : I) => B i t ω)
      (Measure.pi (fun _ : I => gaussianReal 0 t)) P := by
  classical
  have hm : Measurable (fun ω (i : I) => B i t ω - B i 0 ω) :=
    Measurable.of_eval (fun index => (hB index).measurable.sub (hB index).measurable)
  have hh := (gaussianPi_law_and_indep_of_weighted_characters
    (F.le 0) hm (fun _ : I => t - 0) (hchar I 0 t bot_le)
    (measurable_const : Measurable[F 0] (fun _ : Ω => ()))).1
  simp only [tsub_zero] at hh
  apply hh.congr
  have hz : ∀ᵐ ω ∂P, ∀ i : I, B i 0 ω = 0 := ae_all_iff.mpr (fun i => hzero i)
  filter_upwards [hz] with ω hω
  funext i
  simp [hω i]

theorem crossCovariance_of_conditional_finite_characters
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ι → ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : ∀ i, Adapted F (B i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, B i 0 ω = 0)
    (hchar : ∀ (I : Finset ι) (s t : ℝ≥0), s ≤ t → ∀ a : I → ℝ,
      P[character (fun ω => ∑ i : I, a i * (B i t ω - B i s ω)) 1 | F s] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i : I, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2)) :
    ∀ i j, i ≠ j → ∀ s t, cov[B i s, B j t; P] = 0 := by
  classical
  have hb (i : ι) := preBrownian_coordinate_of_conditional_finite_characters F hB hzero hchar i
  have hL2 (i : ι) (t : ℝ≥0) : MemLp (B i t) 2 P :=
    (hb i).isGaussianProcess.hasGaussianLaw_eval t |>.memLp_two
  have hsame (i j : ι) (hij : i ≠ j) (t : ℝ≥0) : cov[B i t, B j t; P] = 0 := by
    let I : Finset ι := {i, j}
    let ii : I := ⟨i, by simp [I]⟩
    let jj : I := ⟨j, by simp [I]⟩
    have hne : ii ≠ jj := fun h => hij (congrArg Subtype.val h)
    exact covariance_coordinate_ne_of_gaussianPi_law (fun _ : I => t)
      (law_finite_coordinates_of_conditional_finite_characters F hB hzero hchar I t)
      ii jj hne
  have hordered (i j : ι) (hij : i ≠ j) (s t : ℝ≥0) (hst : s ≤ t) :
      cov[B i s, B j t; P] = 0 := by
    have hi : IndepFun (fun ω => B j t ω - B j s ω) (B i s) P :=
      indepFun_of_condExp_character (F.le s)
        ((hB j).measurable.sub (hB j).measurable) (gaussianReal 0 (t - s))
        (conditional_character_coordinate F hchar j s t hst) (hB i s)
    change IndepFun (B j t - B j s) (B i s) P at hi
    have heq : B j t = (B j t - B j s) + B j s := by
      funext ω
      simp
    rw [heq, covariance_add_right (hL2 i s) ((hL2 j t).sub (hL2 j s)) (hL2 j s),
      hi.symm.covariance_eq_zero (hL2 i s) ((hL2 j t).sub (hL2 j s)), hsame i j hij s,
      add_zero]
  intro i j hij s t
  rcases le_total s t with hst | hts
  · exact hordered i j hij s t hst
  · rw [covariance_comm]
    exact hordered j i hij.symm t s hts

end Problem367.GaussianArrayCharacterization

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

theorem coordinate_isBrownianReal :
    IsBrownianReal (fun t (f : Path) => f t) wienerMeasure :=
  (Classical.choose_spec exists_wienerMeasure).2

end Problem367.WienerSampler

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ArrayInnovationLaw
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.innovationPath_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
open Problem367.ConditionalCharacteristic

namespace Problem367.ArrayInnovationLaw

variable {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
  (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
  {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
  (hmB : ∀ i t, Measurable (B i t))
  {σ : S → ι → ℝ} (hσ : Measurable σ)
  {C : ℝ≥0} (hσbound : ∀ i, ∀ᵐ s ∂ν, |σ s i| ≤ (C : ℝ))
  {m : ι → ℝ≥0 → S × (ι → Ω) → ℝ}
  (hm : ∀ i, IsStronglyProgressive (arrayObservationFiltration B hmB σ hσ) (m i))
  (hposterior : ∀ i t, m i t =ᵐ[ν.prod (Measure.infinitePi μ)]
    (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
      arrayObservationFiltration B hmB σ hσ t])

include hB hmB hσ hσbound hm hposterior

theorem conditional_weighted_character
    (I : Finset ι) (s t : ℝ≥0) (hst : s ≤ t) (a : I → ℝ) :
    (ν.prod (Measure.infinitePi μ))[character (fun q => ∑ i : I, a i *
      ((plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q) -
        (plantedArrayObservation B σ i s q - nnrealTimePrimitive (m i) s q))) 1 |
          arrayObservationFiltration B hmB σ hσ s] =ᵐ[ν.prod (Measure.infinitePi μ)]
      fun _ => Complex.exp (-(∑ i : I, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2) := by
  classical
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  apply ConditionalGaussianVector.condExp_weighted_character_of_unit_character
    ((arrayObservationFiltration B hmB σ hσ).le s) (t - s) _ a
  intro b hb u
  let c : ι → ℝ := fun i => if hi : i ∈ I then b ⟨i, hi⟩ else 0
  have hc (i : I) : c i = b i := by simp [c, i.property]
  have hcs : ∑ i ∈ I, c i ^ 2 = 1 := by
    rw [← Finset.sum_coe_sort I]
    simpa only [hc] using hb
  have h := array_innovation_unit_projection_condExp_character
    ν μ hB hmB hσ hσbound hm hposterior I c hcs hst u
  have heq : (fun q => ∑ i ∈ I, c i *
      ((plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q) -
        (plantedArrayObservation B σ i s q - nnrealTimePrimitive (m i) s q))) =
      (fun q => ∑ i : I, b i *
      ((plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q) -
        (plantedArrayObservation B σ i s q - nnrealTimePrimitive (m i) s q))) := by
    funext q
    rw [← Finset.sum_coe_sort I]
    simp only [hc]
  rw [heq] at h
  exact h

theorem isGaussianProcess_innovation_array :
    IsGaussianProcess (fun p : (_ : ι) × ℝ≥0 => fun q =>
      plantedArrayObservation B σ p.1 p.2 q - nnrealTimePrimitive (m p.1) p.2 q)
      (ν.prod (Measure.infinitePi μ)) := by
  classical
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  apply GaussianArrayCharacterization.isGaussianProcess_array_of_conditional_finite_characters
    (B := fun i t q => plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q)
    (P := ν.prod (Measure.infinitePi μ)) (arrayObservationFiltration B hmB σ hσ)
  · exact fun i => (preBrownian_array_innovation_martingale_of_progressive_posterior
      ν μ hB hmB hσ i (hσbound i) (hm i) (hposterior i)).stronglyAdapted.adapted
  · exact fun i => (preBrownian_array_innovation_of_progressive_posterior
      ν μ hB hmB hσ i (hσbound i) (hm i) (hposterior i)).eval_zero_ae_eq_zero
  · exact conditional_weighted_character ν μ hB hmB hσ hσbound hm hposterior

theorem exists_continuous_innovation_array_wiener_law
    (hcontinuous : ∀ i, ∀ᵐ ω ∂μ i, Continuous (fun t => B i t ω)) :
    ∃ X : ι → S × (ι → Ω) → WienerSampler.Path,
      (∀ i, Measurable (X i)) ∧
      (∀ i, ∀ᵐ q ∂ν.prod (Measure.infinitePi μ), ∀ t,
        X i q t = plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q) ∧
      (ν.prod (Measure.infinitePi μ)).map (fun q i => X i q) =
        Measure.infinitePi (fun _ : ι => WienerSampler.wienerMeasure) := by
  classical
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := ν.prod (Measure.infinitePi μ)
  let F := arrayObservationFiltration B hmB σ hσ
  let W : ι → ℝ≥0 → S × (ι → Ω) → ℝ := fun i t q =>
    plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q
  have hW (i : ι) : Martingale (W i) F P :=
    preBrownian_array_innovation_martingale_of_progressive_posterior
      ν μ hB hmB hσ i (hσbound i) (hm i) (hposterior i)
  have hpre (i : ι) : IsPreBrownianReal (W i) P :=
    preBrownian_array_innovation_of_progressive_posterior
      ν μ hB hmB hσ i (hσbound i) (hm i) (hposterior i)
  have hcont (i : ι) : ∀ᵐ q ∂P, Continuous (fun t => W i t q) :=
    (brownian_array_innovation_of_progressive_posterior
      ν μ (fun j => ⟨hB j, hcontinuous j⟩) hmB hσ i (hσbound i)
      (hm i) (hposterior i)).cont
  choose X hXm hXe using fun i => WienerSampler.exists_measurable_path_version
    P (W i) (fun t => ((hW i).stronglyMeasurable t).mono (F.le t) |>.measurable) (hcont i)
  refine ⟨X, hXm, hXe, ?_⟩
  have hcross := GaussianArrayCharacterization.crossCovariance_of_conditional_finite_characters
    F (fun i => (hW i).stronglyAdapted.adapted)
    (fun i => (hpre i).eval_zero_ae_eq_zero)
    (conditional_weighted_character ν μ hB hmB hσ hσbound hm hposterior)
  have hG : IsGaussianProcess (fun p : (_ : ι) × ℝ≥0 => W p.1 p.2) P :=
    isGaussianProcess_innovation_array ν μ hB hmB hσ hσbound hm hposterior
  have hi : iIndepFun (fun i q t => X i q t) P :=
    (iIndepFun_of_gaussianArray_crossCovariance hG hcross).congr (fun i => by
      filter_upwards [hXe i] with q hq
      exact funext (fun t => (hq t).symm))
  have hiX : iIndepFun X P := iIndepFun_continuousPaths_of_evaluations hi
  rw [hiX.map_fun_eq_infinitePi_map hXm]
  congr 1
  funext i
  have hpx : IsPreBrownianReal (fun t q => X i q t) P := (hpre i).congr (fun t => by
    filter_upwards [hXe i] with q hq
    exact (hq t).symm)
  simpa only [Measure.map_id] using map_continuousPreBrownian_eq (hXm i)
    (measurable_id : Measurable (id : WienerSampler.Path → WienerSampler.Path)) hpx
    WienerSampler.coordinate_isBrownianReal.toIsPreBrownianReal

end Problem367.ArrayInnovationLaw

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FieldCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ContDiff

namespace Problem367.FinitePosterior

variable {S : Type*} [Fintype S] [Nonempty S]

section Fields

variable {V : Type*} [Fintype V]

def fieldCovariance (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) : ℝ :=
  fieldMean energy spin (fun s => observable s * spin s v) x -
    fieldMean energy spin observable x * fieldMean energy spin (fun s => spin s v) x

def fieldMeanDerivative (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) : (V → ℝ) →L[ℝ] ℝ :=
  ∑ v, fieldCovariance energy spin observable x v • ContinuousLinearMap.proj v

def fieldField (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) : ℝ :=
  Real.artanh (fieldMean energy spin observable x)

def normalizedFieldCovariance (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) : ℝ :=
  fieldCovariance energy spin observable x v /
    (1 - fieldMean energy spin observable x ^ 2)

end Fields

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_GaussianGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Nonempty S] [Fintype V]

def fieldSquareGradient (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) : ℝ :=
  2 * fieldMean energy spin observable x * fieldCovariance energy spin observable x v

def fieldSquareHessianDiagonal (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) : ℝ :=
  2 * fieldCovariance energy spin observable x v ^ 2 -
    4 * fieldMean energy spin observable x * fieldMean energy spin (fun s => spin s v) x *
      fieldCovariance energy spin observable x v

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteIsingBrownianEnergy
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Problem367

local instance finiteIsingBrownianEnergyNonemptySpin_rbb8cb6_1 : Nonempty IsingSpin := ⟨.neg⟩
def finiteIsingBrownianObservation {d : ℕ} {Ω : Type*}
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (D : Finset (TreeVertex d))
    (t : ℝ) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : D → ℝ :=
  fun v => t * spinSign (p.1 v) + B v t.toNNReal (p.2 v)

def finiteIsingBrownianMean {d : ℕ} {Ω : Type*}
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : ℝ :=
  FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v))
    (finiteIsingBrownianObservation B D t p)

def finiteIsingBrownianCovariance {d : ℕ} {Ω : Type*}
    (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : ℝ :=
  FinitePosterior.fieldCovariance (finiteIsingEnergy beta D)
    (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v))
    (finiteIsingBrownianObservation B D t p) u

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FiniteIsingFilteringRepresentation
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.FiniteIsingFiltering

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

local instance finiteIsingFilteringNonemptySpin_rbb8cb6_1 : Nonempty IsingSpin := ⟨.neg⟩
abbrev State (d : ℕ) (Ω : Type*) :=
  (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)

def signal (sigma : TreeVertex d → IsingSpin) (i : TreeVertex d) : ℝ :=
  spinSign (sigma i)

lemma measurable_signal : Measurable (signal (d := d)) := by
  apply Measurable.of_eval
  intro i
  have hs : Measurable spinSign := by intro s hs; trivial
  exact hs.comp (measurable_pi_apply i)

def observationFiltration
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hmB : ∀ i t, Measurable (B i t)) (D : Finset (TreeVertex d)) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (State d Ω)) :=
  arrayNaturalFiltration (fun i : D => plantedArrayObservation B signal i)
    (fun i t => plantedArrayObservation_measurable hmB measurable_signal i t)

abbrev mean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) : ℝ :=
  finiteIsingBrownianMean beta D v B (t : ℝ) p

abbrev covariance (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) : ℝ :=
  finiteIsingBrownianCovariance beta D v u B (t : ℝ) p

end Problem367.FiniteIsingFiltering

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FilteringCrossEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

namespace Problem367.FilteringCrossEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

def innovation (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ) (m : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  B t ω + (t : ℝ) * S ω - nnrealTimePrimitive m t ω

end Problem367.FilteringCrossEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteIsingInnovation
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Problem367.ConditionalCharacteristic

namespace Problem367.FiniteIsingFiltering

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

def innovation (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) : ℝ :=
  plantedArrayObservation B signal v t p - nnrealTimePrimitive (mean beta D v B) t p

end Problem367.FiniteIsingFiltering

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteIsingCompensatedSquare
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Problem367.FiniteIsingFiltering

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

def quadraticCompensator (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) : ℝ :=
  ∑ u : D, ∫ r in (0 : ℝ)..(t : ℝ), covariance beta D v u B r.toNNReal p ^ 2

end Problem367.FiniteIsingFiltering

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteSpinCoupling
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FiniteSpinCoupling

variable {A B : Type*} [Fintype A] [Fintype B]

def energy (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) (x : A × B) : ℝ :=
  EA x.1 + EB x.2 + beta * spinSign (a x.1) * spinSign (b x.2)

def numerator (E : A → ℝ) (a : A → IsingSpin) : ℝ :=
  ∑ x, spinSign (a x) * Real.exp (E x)

def mean (E : A → ℝ) (a : A → IsingSpin) : ℝ :=
  FinitePosterior.mean E (fun _ => 0) (fun x => spinSign (a x)) 0

end Problem367.FiniteSpinCoupling

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteIsingSplit
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FiniteIsingSplit

variable {V : Type*} [DecidableEq V]

variable {d : ℕ}

def observedEnergy (beta : ℝ) (D : Finset (TreeVertex d))
    (y : TreeVertex d → ℝ) : (D → IsingSpin) → ℝ :=
  FinitePosterior.fieldEnergy (finiteIsingEnergy beta D)
    (fun eta v => spinSign (eta v)) (D.restrict y)

def mean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (y : TreeVertex d → ℝ) : ℝ :=
  FiniteSpinCoupling.mean (observedEnergy beta D y) (fun eta => eta v)

def field (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (y : TreeVertex d → ℝ) : ℝ := Real.artanh (mean beta D v y)

end Problem367.FiniteIsingSplit

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FreeLawStationarity
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.map_relabel_eq {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (g : TreeAut d) :
    mu.map (relabel g) = mu :=
  (hmu.map_relabel g).unique hmu

theorem HasFreeIsingLaw.measurePreserving_relabel {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (g : TreeAut d) :
    MeasurePreserving (relabel g) mu mu :=
  ⟨Problem367.measurable_relabel g, hmu.map_relabel_eq g⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_CoordinateNaturality
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

def coordinateRelabelEquiv {ι A : Type*} [MeasurableSpace A] (e : ι ≃ ι) :
    (ι → A) ≃ᵐ (ι → A) where
  toFun x i := x (e.symm i)
  invFun x i := x (e i)
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  measurable_toFun := Measurable.of_eval (fun _ => measurable_pi_apply _)
  measurable_invFun := Measurable.of_eval (fun _ => measurable_pi_apply _)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathCylinders
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
namespace Problem367
namespace ConnectedHull

def pathEdge {d : ℕ} (v : TreeVertex d) (i : Fin v.1.length) :
    TreeVertex d × TreeVertex d := (path v i.castSucc, path v i.succ)

end ConnectedHull

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_ComponentSignalAttenuation
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.ComponentSignalAttenuation

open PlantedSymmetry

def posteriorMean {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (c : Fin d) (t : ℝ≥0) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ :=
  (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
    fun p => spinSign (p.1 ⟨[c], List.IsChain.singleton c⟩) |
    PlantedInformation.observationSigma (componentIndexVertex (c := c)) t]

def posteriorLaw {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (c : Fin d) (t : ℝ≥0) : Measure ℝ :=
  (μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (posteriorMean μ c t)

end Problem367.ComponentSignalAttenuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ContinuousObservationHistory
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability
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

theorem measurable_stoppedPath (s : ℝ≥0) : Measurable (stoppedPath s) := by
  apply measurable_path_of_eval
  intro t
  exact (continuous_eval_const (min t s)).measurable

theorem stoppedPath_stoppedPath {s t : ℝ≥0} (hst : s ≤ t) (f : Path) :
    stoppedPath s (stoppedPath t f) = stoppedPath s f := by
  ext u
  simp only [stoppedPath_apply, min_eq_left ((min_le_right u s).trans hst)]

variable {ι : Type*}

def stoppedArray (s : ℝ≥0) (f : ι → Path) : ι → Path :=
  fun i => stoppedPath s (f i)

theorem measurable_stoppedArray (s : ℝ≥0) : Measurable (stoppedArray (ι := ι) s) := by
  exact Measurable.of_eval fun index =>
    (measurable_stoppedPath s).comp (measurable_pi_apply index)

theorem stoppedArray_stoppedArray {s t : ℝ≥0} (hst : s ≤ t) (f : ι → Path) :
    stoppedArray s (stoppedArray t f) = stoppedArray s f := by
  funext i
  exact stoppedPath_stoppedPath hst (f i)

end Problem367.ContinuousObservationHistory

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_ContinuousNoiseSplit
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability
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

variable {ι : Type*}

def futureArray (s : ℝ≥0) (f : ι → Path) : ι → Path := fun i => futurePath s (f i)

end Problem367.ContinuousNoiseSplit

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_FiniteFieldGaussianEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal

namespace Problem367.FinitePosterior

variable {S : Type*} [Fintype S] [Nonempty S]

variable {V : Type*} [Fintype V]

def fieldEntropy (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) : ℝ :=
  -Real.log (1 - fieldMean energy spin observable x ^ 2)

def fieldEntropyGradient (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) : ℝ :=
  2 * fieldMean energy spin observable x * normalizedFieldCovariance energy spin observable x v

def fieldEntropyHessianDiagonal (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) : ℝ :=
  2 * (1 + fieldMean energy spin observable x ^ 2) *
      normalizedFieldCovariance energy spin observable x v ^ 2 -
    4 * fieldMean energy spin observable x * fieldMean energy spin (fun s => spin s v) x *
      normalizedFieldCovariance energy spin observable x v

open MeasureTheory

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_Leaf
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.GibbsLeaf

def energy {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) : ℝ :=
  (∑ x ∈ D, h x * spinSign (eta x)) +
    beta * ∑ e ∈ inducedEdges D, spinSign (eta e.1) * spinSign (eta e.2)

def weight {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) : ℝ :=
  Real.exp (energy beta h D eta)

end Problem367.GibbsLeaf

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_LeafMessage
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.GibbsLeaf

def partition {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) : ℝ :=
  ∑ eta : D → IsingSpin, weight beta h D (extendFiniteSpin D eta)

def mass {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) : ℝ :=
  weight beta h D eta / partition beta h D

end Problem367.GibbsLeaf

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_FinitePathGibbs
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePathGibbs

def backwardField (beta : ℝ) (h : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, 0 => h 0 +
      (Real.log (tailPartition beta (fun i => h (i + 1)) n .pos) -
        Real.log (tailPartition beta (fun i => h (i + 1)) n .neg)) / 2
  | n + 1, i + 1 => backwardField beta (fun j => h (j + 1)) n i

def partition (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ a, Real.exp (root * spinSign a) * tailPartition beta h n a

def rootLaw (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) (a : IsingSpin) : ℝ :=
  Real.exp (root * spinSign a) * tailPartition beta h n a / partition beta root h n

def mass (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (x : Fin (n + 1) → IsingSpin) : ℝ :=
  InhomogeneousChain.jointWeight (rawKernel beta h)
    (fun a => Real.exp (root * spinSign a)) n x / partition beta root h n

def energy (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (x : Fin (n + 1) → IsingSpin) : ℝ :=
  root * spinSign (x 0) + ∑ i : Fin n,
    (h i + beta * spinSign (x i.castSucc)) * spinSign (x i.succ)

def mean (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (f : (Fin (n + 1) → IsingSpin) → ℝ) : ℝ :=
  ∑ x, mass beta root h n x * f x

def endpointCovariance (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  mean beta root h n (fun x => spinSign (x 0) * spinSign (x (Fin.last n))) -
    mean beta root h n (fun x => spinSign (x 0)) *
      mean beta root h n (fun x => spinSign (x (Fin.last n)))

end Problem367.FinitePathGibbs

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathResponse
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.TreePathResponse

def mean {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) (v : TreeVertex d) : ℝ :=
  LeafGibbs.expectation
    (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
    (fun eta => spinSign (extendFiniteSpin D eta v))

def covariance {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) (u v : TreeVertex d) : ℝ :=
  LeafGibbs.covariance
    (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
    (fun eta => spinSign (extendFiniteSpin D eta u))
    (fun eta => spinSign (extendFiniteSpin D eta v))

def response {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) (u v : TreeVertex d) : ℝ :=
  covariance beta h D u v / (1 - mean beta h D u ^ 2)

end Problem367.TreePathResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeResponse
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.GaussianTreeResponse

open GaussianTreeCovariance (gaussianContraction )

abbrev response {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d))
    (r v : TreeVertex d) (h : TreeVertex d → ℝ) : ℝ :=
  TreePathResponse.response beta h E r v

end Problem367.GaussianTreeResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeResponseEnergy
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianTreeResponse

open GaussianTreeCovariance

def finiteRow {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d)) (r : TreeVertex d)
    (h x : TreeVertex d → ℝ) (v : TreeVertex d) (y : E → ℝ) : ℝ :=
  if v ∈ E then response beta E r v
    (fun u => h u + Function.updateFinset x E y u) else 0

end Problem367.GaussianTreeResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeResponseMixture
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianTreeResponse

open GaussianTreeCovariance

def shiftedRow {d : ℕ} {Ω : Type*} (beta : ℝ) (E : Finset (TreeVertex d))
    (r : TreeVertex d) (H : Ω → TreeVertex d → ℝ) (x : TreeVertex d → ℝ)
    (v : TreeVertex d) (p : Ω × (E → ℝ)) : ℝ :=
  finiteRow beta E r (H p.1) x v p.2

end Problem367.GaussianTreeResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeResponseNaturality
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianTreeResponseNaturality

def fieldEquiv {d : ℕ} (g : TreeAut d) (D : Finset (TreeVertex d)) :
    (D → ℝ) ≃ᵐ (D.image g.toEquiv → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : D.image g.toEquiv => ℝ)
    (TreeGibbsAut.vertexEquiv g D)

@[simp] theorem fieldEquiv_apply_image {d : ℕ} (g : TreeAut d)
    (D : Finset (TreeVertex d)) (y : D → ℝ) (u : D) :
    fieldEquiv g D y (TreeGibbsAut.vertexEquiv g D u) = y u := by
  simp [fieldEquiv, MeasurableEquiv.coe_piCongrLeft]

end Problem367.GaussianTreeResponseNaturality

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeResponsePlanted
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianTreeResponse

open GaussianTreeCovariance PlantedSymmetry

def spinDrift {d : ℕ} (t : ℝ) (σ : TreeVertex d → IsingSpin) : TreeVertex d → ℝ :=
  fun u => t * spinSign (σ u)

def observedRow {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d)) (r : TreeVertex d)
    (t : ℝ) (v : TreeVertex d)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) : ℝ :=
  if v ∈ E then response beta E r v (observation t p) else 0

end Problem367.GaussianTreeResponse

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

def quadraticSum {I : Type*} (M : I → Ω → ℝ) (t : ℕ → I) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, secondWeight (M (t i) ω) * (M (t (i + 1)) ω - M (t i) ω) ^ 2

def compensatorSum {I : Type*} (M A : I → Ω → ℝ) (t : ℕ → I) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, secondWeight (M (t i) ω) * (A (t (i + 1)) ω - A (t i) ω)

end Problem367.ArtanhMartingaleFormula

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PlantedStationarity
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
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

theorem measurePreserving_iid_relabel (nu : Measure A) [IsProbabilityMeasure nu]
    (g : TreeAut d) :
    MeasurePreserving (relabel g)
      (Measure.infinitePi (fun _ : TreeVertex d => nu))
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) := by
  refine ⟨measurable_relabel g, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj g.toEquiv.symm.injective

theorem measurePreserving_planted_relabel {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu] (g : TreeAut d) :
    MeasurePreserving (Prod.map (relabel g) (relabel g))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
  let := hmu.isProbabilityMeasure
  exact (hmu.measurePreserving_relabel g).prod (measurePreserving_iid_relabel nu g)

end Problem367.PlantedStationarity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ArrayPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367

lemma measurable_arrayNaturalFiltration_of_intertwining
    {ι Ω : Type*} [MeasurableSpace Ω]
    (X : ι → ℝ≥0 → Ω → ℝ) (hmX : ∀ i t, Measurable (X i t))
    (T : Ω → Ω) (r : ι → ι)
    (hT : ∀ i t ω, X i t (T ω) = X (r i) t ω) (t : ℝ≥0) :
    Measurable[arrayNaturalFiltration X hmX t,
      arrayNaturalFiltration X hmX t] T := by
  rw [arrayNaturalFiltration_eq_comap]
  apply measurable_comap_iff.mpr
  have heq : (fun ω i (s : Set.Iic t) => X i s ω) ∘ T =
      (fun x : ι → Set.Iic t → ℝ => fun i s => x (r i) s) ∘
        (fun ω i (s : Set.Iic t) => X i s ω) := by
    funext ω i s
    exact hT i s ω
  rw [heq]
  exact (Measurable.of_eval fun index =>
    Measurable.of_eval fun time => (measurable_pi_apply time).comp
      (measurable_pi_apply (r index))).comp (comap_measurable _)

theorem ae_all_nnrealTimePrimitive_eq_of_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {m n : ℝ≥0 → Ω → ℝ}
    (hm : Measurable (fun p : ℝ≥0 × Ω => m p.1 p.2))
    (hn : Measurable (fun p : ℝ≥0 × Ω => n p.1 p.2))
    (heq : ∀ t, m t =ᵐ[P] n t) :
    ∀ᵐ ω ∂P, ∀ t, nnrealTimePrimitive m t ω = nnrealTimePrimitive n t ω := by
  have hmR : Measurable (fun p : ℝ × Ω => m p.1.toNNReal p.2) :=
    hm.comp (show Measurable (fun p : ℝ × Ω => (p.1.toNNReal, p.2)) by fun_prop)
  have hnR : Measurable (fun p : ℝ × Ω => n p.1.toNNReal p.2) :=
    hn.comp (show Measurable (fun p : ℝ × Ω => (p.1.toNNReal, p.2)) by fun_prop)
  have htime : ∀ᵐ ω ∂P, ∀ᵐ (s : ℝ) ∂volume, m s.toNNReal ω = n s.toNNReal ω :=
    (Measure.ae_ae_comm (μ := (volume : Measure ℝ)) (ν := P)
      (p := fun s ω => m s.toNNReal ω = n s.toNNReal ω)
      (measurableSet_eq_fun hmR hnR)).mp
      (Filter.Eventually.of_forall fun (s : ℝ) => heq s.toNNReal)
  filter_upwards [htime] with ω hω
  intro t
  exact intervalIntegral.integral_congr_ae (hω.mono fun _ hs _ => hs)

namespace ArrayPosteriorStationarity

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

def plantedRelabel (g : TreeAut d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) ≃ᵐ
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) :=
  (coordinateRelabelEquiv g.toEquiv).prodCongr (coordinateRelabelEquiv g.toEquiv)

lemma measurable_spinArray : Measurable (spinArray (d := d)) := by
  have hm : Measurable spinSign := by intro s hs; trivial
  exact Measurable.of_eval fun vertex => hm.comp (measurable_pi_apply vertex)

def filtration (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t)) :
    Filtration ℝ≥0
      (inferInstance : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A))) :=
  arrayObservationFiltration (fun _ : TreeVertex d => B) (fun _ => hmB)
    spinArray measurable_spinArray

lemma measurable_plantedRelabel_filtration
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (g : TreeAut d) (t : ℝ≥0) :
    Measurable[filtration B hmB t, filtration B hmB t] (plantedRelabel (A := A) g) := by
  apply measurable_arrayNaturalFiltration_of_intertwining
    (plantedArrayObservation (fun _ : TreeVertex d => B) spinArray)
    (plantedArrayObservation_measurable (fun _ => hmB) measurable_spinArray)
    (plantedRelabel g) g.toEquiv.symm
  intro i s q
  rfl

lemma measurable_plantedRelabel_symm_filtration
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (g : TreeAut d) (t : ℝ≥0) :
    Measurable[filtration B hmB t, filtration B hmB t] (plantedRelabel (A := A) g).symm := by
  apply measurable_arrayNaturalFiltration_of_intertwining
    (plantedArrayObservation (fun _ : TreeVertex d => B) spinArray)
    (plantedArrayObservation_measurable (fun _ => hmB) measurable_spinArray)
    (plantedRelabel g).symm g.toEquiv
  intro i s q
  rfl

lemma measurePreserving_plantedRelabel {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (g : TreeAut d) :
    MeasurePreserving (plantedRelabel (A := A) g)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) :=
  PlantedStationarity.measurePreserving_planted_relabel hμ ν g

lemma integrable_spin_coordinate
    (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    [IsFiniteMeasure P] (v : TreeVertex d) :
    Integrable (fun q => spinSign (q.1 v)) P := by
  have hm : Measurable spinSign := by intro s hs; trivial
  apply Integrable.of_bound
    (hm.comp ((measurable_pi_apply v).comp measurable_fst)).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro q
  cases hs : q.1 v <;> norm_num [spinSign, hs]

def posterior
    (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v : TreeVertex d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ :=
  P[fun q => spinSign (q.1 v) | filtration B hmB t]

theorem posterior_relabel_ae {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (g : TreeAut d) (t : ℝ≥0) (v : TreeVertex d) :
    posterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v ∘
        plantedRelabel g =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t
        (g.toEquiv.symm v) := by
  let := hμ.isProbabilityMeasure
  exact condExp_comp_measurePreserving_equiv (filtration B hmB |>.le t)
    (plantedRelabel g) (measurePreserving_plantedRelabel hμ ν g)
    (measurable_plantedRelabel_filtration B hmB g t)
    (measurable_plantedRelabel_symm_filtration B hmB g t)
    (integrable_spin_coordinate _ v)

theorem posterior_version_relabel_ae {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    {m : ℝ≥0 → TreeVertex d →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ}
    (hversion : ∀ t v, m t v =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v)
    (g : TreeAut d) (t : ℝ≥0) (v : TreeVertex d) :
    m t v ∘ plantedRelabel g =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      m t (g.toEquiv.symm v) := by
  exact ((measurePreserving_plantedRelabel hμ ν g).quasiMeasurePreserving.ae_eq_comp
    (hversion t v)).trans ((posterior_relabel_ae hμ ν B hmB g t v).trans
      (hversion t (g.toEquiv.symm v)).symm)

theorem posterior_primitive_relabel_ae {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    {m : ℝ≥0 → TreeVertex d →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ}
    (hm : ∀ v, Measurable (fun p : ℝ≥0 ×
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) => m p.1 v p.2))
    (hversion : ∀ t v, m t v =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v)
    (g : TreeAut d) :
    ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)), ∀ v t,
      nnrealTimePrimitive (fun u => m u v) t (plantedRelabel g q) =
        nnrealTimePrimitive (fun u => m u (g.toEquiv.symm v)) t q := by
  let := hμ.isProbabilityMeasure
  apply ae_all_iff.mpr
  intro v
  have hleft : Measurable (fun p : ℝ≥0 ×
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
      m p.1 v (plantedRelabel g p.2)) :=
    (hm v).comp (measurable_fst.prodMk ((plantedRelabel g).measurable.comp measurable_snd))
  exact ae_all_nnrealTimePrimitive_eq_of_version _ hleft (hm (g.toEquiv.symm v))
    (fun t => posterior_version_relabel_ae hμ ν B hmB hversion g t v)

theorem innovation_array_relabel_ae {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    {m : ℝ≥0 → TreeVertex d →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ}
    (hm : ∀ v, Measurable (fun p : ℝ≥0 ×
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) => m p.1 v p.2))
    (hversion : ∀ t v, m t v =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v)
    (g : TreeAut d) :
    ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
      (fun v t => plantedArrayObservation (fun _ : TreeVertex d => B) spinArray
        v t (plantedRelabel g q) -
          nnrealTimePrimitive (fun u => m u v) t (plantedRelabel g q)) =
      relabel g (fun v t => plantedArrayObservation (fun _ : TreeVertex d => B) spinArray
        v t q - nnrealTimePrimitive (fun u => m u v) t q) := by
  filter_upwards [posterior_primitive_relabel_ae hμ ν B hmB hm hversion g] with q hq
  funext v t
  rw [hq v t]
  rfl

end ArrayPosteriorStationarity
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_ColoredKoopman
attribute [-simp] _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.ColoredEdgeLifts
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def koopmanEquiv (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℝ τ hτ)
    (koopmanL2_involutive τ hτ hinv).surjective

@[simp] theorem koopmanEquiv_apply (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) (f : Lp ℝ 2 μ) :
    koopmanEquiv τ hτ hinv f = koopmanL2 τ hτ f := rfl

variable [IsFiniteMeasure μ]

def centeredKoopmanIsometry (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) : centeredL2 μ →ₗᵢ[ℝ] centeredL2 μ where
  toLinearMap := ((koopmanL2 τ hτ).restrict
    (koopmanL2_preserves_centered τ hτ hinv)).toLinearMap
  norm_map' f := koopmanL2_norm τ hτ (f : Lp ℝ 2 μ)

@[simp] theorem centeredKoopmanIsometry_apply_coe
    (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) (f : centeredL2 μ) :
    (centeredKoopmanIsometry τ hτ hinv f : Lp ℝ 2 μ) = koopmanL2 τ hτ f := rfl

theorem centeredKoopmanIsometry_involutive
    (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) : Function.Involutive (centeredKoopmanIsometry τ hτ hinv) := by
  intro f
  apply Subtype.ext
  exact koopmanL2_involutive τ hτ hinv f

def centeredKoopmanEquiv (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) : centeredL2 μ ≃ₗᵢ[ℝ] centeredL2 μ :=
  LinearIsometryEquiv.ofSurjective (centeredKoopmanIsometry τ hτ hinv)
    (centeredKoopmanIsometry_involutive τ hτ hinv).surjective

@[simp] theorem centeredKoopmanEquiv_apply_coe
    (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) (f : centeredL2 μ) :
    (centeredKoopmanEquiv τ hτ hinv f : Lp ℝ 2 μ) = koopmanL2 τ hτ f := rfl

end Problem367.ColoredEdgeLifts

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_DifferenceKoopman
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.CopyDifference

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable {μ : Measure A} {ν : Measure B} {p q : B → A}
variable (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
variable (τ : A → A) (σ : B → B)
variable (hτ : MeasurePreserving τ μ μ) (hσ : MeasurePreserving σ ν ν)
variable (hpc : p ∘ σ = τ ∘ p) (hqc : q ∘ σ = τ ∘ q)

include hpc hqc in
theorem symmetry_intertwines (f : Lp ℝ 2 μ) :
    koopmanL2 σ hσ (operator hp hq f) = operator hp hq (koopmanL2 τ hτ f) :=
  congrArg (fun L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν => L f)
    (intertwines hp hq hτ hσ hpc hqc)

def differenceKoopmanIsometry :
    rangeClosure (operator hp hq) →ₗᵢ[ℝ] rangeClosure (operator hp hq) where
  toLinearMap := (restrictToRangeClosure (operator hp hq)
    (koopmanL2 τ hτ) (koopmanL2 σ hσ)
    (symmetry_intertwines hp hq τ σ hτ hσ hpc hqc)).toLinearMap
  norm_map' f := koopmanL2_norm σ hσ (f : Lp ℝ 2 ν)

@[simp] theorem differenceKoopmanIsometry_apply_coe
    (f : rangeClosure (operator hp hq)) :
    (differenceKoopmanIsometry hp hq τ σ hτ hσ hpc hqc f : Lp ℝ 2 ν) =
      koopmanL2 σ hσ f := rfl

theorem differenceKoopmanIsometry_involutive (hinv : Function.Involutive σ) :
    Function.Involutive (differenceKoopmanIsometry hp hq τ σ hτ hσ hpc hqc) := by
  intro f
  apply Subtype.ext
  exact koopmanL2_involutive σ hσ hinv f

def differenceKoopmanEquiv (hinv : Function.Involutive σ) :
    rangeClosure (operator hp hq) ≃ₗᵢ[ℝ] rangeClosure (operator hp hq) :=
  LinearIsometryEquiv.ofSurjective
    (differenceKoopmanIsometry hp hq τ σ hτ hσ hpc hqc)
    (differenceKoopmanIsometry_involutive hp hq τ σ hτ hσ hpc hqc hinv).surjective

@[simp] theorem differenceKoopmanEquiv_apply_coe (hinv : Function.Involutive σ)
    (f : rangeClosure (operator hp hq)) :
    (differenceKoopmanEquiv hp hq τ σ hτ hσ hpc hqc hinv f : Lp ℝ 2 ν) =
      koopmanL2 σ hσ f := rfl

end Problem367.CopyDifference

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_ContinuousCopyBrownian
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability
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

def history (s : ℝ≥0) (q : Joint (ι := ι)) : Joint (ι := ι) :=
  (stoppedArray s q.1, (stoppedArray s q.2.1, stoppedArray s q.2.2))

theorem measurable_history (s : ℝ≥0) : Measurable (history (ι := ι) s) :=
  ((measurable_stoppedArray s).comp measurable_fst).prodMk
    (((measurable_stoppedArray s).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_stoppedArray s).comp (measurable_snd.comp measurable_snd)))

theorem history_history {s t : ℝ≥0} (hst : s ≤ t) (q : Joint (ι := ι)) :
    history s (history t q) = history s q := by
  simp only [history, stoppedArray_stoppedArray hst]

abbrev pastSpace (s : ℝ≥0) : MeasurableSpace (Joint (ι := ι)) :=
  MeasurableSpace.comap (history s) inferInstance

def joinedFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Joint (ι := ι))) where
  seq := pastSpace
  mono' := by
    intro s t hst
    have h := MeasurableSpace.comap_mono (g := history (ι := ι) t) (measurable_history s).comap_le
    simpa only [MeasurableSpace.comap_comp, Function.comp_def, history_history hst] using h
  le' s := (measurable_history s).comap_le

end Problem367.ContinuousCopyBrownian

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastOutsideCone
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

abbrev OutsideConeVertex {d : ℕ} (b : TreeVertex d) :=
  {v : TreeVertex d // ¬ b.1 <+: v.1}

abbrev OutsideConeNonroot {d : ℕ} (b : TreeVertex d) :=
  {v : TreeVertex d // v.1 ≠ [] ∧ ¬ b.1 <+: v.1}

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredPathCount
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_restrictedTreeCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.ColoredPathAverage

def pathReducedTailEquiv {d : ℕ} (n : ℕ) (i : Fin d) :
    Path d n i ≃ ReducedTail i n := by
  induction n generalizing i with
  | zero =>
    change PUnit ≃ ReducedTail i 0
    exact (Equiv.ofUnique PUnit Unit).trans (reducedTailZeroEquiv i).symm
  | succ n ih =>
    refine Equiv.trans ?_ (reducedTailSuccEquiv i n).symm
    exact {
      toFun := fun p => ⟨⟨p.1.1, Ne.symm p.1.2⟩, ih p.1.1 p.2⟩
      invFun := fun p => ⟨⟨p.1.1, Ne.symm p.1.2⟩, (ih p.1.1).symm p.2⟩
      left_inv := by
        rintro ⟨⟨color, hcolor⟩, path⟩
        simp only [Equiv.symm_apply_apply]
        rfl
      right_inv := by rintro ⟨⟨j, hj⟩, p⟩; simp }

@[simp] theorem card_path {d : ℕ} (n : ℕ) (i : Fin d) :
    Fintype.card (Path d n i) = (d - 1) ^ n := by
  rw [Fintype.card_congr (pathReducedTailEquiv n i), card_reducedTail]

@[simp] theorem colors_eq_cons_pathReducedTailEquiv {d n : ℕ} {i : Fin d}
    (p : Path d n i) :
    colors p = i :: (pathReducedTailEquiv n i p).1 := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨⟨j, hj⟩, p⟩
    change i :: colors p = i :: j :: (pathReducedTailEquiv n j p).1
    exact congrArg (List.cons i) (ih p)

end Problem367.ColoredPathAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredPathEndpoints
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

namespace ColoredPathAverage

def tailVertex {d n : ℕ} {i : Fin d} (p : Path d n i) : TreeVertex d :=
  ⟨(colors p).dropLast, (colors_isChain p).dropLast⟩

def headVertex {d n : ℕ} {i : Fin d} (p : Path d n i) : TreeVertex d :=
  ⟨colors p, colors_isChain p⟩

end ColoredPathAverage

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Escape
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace TreeEscape

abbrev root {d : ℕ} : TreeVertex d := ⟨[], List.IsChain.nil⟩

end TreeEscape

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_InfiniteCanonicalPathResponse
attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators

namespace Problem367

open PlantedSymmetry

namespace CavityFieldLimit

def rootResponseProduct {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (v : TreeVertex d) (y : TreeVertex d → ℝ) : ℝ :=
  Real.tanh beta ^ v.1.length *
    ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
      (infiniteCavityField hbeta (ConnectedHull.takeVertex v (i + 1))
        (ConnectedHull.takeVertex v i) y)

end CavityFieldLimit

open CavityFieldLimit

end Problem367

end

end OAI
end


