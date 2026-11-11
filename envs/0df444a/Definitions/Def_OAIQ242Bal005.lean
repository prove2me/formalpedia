-- Prove2me | Definitions.Def_OAIQ242Bal005
-- name    : OAIQ242Bal005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:52:54.626579+00:00
-- url     : https://prove2.me/theorems/5b2cdf66-41a7-4c05-a2f9-b6a0519fce8b
-- title:
--   Definitions bundle OAIQ242Bal005 of the split of OpenAI, Directional transience implies ballisticity
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 188 declarations of OpenAI's Lean: 53 definitions, 2 inductive types or structures, 15 instances and 118 theorems. The definitions and types are `OAI.DirectionalTransience.SeedPreserved`, `OAI.DirectionalTransience.SeedStateOrdered`, `OAI.DirectionalTransience.SeedStateRetained`, `OAI.DirectionalTransience.StationaryArrayLaw`, `OAI.DirectionalTransience.StationaryArrayLaw.actualProfileSystem`, `OAI.DirectionalTransience.StationaryProfileSystem`, `OAI.DirectionalTransience.TubeThreat`, `OAI.DirectionalTransience.actualCurrentLaw`, `OAI.DirectionalTransience.actualCurrentWindow`, `OAI.DirectionalTransience.allocatedSmallCuts`, `OAI.DirectionalTransience.annealedFrom`, `OAI.DirectionalTransience.arrayClassFinset`, `OAI.DirectionalTransience.arrayClassKernel`, `OAI.DirectionalTransience.arrayCurrentData`, `OAI.DirectionalTransience.arrayTransport`, `OAI.DirectionalTransience.boundarySuffix`, `OAI.DirectionalTransience.bridgedRestart`, `OAI.DirectionalTransience.cellRadius`, `OAI.DirectionalTransience.centralPrefixMass`, `OAI.DirectionalTransience.clippedNoDropProduct`, `OAI.DirectionalTransience.commonBoundaryGap`, `OAI.DirectionalTransience.conditionedFrom`, `OAI.DirectionalTransience.coordinateProfile`, `OAI.DirectionalTransience.currentAnchorKernel`, `OAI.DirectionalTransience.currentClassKernel`, `OAI.DirectionalTransience.currentDustWeight`, `OAI.DirectionalTransience.currentInput`, `OAI.DirectionalTransience.currentReferenceLaw`, `OAI.DirectionalTransience.currentSelect`, `OAI.DirectionalTransience.currentStoppedProfile`, `OAI.DirectionalTransience.currentWindowReference`, `OAI.DirectionalTransience.curvePolicyKernel`, `OAI.DirectionalTransience.curvePolicy_average`, `OAI.DirectionalTransience.curveWordEvent`, `OAI.DirectionalTransience.episodeStageCount`, `OAI.DirectionalTransience.fullMarkedShift`, `OAI.DirectionalTransience.horizontalCoordinateKernel`, `OAI.DirectionalTransience.horizontalLayerEquiv`, `OAI.DirectionalTransience.markedArrayLaw`, `OAI.DirectionalTransience.markedData` and 15 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `Ballisticity_Coupling_SeedOrder`, `Ballisticity_Coupling_SeedProfile`, `Ballisticity_Crossings_Hit`, `Ballisticity_Entropy_AnchorEntropy`, `Ballisticity_Entropy_WindowEntropy`, `Ballisticity_Estimates_AlignedRecordPrefix`, `Ballisticity_Estimates_CellSchedule`, `Ballisticity_Estimates_ClassFinset`, `Ballisticity_Estimates_ClassMoment`, `Ballisticity_Estimates_ClassSelection`, `Ballisticity_Estimates_ClippedInverse`, `Ballisticity_Estimates_CurvePolicy`, `Ballisticity_Estimates_CurvePolicyPMF`, `Ballisticity_Estimates_CurvePrefix`, `Ballisticity_Estimates_Dust`, `Ballisticity_Estimates_FiniteClasses`, `Ballisticity_Estimates_FirstBelow`, `Ballisticity_Estimates_IndependentDyadic`, `Ballisticity_Estimates_InputMarginal`, `Ballisticity_Estimates_JointPastRestart`, `Ballisticity_Estimates_LowerClip`, `Ballisticity_Estimates_MarkedObservables`, `Ballisticity_Estimates_ObservedCharges`, `Ballisticity_Estimates_ProfileMeasureUpdate`, `Ballisticity_Estimates_ProperProfile`, `Ballisticity_Estimates_StayUntil`, `Ballisticity_Estimates_WordDepartures`, `Ballisticity_Geometry_StoppedTubeEndpoint`, `Ballisticity_Geometry_TubeEndpoint`, `Ballisticity_Geometry_TubePrefix`, `Ballisticity_Geometry_TubePrefixMass`, `Ballisticity_Geometry_WindowProjection`, `Ballisticity_Geometry_WindowWeak`, `Ballisticity_Renewal_RegenerationWords`, `Ballisticity_Stationary_Array`, `Ballisticity_Stationary_ArrayClassProbability`, `Ballisticity_Stationary_ArrayClosed`, `Ballisticity_Stationary_ArrayDust`, `Ballisticity_Stationary_ArrayFiniteClasses`, `Ballisticity_Stationary_ArrayFull`, `Ballisticity_Stationary_ArrayMarkedEntropy`, `Ballisticity_Stationary_ArrayMarkedIterate`, `Ballisticity_Stationary_ArrayMassSurvival`, `Ballisticity_Stationary_ArrayTopology`, `Ballisticity_Stationary_EpisodeGlobalRetention`, `Ballisticity_Stationary_StationaryArrayLaw`, `Ballisticity_Stationary_StationaryMarking`, `Ballisticity_Stationary_StationaryMonotone`, `Ballisticity_Stationary_StationaryProfile`, `Ballisticity_Stationary_StationaryProfile2`, `Ballisticity_Walk_ClippedPairGrowth`, `Ballisticity_Walk_CurvePolicyKernel`, `Ballisticity_Walk_FixedQuenchedKernel`, `Ballisticity_Walk_ProfileGrowth2`.
--
--   **Imports.** It imports the published bundle `Def_DirectionalBallisticity`; the bundles `OAIQ242Bal002` and `OAIQ242Bal003` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ242Bal007`; the statements `OAI.DirectionalTransience.OperationalConstants.bad_stationary_array_law`, `OAI.DirectionalTransience.OperationalConstants.stationary_window_entropy`, `OAI.DirectionalTransience.actualOccupation_window_kl_le`, `OAI.DirectionalTransience.actual_finite_stage_estimate`, `OAI.DirectionalTransience.canonical_two_tube_threat`, `OAI.DirectionalTransience.clipped_pair_favorable_fraction`, `OAI.DirectionalTransience.curveIncrement_short_block`, `OAI.DirectionalTransience.curvePolicy_real_tube_probability`, `OAI.DirectionalTransience.raw_median_tube_single_site`, `OAI.DirectionalTransience.recordMedianSlope_small`, `OAI.DirectionalTransience.recordMedian_shortBlock`, `OAI.DirectionalTransience.shared_centered_cross_uniform_bound`, `OAI.DirectionalTransience.shared_finite_past_cross_bound`, `OAI.DirectionalTransience.shared_limit_finite_past_identity`, `OAI.DirectionalTransience.shared_median_pair_path_limit`, `OAI.DirectionalTransience.shared_pair_path_limit`, `OAI.DirectionalTransience.short_block_survival`, `OAI.DirectionalTransience.small_scale_gaussian_mass`, `OAI.DirectionalTransience.small_scale_tail_moment`, `OAI.DirectionalTransience.successfulMedian_scaled_tail_comparison`, `OAI.DirectionalTransience.successful_small_variance_bound`, `OAI.DirectionalTransience.successful_tail_profile_bound`, `OAI.DirectionalTransience.transverse_firstHit_linear_path_limit` and `OAI.DirectionalTransience.transverse_firstHit_path_limit`; the proofs of `OAI.DirectionalTransience.EpisodeChainLedger.mean_episode_drops_local`, `OAI.DirectionalTransience.OperationalConstants.bad_array_finite_marks`, `OAI.DirectionalTransience.OperationalConstants.bad_limit_averaged_survival`, `OAI.DirectionalTransience.OperationalConstants.bad_limit_drop_moment`, `OAI.DirectionalTransience.OperationalConstants.bad_limit_length_moment`, `OAI.DirectionalTransience.OperationalConstants.bad_occupation_stationary_limit`, `OAI.DirectionalTransience.OperationalConstants.bad_stationary_array_law`, `OAI.DirectionalTransience.OperationalConstants.conditional_episode_drops`, `OAI.DirectionalTransience.OperationalConstants.raw_dropCut_upper`, `OAI.DirectionalTransience.OperationalConstants.stationary_window_entropy`, `OAI.DirectionalTransience.actual_late_protection_first_failure`, `OAI.DirectionalTransience.actual_outward_log_bound`, `OAI.DirectionalTransience.canonical_two_tube_threat`, `OAI.DirectionalTransience.clipped_pair_favorable_fraction`, `OAI.DirectionalTransience.clipping_uniform`, `OAI.DirectionalTransience.conditioned_wordRadius_integrable`, `OAI.DirectionalTransience.curveIncrement_short_block`, `OAI.DirectionalTransience.curvePolicy_real_tube_probability`, `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, `OAI.DirectionalTransience.fresh_budget_threat_bound`, `OAI.DirectionalTransience.independent_commonWordIncrement_integrable`, `OAI.DirectionalTransience.independent_firstHit_clipped_drift`, `OAI.DirectionalTransience.operational_constants_exist`, `OAI.DirectionalTransience.raw_median_tube_single_site`, `OAI.DirectionalTransience.recordFluctuationScale_tendsto`, `OAI.DirectionalTransience.recordMedianSlope_small`, `OAI.DirectionalTransience.recordMedian_shortBlock`, `OAI.DirectionalTransience.seed_block_tests`, `OAI.DirectionalTransience.separated_seeds`, `OAI.DirectionalTransience.short_block_survival`, `OAI.DirectionalTransience.small_scale_tail_moment`, `OAI.DirectionalTransience.spatial_confinement`, `OAI.DirectionalTransience.successfulMedian_scaled_tail_comparison`, `OAI.DirectionalTransience.successful_small_variance_bound`, `OAI.DirectionalTransience.successful_tail_profile_bound`, `OAI.DirectionalTransience.transverse_bad_radius_spread`, `OAI.DirectionalTransience.transverse_firstHit_fixed_sum_error`, `OAI.DirectionalTransience.transverse_firstHit_linear_path_limit` and `OAI.DirectionalTransience.transverse_firstHit_path_limit`.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal002
import Definitions.Def_OAIQ242Bal003

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordDepartures
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero _root_.OAI.DirectionalTransience.recordCount_zero _root_.OAI.DirectionalTransience.regenerationTimes_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma measurable_noDropQuenched {d : ℕ} (ℓ : Vector d) (x : Lattice d) :
    Measurable (noDropQuenched ℓ x) :=
  (Kernel.measurable_coe _ (measurableSet_noDrop ℓ x)).comp
    (measurable_id.prodMk measurable_const)

lemma noDropQuenched_translation {d : ℕ} (ℓ : Vector d) (ω : Environment d) (x : Lattice d) :
    noDropQuenched ℓ x ω = noDropQuenched ℓ 0 (fun a => ω (x + a)) := by
  have h := congrArg (fun μ : Measure (Path d) => μ (NoDrop ℓ 0))
    (quenched_translation ω x 0)
  rw [Measure.map_apply (by fun_prop) (measurableSet_noDrop ℓ 0), noDrop_translation] at h
  simpa [noDropQuenched] using h

lemma annealed_noDrop_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) :
    (∫⁻ ω, noDropQuenched ℓ x ω ∂environmentLaw ν) = annealedLaw ν (NoDrop ℓ 0) := by
  simp_rw [noDropQuenched_translation ℓ _ x]
  rw [← lintegral_map (measurable_noDropQuenched ℓ 0) (by fun_prop),
    environment_translation, annealed_apply ν (measurableSet_noDrop ℓ 0)]
  rfl

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StayUntil
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero _root_.OAI.DirectionalTransience.recordCount_zero _root_.OAI.DirectionalTransience.regenerationTimes_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma measurableSet_stayUntil {d : ℕ} (S : Set (Lattice d)) (n : ℕ) :
    MeasurableSet (StayUntil S n) := by
  simp only [StayUntil, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    (measurable_pi_apply i) S.to_countable.measurableSet

lemma quenched_stayUntil_congr {d : ℕ} (S : Set (Lattice d))
    (ω η : Environment d) (hωη : Set.EqOn ω η S) (x : Lattice d) (n : ℕ) :
    quenchedKernel (ω, x) (StayUntil S n) = quenchedKernel (η, x) (StayUntil S n) := by
  let A : Set ((i : Finset.Iic n) → Lattice d) := {f | ∀ i, f i ∈ S}
  have hA : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' A = StayUntil S n := by
    ext X
    constructor
    · intro h i hi
      exact h ⟨i, Finset.mem_Iic.mpr hi⟩
    · intro h i
      exact h i (Finset.mem_Iic.mp i.2)
  have hm (f : (i : Finset.Iic n) → Lattice d) (_ : f ∈ A) :
      MeasurableSet ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' {f}) :=
    (Preorder.measurable_frestrictLe n) (measurableSet_singleton f)
  rw [← hA, ← tsum_measure_preimage_singleton A.to_countable hm,
    ← tsum_measure_preimage_singleton A.to_countable hm]
  apply tsum_congr
  intro f
  rw [restrict_prefix_fiber]
  by_cases hf : extendPrefix n f.val 0 = x
  · rw [quenched_pathCylinder _ _ _ hf, quenched_pathCylinder _ _ _ hf]
    apply Finset.prod_congr rfl
    intro i hi
    have hie : i ≤ n := Nat.le_of_lt (Finset.mem_range.mp hi)
    have hiS : extendPrefix n f.val i ∈ S := by
      rw [extendPrefix_apply _ _ _ hie]
      exact f.property _
    simp only [edgeWeight, hωη hiS]
  · rw [quenched_pathCylinder_zero _ _ _ hf, quenched_pathCylinder_zero _ _ _ hf]

lemma quenched_stay_congr {d : ℕ} (S : Set (Lattice d))
    (ω η : Environment d) (hωη : Set.EqOn ω η S) (x : Lattice d) :
    quenchedKernel (ω, x) (Stay S) = quenchedKernel (η, x) (Stay S) := by
  have hS : Stay S = ⋂ n, StayUntil S n := by
    ext X
    simp only [Stay, StayUntil, Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h _ i _ => h i, fun h i => h i i le_rfl⟩
  have hm : Antitone (StayUntil S) := fun m n hmn X hX i hi => hX i (hi.trans hmn)
  rw [hS, hm.measure_iInter (fun n => (measurableSet_stayUntil S n).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩,
    hm.measure_iInter (fun n => (measurableSet_stayUntil S n).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩]
  congr 1
  funext n
  exact quenched_stayUntil_congr S ω η hωη x n

lemma measurable_stay_rows {d : ℕ} (S : Set (Lattice d)) (x : Lattice d) (hx : x ∈ S) :
    @Measurable _ _ (rowSigma S) _ (fun ω : Environment d => quenchedKernel (ω, x) (Stay S)) := by
  classical
  let patch : Environment d → Environment d := fun ω y => if y ∈ S then ω y else ω x
  have hp : @Measurable _ _ (rowSigma S) _ patch := by
    refine @Measurable.of_eval _ _ _ (rowSigma S) _ _ ?_
    intro y
    by_cases hy : y ∈ S
    · simpa only [patch, ite_eq_left hy] using measurable_row_on hy
    · simpa only [patch, ite_eq_right hy] using measurable_row_on hx
  have hm : Measurable (fun η : Environment d => quenchedKernel (η, x) (Stay S)) :=
    (Kernel.measurable_coe _ (measurableSet_stay S)).comp
      (measurable_id.prodMk measurable_const)
  have he : (fun ω : Environment d => quenchedKernel (ω, x) (Stay S)) =
      (fun η : Environment d => quenchedKernel (η, x) (Stay S)) ∘ patch := by
    funext ω
    exact quenched_stay_congr S ω (patch ω) (fun y hy => by simp [patch, hy]) x
  rw [he]
  exact hm.comp hp

lemma measurable_noDropQuenched_rows {d : ℕ} (ℓ : Vector d) (x : Lattice d) :
    @Measurable _ _ (rowSigma {y | dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ}) _
      (noDropQuenched ℓ x) :=
  measurable_stay_rows {y | dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ} x
    (show dot (realPosition x) ℓ ≤ dot (realPosition x) ℓ from le_rfl)

lemma noDropQuenched_lower_step {d : ℕ} (ℓ : Vector d) (ω : Environment d)
    (x : Lattice d) (e : Direction d) (he : 0 ≤ dot (realPosition (step e)) ℓ) :
    ((ω x).1 e : ℝ≥0∞) * noDropQuenched ℓ (x + step e) ω ≤ noDropQuenched ℓ x ω := by
  let f := wordPath x [e]
  have hm := quenched_prefix_future ω x f (by simp [f]) 1
    (measurableSet_noDrop ℓ (x + step e))
  have hf1 : f 1 = x + step e := by simp [f, wordPath]
  rw [hf1] at hm
  have hcy : pathCylinder f 1 = wordCylinder x [e] := rfl
  rw [hcy, quenched_wordCylinder] at hm
  have hw : ENNReal.ofReal (wordWeight ω x [e]) = ((ω x).1 e : ℝ≥0∞) := by
    simp [wordWeight]
  rw [hw] at hm
  unfold noDropQuenched
  rw [← hm]
  apply measure_mono
  intro X hX n
  rcases n with _ | n
  · simpa only [show X 0 = x from hX.2 0 (by simp)] using
      (le_refl (dot (realPosition x) ℓ))
  · have ht := hX.1 n
    change dot (realPosition (x + step e)) ℓ ≤ dot (realPosition (X (1 + n))) ℓ at ht
    rw [dot_realPosition_add] at ht
    simpa only [Nat.add_comm 1 n] using (le_trans (le_add_of_nonneg_right he) ht)

lemma noDrop_positive_limsup {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (he : 0 < dot (realPosition (step e)) ℓ)
    (hp : 0 < annealedLaw ν (NoDrop ℓ 0)) :
    ∀ᵐ ω ∂environmentLaw ν,
      ω ∈ limsup (fun n : ℕ => {ω | 0 < noDropQuenched ℓ (n • step e) ω}) atTop := by
  let A : ℕ → Set (Environment d) := fun n => {ω | 0 < noDropQuenched ℓ (n • step e) ω}
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    measurableSet_lt measurable_const (measurable_noDropQuenched ℓ _)
  have hsame (n : ℕ) : environmentLaw ν (A n) = environmentLaw ν (A 0) := by
    have hA : A n = (fun ω : Environment d => fun a => ω (n • step e + a)) ⁻¹' A 0 := by
      ext ω
      simp only [A, Set.mem_ofPred_eq, Set.mem_preimage, zero_nsmul]
      rw [noDropQuenched_translation]
    rw [hA, ← Measure.map_apply (by fun_prop) (hAm 0), environment_translation]
  have hpos : 0 < environmentLaw ν (A 0) := by
    by_contra hn
    have hz : environmentLaw ν (A 0) = 0 := le_antisymm (not_lt.mp hn) zero_le
    have hq : noDropQuenched ℓ 0 =ᵐ[environmentLaw ν] 0 := by
      apply ae_iff.mpr
      simpa only [A, zero_nsmul, pos_iff_ne_zero, Pi.zero_apply] using hz
    have hi := (lintegral_eq_zero_iff (measurable_noDropQuenched ℓ 0)).mpr hq
    rw [annealed_noDrop_translation] at hi
    exact (ne_of_gt hp) hi
  have htail : ∀ S ∈ (cofinite : Filter (Lattice d)),
      MeasurableSet[rowSigma S] (limsup A atTop) := by
    intro S hS
    have hfin : Sᶜ.Finite := mem_cofinite.mp hS
    obtain ⟨B, hB⟩ := (hfin.image (fun y => dot (realPosition y) ℓ)).bddAbove
    have ht : Tendsto (fun n : ℕ => dot (realPosition (n • step e)) ℓ) atTop atTop := by
      simp_rw [dot_realPosition_nsmul]
      exact tendsto_natCast_atTop_atTop.atTop_mul_const he
    obtain ⟨k, hk⟩ := eventually_atTop.mp (ht.eventually (eventually_gt_atTop B))
    rw [← limsup_nat_add A k]
    apply @MeasurableSet.measurableSet_limsup _ (rowSigma S)
    intro n
    apply measurableSet_lt measurable_const
    apply (measurable_noDropQuenched_rows ℓ ((n + k) • step e)).mono _ le_rfl
    apply rowSigma_mono
    intro y hy
    by_contra hyS
    have hBy : dot (realPosition y) ℓ ≤ B := hB ⟨y, hyS, rfl⟩
    exact (not_le_of_gt (hk (n + k) (Nat.le_add_left k n))) (le_trans hy hBy)
  have hEpos : 0 < environmentLaw ν (limsup A atTop) := by
    apply lt_of_lt_of_le hpos
    rw [limsup_eq_iInf_iSup_of_nat]
    change environmentLaw ν (A 0) ≤ environmentLaw ν (⋂ n, ⋃ i ≥ n, A i)
    have ha : Antitone (fun n => ⋃ i ≥ n, A i) := by
      intro n m hnm ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨i, hi, hω⟩ := hω
      exact ⟨i, le_trans hnm hi, hω⟩
    rw [ha.measure_iInter (fun n => (MeasurableSet.iUnion fun i =>
      MeasurableSet.iUnion fun _ => hAm i).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
    apply le_iInf
    intro n
    rw [← hsame n]
    exact measure_mono (Set.subset_iUnion_of_subset n (Set.subset_iUnion_of_subset le_rfl le_rfl))
  have hEone := (environment_tail_zero_one ν htail).resolve_left (ne_of_gt hEpos)
  exact ae_iff.mpr ((prob_compl_eq_zero_iff (MeasurableSet.measurableSet_limsup hAm)).mpr hEone)

lemma noDropQuenched_positive_ae {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (e : Direction d)
    (he : 0 < dot (realPosition (step e)) ℓ)
    (hp : 0 < annealedLaw ν (NoDrop ℓ 0)) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ x, 0 < noDropQuenched ℓ x ω := by
  have h0 : ∀ᵐ ω ∂environmentLaw ν, 0 < noDropQuenched ℓ 0 ω := by
    obtain ⟨κ, hκ, hκae⟩ := environment_uniform_elliptic ν hue
    filter_upwards [hκae, noDrop_positive_limsup ν ℓ e he hp] with ω hω hE
    obtain ⟨n, hn⟩ := (mem_limsup_iff_frequently_mem.mp hE).exists
    have htransfer : ∀ n : ℕ, 0 < noDropQuenched ℓ (n • step e) ω →
        0 < noDropQuenched ℓ 0 ω := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        intro hn
        apply ih
        apply lt_of_lt_of_le _ (noDropQuenched_lower_step ℓ ω (n • step e) e he.le)
        apply ENNReal.mul_pos
        · apply ne_of_gt
          exact_mod_cast (lt_of_lt_of_le hκ (hω (n • step e) e))
        · simpa only [succ_nsmul] using ne_of_gt hn
    exact htransfer n hn
  apply ae_all_iff.mpr
  intro x
  have ht : Measurable (fun ω : Environment d => fun a => ω (x + a)) := by fun_prop
  have hm := environment_translation ν x
  have hmap : ∀ᵐ ω ∂(environmentLaw ν).map (fun η : Environment d => fun a => η (x + a)),
      0 < noDropQuenched ℓ 0 ω := by rwa [hm]
  have ha := (ae_map_iff ht.aemeasurable ((measurable_noDropQuenched ℓ 0) measurableSet_Ioi)).mp hmap
  filter_upwards [ha] with ω hω
  simpa only [noDropQuenched_translation ℓ ω x, Set.mem_Ioi] using hω

lemma quenched_futureNoDrop_zero {d : ℕ} (ℓ : Vector d) (ω : Environment d)
    (x : Lattice d) (hzero : ∀ y, noDropQuenched ℓ y ω = 0) (n : ℕ) :
    quenchedKernel (ω, x) (FutureNoDrop ℓ n) = 0 := by
  let E := fun f : (i : Finset.Iic n) → Lattice d =>
    (fun X : Path d => fun j => X (n + j)) ⁻¹' NoDrop ℓ (extendPrefix n f n) ∩
      pathCylinder (extendPrefix n f) n
  have hE (f : (i : Finset.Iic n) → Lattice d) : quenchedKernel (ω, x) (E f) = 0 := by
    by_cases hf : extendPrefix n f 0 = x
    · change quenchedKernel (ω, x) (_ ∩ _) = 0
      rw [quenched_prefix_future ω x _ hf n (measurableSet_noDrop _ _)]
      change _ * noDropQuenched ℓ _ ω = 0
      rw [hzero, mul_zero]
    · apply measure_mono_null Set.inter_subset_right
      exact quenched_pathCylinder_zero ω x _ hf n
  apply measure_mono_null (t := ⋃ f, E f) _ (measure_iUnion_null hE)
  intro X hX
  apply Set.mem_iUnion.mpr
  refine ⟨fun i => X i, ?_⟩
  constructor
  · change ∀ j, dot (realPosition (extendPrefix n (fun i => X i) n)) ℓ ≤
        dot (realPosition (X (n + j))) ℓ
    simpa [extendPrefix, FutureNoDrop] using hX
  · intro i hi
    simp [extendPrefix, hi]

lemma noDrop_positive_of_directionallyTransient {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    0 < annealedLaw ν (NoDrop ℓ 0) := by
  by_contra hn
  have hzero : annealedLaw ν (NoDrop ℓ 0) = 0 := le_antisymm (le_of_not_gt hn) bot_le
  have hq : ∀ᵐ ω ∂environmentLaw ν, ∀ x, noDropQuenched ℓ x ω = 0 := by
    apply ae_all_iff.mpr
    intro x
    apply (lintegral_eq_zero_iff (measurable_noDropQuenched ℓ x)).mp
    rw [annealed_noDrop_translation ν ℓ x, hzero]
  have hnzero (n : ℕ) : annealedLaw ν (FutureNoDrop ℓ n) = 0 := by
    rw [annealed_apply ν (measurableSet_futureNoDrop ℓ n)]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hq] with ω hω
    exact quenched_futureNoDrop_zero ℓ ω 0 hω n
  have hnone : ∀ᵐ X ∂annealedLaw ν, ∀ n, X ∉ FutureNoDrop ℓ n := by
    apply ae_all_iff.mpr
    intro n
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hnzero n
  have hfalse : ∀ᵐ X ∂annealedLaw ν, False := by
    filter_upwards [htrans, hnone] with X ht hh
    obtain ⟨n, hn⟩ := tendsto_atTop_has_minimum _ ht
    exact hh n (fun i => hn (n + i))
  obtain ⟨X, hX⟩ := hfalse.exists
  exact hX

lemma measurableSet_futureEvent {d : ℕ} (B : Lattice d → Set (Path d))
    (hB : ∀ y, MeasurableSet (B y)) (n : ℕ) : MeasurableSet (FutureEvent B n) := by
  have he : FutureEvent B n = ⋃ y, {X : Path d | X n = y} ∩
      (fun X : Path d => fun j => X (n + j)) ⁻¹' B y := by
    ext X
    simp only [FutureEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro h
      exact ⟨X n, rfl, h⟩
    · rintro ⟨y, rfl, h⟩
      exact h
  rw [he]
  apply MeasurableSet.iUnion
  intro y
  exact (measurableSet_eq_fun (measurable_pi_apply n) measurable_const).inter
    ((by fun_prop : Measurable (fun X : Path d => fun j => X (n + j))) (hB y))

lemma quenched_past_future {d : ℕ} (ω : Environment d) (x : Lattice d) (n : ℕ)
    (C : Set ((i : Finset.Iic n) → Lattice d)) (B : Lattice d → Set (Path d))
    (hB : ∀ y, MeasurableSet (B y)) :
    quenchedKernel (ω, x) ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C ∩ FutureEvent B n) =
      ∫⁻ X in (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C,
        quenchedKernel (ω, X n) (B (X n)) ∂quenchedKernel (ω, x) := by
  classical
  let Q := fun X : Path d => Preorder.frestrictLe n X
  let g := fun f : (i : Finset.Iic n) → Lattice d =>
    quenchedKernel (ω, extendPrefix n f n) (B (extendPrefix n f n))
  have hr : (∫⁻ X in Q ⁻¹' C, quenchedKernel (ω, X n) (B (X n)) ∂quenchedKernel (ω, x)) =
      ∑' f : (i : Finset.Iic n) → Lattice d,
        g f * quenchedKernel (ω, x) (Q ⁻¹' C ∩ pathCylinder (extendPrefix n f) n) := by
    convert lintegral_partition_prefix (quenchedKernel (ω, x)) (Q ⁻¹' C) n g using 1
    all_goals try with_reducible_and_instances rfl
    apply lintegral_congr
    intro X
    simp [g, extendPrefix]
  rw [hr, measure_partition_prefix _ _ n]
  apply tsum_congr
  intro f
  have hcf (X : Path d) (hX : X ∈ pathCylinder (extendPrefix n f) n) : Q X = f := by
    rw [← restrict_prefix_fiber] at hX
    exact hX
  by_cases hC : f ∈ C
  · have hpc : Q ⁻¹' C ∩ pathCylinder (extendPrefix n f) n = pathCylinder (extendPrefix n f) n := by
      apply Set.inter_eq_right.mpr
      intro X hX
      change Q X ∈ C
      simpa only [hcf X hX] using hC
    have hfc : (Q ⁻¹' C ∩ FutureEvent B n) ∩ pathCylinder (extendPrefix n f) n =
        (fun X : Path d => fun j => X (n + j)) ⁻¹' B (extendPrefix n f n) ∩
          pathCylinder (extendPrefix n f) n := by
      ext X
      constructor
      · rintro ⟨⟨_, hF⟩, hX⟩
        exact ⟨by simpa only [FutureEvent, Set.mem_ofPred_eq, Set.mem_preimage, ← hX n le_rfl] using hF, hX⟩
      · rintro ⟨hF, hX⟩
        refine ⟨⟨by change Q X ∈ C; simpa only [hcf X hX] using hC, ?_⟩, hX⟩
        change (fun j => X (n + j)) ∈ B (X n)
        simpa only [Set.mem_preimage, hX n le_rfl] using hF
    change quenchedKernel (ω, x) ((Q ⁻¹' C ∩ FutureEvent B n) ∩ _) = _
    rw [hpc, hfc]
    by_cases hf : extendPrefix n f 0 = x
    · rw [quenched_prefix_future ω x _ hf n (hB _)]
      exact mul_comm _ _
    · rw [quenched_pathCylinder_zero ω x _ hf, mul_zero]
      exact measure_mono_null Set.inter_subset_right (quenched_pathCylinder_zero ω x _ hf n)
  · have hz : Q ⁻¹' C ∩ pathCylinder (extendPrefix n f) n = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨hX, hcy⟩
      exact hC (by simpa only [Set.mem_preimage, hcf X hcy] using hX)
    change quenchedKernel (ω, x) ((Q ⁻¹' C ∩ FutureEvent B n) ∩ _) = _
    rw [hz, measure_empty, mul_zero]
    apply measure_mono_null (t := Q ⁻¹' C ∩ pathCylinder (extendPrefix n f) n)
      (by intro X hX; exact ⟨hX.1.1, hX.2⟩)
    rw [hz, measure_empty]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_Hit
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero _root_.OAI.DirectionalTransience.recordCount_zero _root_.OAI.DirectionalTransience.regenerationTimes_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma quenched_hitAt_future {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (n : ℕ) (B : Lattice d → Set (Path d))
    (hB : ∀ y, MeasurableSet (B y)) :
    quenchedKernel (ω, x) (HitAt S T n ∩ FutureEvent B n) =
      ∫⁻ X in HitAt S T n, quenchedKernel (ω, X n) (B (X n)) ∂quenchedKernel (ω, x) := by
  let C : Set ((i : Finset.Iic n) → Lattice d) :=
    {f | f ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ T ∧ ∀ i : Finset.Iic n, (i : ℕ) < n → f i ∈ S}
  have hC : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C = HitAt S T n := by
    ext X
    constructor
    · intro h
      exact ⟨h.1, fun i hi => h.2 ⟨i, Finset.mem_Iic.mpr hi.le⟩ hi⟩
    · intro h
      exact ⟨h.1, fun i hi => h.2 i hi⟩
  simpa only [hC] using quenched_past_future ω x n C B hB

lemma hitKernel_future {d : ℕ} (ω : Environment d) (x : Lattice d)
    {S T : Set (Lattice d)} (hST : Disjoint S T) (B : Lattice d → Set (Path d))
    (hB : ∀ y, MeasurableSet (B y)) :
    (∫⁻ y, quenchedKernel (ω, y) (B y) ∂hitKernel S T (ω, x)) =
      quenchedKernel (ω, x) (⋃ n, HitAt S T n ∩ FutureEvent B n) := by
  rw [hitKernel, Kernel.sum_apply, lintegral_sum_measure]
  rw [measure_iUnion (fun n m hnm => (hitAt_pairwise_disjoint hST hnm).mono
    Set.inter_subset_left Set.inter_subset_left)
    (fun n => (measurableSet_hitAt S T n).inter (measurableSet_futureEvent B hB n))]
  apply tsum_congr
  intro n
  rw [Kernel.map_apply _ (measurable_pi_apply n),
    lintegral_map (measurable_of_countable _) (measurable_pi_apply n), Kernel.restrict_apply]
  exact (quenched_hitAt_future ω x S T n B hB).symm

lemma hitKernel_noDrop_le {d : ℕ} (ω : Environment d) (x : Lattice d) (ℓ : Vector d)
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    (hS : ∀ y ∈ S, dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ)
    (hT : ∀ y ∈ T, dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ) :
    (∫⁻ y, noDropQuenched ℓ y ω ∂hitKernel S T (ω, x)) ≤ noDropQuenched ℓ x ω := by
  unfold noDropQuenched
  rw [hitKernel_future ω x hST (NoDrop ℓ) (measurableSet_noDrop ℓ)]
  apply measure_mono
  intro X hX
  obtain ⟨n, hn, hF⟩ := Set.mem_iUnion.mp hX
  intro i
  by_cases hi : i < n
  · exact hS _ (hn.2 i hi)
  · have hni : n ≤ i := by omega
    have hh := hF (i - n)
    dsimp only at hh
    rw [Nat.add_sub_of_le hni] at hh
    exact (hT _ hn.1).trans hh

lemma crossingQuenched_tendsto_ae {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ x,
      Tendsto (fun H : ℕ => crossingQuenched ℓ x H ω) atTop (𝓝 (noDropQuenched ℓ x ω)) := by
  filter_upwards [quenched_directionallyTransient_ae ν ℓ htrans] with ω hω
  intro x
  have he : (⋂ H : ℕ, Cross ℓ x H) =ᵐ[quenchedKernel (ω, x)] NoDrop ℓ x := by
    filter_upwards [hω x] with X hX
    apply propext
    constructor
    · exact fun h => iInter_cross_subset_noDrop ℓ x h
    · intro hD
      exact Set.mem_iInter.mpr fun H => noDrop_subset_cross_of_tendsto ℓ x X hX hD H
  have h := tendsto_measure_iInter_atTop
    (μ := quenchedKernel (ω, x)) (s := fun H : ℕ => Cross ℓ x H)
    (fun H => (measurableSet_cross ℓ x H).nullMeasurableSet)
    (fun H K hHK => cross_antitone ℓ x (Nat.cast_le.mpr hHK))
    ⟨0, measure_ne_top _ _⟩
  rw [measure_congr he] at h
  exact h

lemma crossingQuenched_lower_step {d : ℕ} (ℓ : Vector d) (ω : Environment d)
    (x : Lattice d) (e : Direction d) {κ : ℝ≥0}
    (hκ : ∀ y, κ ≤ (ω y).1 e) {H : ℝ} (hH : 0 ≤ H) :
    (κ : ℝ≥0∞) * crossingQuenched ℓ x H ω ≤
      crossingQuenched ℓ x (H + dot (realPosition (step e)) ℓ) ω := by
  let S := Strip ℓ x H
  let T := Upper ℓ x H
  let B := fun y : Lattice d => wordCylinder y [e]
  have hB (y : Lattice d) : MeasurableSet (B y) := measurableSet_wordCylinder y [e]
  have hInt : (κ : ℝ≥0∞) * hitKernel S T (ω, x) Set.univ ≤
      ∫⁻ y, quenchedKernel (ω, y) (B y) ∂hitKernel S T (ω, x) := by
    rw [← lintegral_const]
    apply lintegral_mono
    intro y
    change _ ≤ quenchedKernel (ω, y) (wordCylinder y [e])
    rw [quenched_wordCylinder]
    simpa [wordWeight] using (ENNReal.coe_le_coe.mpr (hκ y))
  rw [hitKernel_future ω x (disjoint_strip_upper ℓ x H) B hB] at hInt
  rw [crossingQuenched_eq_hitKernel ℓ x H]
  refine hInt.trans (measure_mono ?_)
  intro X hX
  obtain ⟨n, hn, hF⟩ := Set.mem_iUnion.mp hX
  have hn1 : X (n + 1) = X n + step e := hF 1 (by simp)
  refine ⟨n + 1, ?_, ?_⟩
  · rw [hn1, dot_realPosition_add]
    have ht : dot (realPosition x) ℓ + H ≤ dot (realPosition (X n)) ℓ := hn.1
    linarith
  · intro i hi
    rcases lt_or_eq_of_le (show i ≤ n by omega) with hi | rfl
    · exact (hn.2 i hi).1
    · exact (le_add_of_nonneg_right hH).trans hn.1

lemma endpointLaw_mean_le {d : ℕ} (ℓ : Vector d) (x : Lattice d) {H : ℝ} (hH : 0 ≤ H)
    (ω : Environment d) :
    (∫⁻ y, noDropQuenched ℓ y ω ∂endpointLaw ℓ x H ω) ≤
      noDropQuenched ℓ x ω / crossingQuenched ℓ x H ω := by
  rw [endpointLaw, lintegral_smul_measure, smul_eq_mul, ENNReal.div_eq_inv_mul]
  apply mul_le_mul_right
  exact hitKernel_noDrop_le ω x ℓ (disjoint_strip_upper ℓ x H)
    (fun _ hy => hy.1) (fun _ hy => (le_add_of_nonneg_right hH).trans hy)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FirstBelow
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero _root_.OAI.DirectionalTransience.recordCount_zero _root_.OAI.DirectionalTransience.regenerationTimes_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma endpointLaw_small_ratio {d : ℕ} (ℓ : Vector d) (x : Lattice d) {H : ℝ} (hH : 0 ≤ H)
    (ω : Environment d) {s : ℝ≥0} (hs : 0 < s)
    (hq : noDropQuenched ℓ x ω < (s : ℝ≥0∞) * crossingQuenched ℓ x H ω) :
    (1 : ℝ≥0∞) ≤ 2 * endpointLaw ℓ x H ω {y | noDropQuenched ℓ y ω ≤ 2 * (s : ℝ≥0∞)} := by
  have ha : crossingQuenched ℓ x H ω ≠ 0 := by
    intro he
    rw [he, mul_zero] at hq
    exact not_lt_zero hq
  let : IsProbabilityMeasure (endpointLaw ℓ x H ω) := ⟨endpointLaw_total ℓ x H ω ha⟩
  apply mass_of_small_mean _ _ (measurable_of_countable _) hs
  apply (endpointLaw_mean_le ℓ x hH ω).trans
  exact le_of_lt ((ENNReal.div_lt_iff (Or.inl ha)
    (Or.inl (crossingQuenched_ne_top ℓ x H ω))).mpr hq)

lemma noDropQuenched_small_translation {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (y : Lattice d) (c : ℝ≥0∞) :
    environmentLaw ν {ω | noDropQuenched ℓ y ω ≤ c} =
      environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ c} := by
  have he := congrArg (fun μ : Measure (Environment d) =>
    μ {ω | noDropQuenched ℓ 0 ω ≤ c}) (environment_translation ν y)
  rw [Measure.map_apply (by fun_prop)
    (measurableSet_le (measurable_noDropQuenched ℓ 0) measurable_const)] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext ω
  change noDropQuenched ℓ y ω ≤ c ↔ noDropQuenched ℓ 0 (fun a => ω (y + a)) ≤ c
  rw [noDropQuenched_translation]

lemma endpointLaw_badmass {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) {H : ℝ} (hH : 0 < H)
    {A : Set (Environment d)} (hA : MeasurableSet[rowSigma (Strip ℓ x H)] A)
    (c : ℝ≥0∞) :
    (∫⁻ ω, A.indicator (fun ω => endpointLaw ℓ x H ω
      {y | noDropQuenched ℓ y ω ≤ c}) ω ∂environmentLaw ν) ≤
      environmentLaw ν A * environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ c} := by
  let w := fun (y : Lattice d) => A.indicator (fun ω => endpointLaw ℓ x H ω {y})
  let B := fun y : Lattice d => {ω | noDropQuenched ℓ y ω ≤ c}
  have hw (y : Lattice d) : @Measurable _ _ (rowSigma (Strip ℓ x H)) _ (w y) :=
    (measurable_endpointLaw_rows ℓ x hH {y}).indicator hA
  have hB (y : Lattice d) : MeasurableSet (B y) :=
    measurableSet_le (measurable_noDropQuenched ℓ y) measurable_const
  have hwB (y : Lattice d) : Measurable (fun ω => w y ω * (B y).indicator 1 ω) :=
    ((hw y).mono (rowSigma_le _) le_rfl).mul (measurable_const.indicator (hB y))
  have he (ω : Environment d) :
      A.indicator (fun ω => endpointLaw ℓ x H ω {y | noDropQuenched ℓ y ω ≤ c}) ω =
        ∑' y, w y ω * (B y).indicator 1 ω := by
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, ← Measure.tsum_indicator_apply_singleton _ _
        (Set.to_countable _).measurableSet]
      apply tsum_congr
      intro y
      by_cases hy : noDropQuenched ℓ y ω ≤ c
      · simp [w, B, hω, hy]
      · simp [w, B, hω, hy]
    · simp [w, hω]
  simp_rw [he]
  rw [lintegral_tsum (fun y => (hwB y).aemeasurable)]
  have hf (y : Lattice d) :
      (∫⁻ ω, w y ω * (B y).indicator 1 ω ∂environmentLaw ν) =
        (∫⁻ ω, w y ω ∂environmentLaw ν) *
          environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ c} := by
    by_cases hy : y ∈ Upper ℓ x H
    · have hST : Disjoint (Strip ℓ x H)
          {z | dot (realPosition y) ℓ ≤ dot (realPosition z) ℓ} := by
        apply Set.disjoint_left.mpr
        intro z hz hz'
        have hy' : dot (realPosition x) ℓ + H ≤ dot (realPosition y) ℓ := hy
        exact (not_le_of_gt hz.2) (hy'.trans hz')
      have hmB : @Measurable _ _ (rowSigma {z | dot (realPosition y) ℓ ≤ dot (realPosition z) ℓ}) _
          ((B y).indicator (1 : Environment d → ℝ≥0∞)) :=
        measurable_const.indicator (measurableSet_le
          (measurable_noDropQuenched_rows ℓ y) measurable_const)
      rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
        (rowSigma_le _) (rowSigma_le _) (environment_indep_rows ν hST) (hw y) hmB,
        lintegral_indicator_one (hB y)]
      rw [noDropQuenched_small_translation ν ℓ y c]
    · have hew : w y = 0 := by
        funext ω
        change A.indicator (fun ω => endpointLaw ℓ x H ω {y}) ω = 0
        by_cases hω : ω ∈ A
        · rw [Set.indicator_of_mem hω, endpointLaw_supported ℓ x H ω hy]
        · exact Set.indicator_of_notMem hω _
      simp [hew]
  simp_rw [hf]
  rw [ENNReal.tsum_mul_right, ← lintegral_tsum
    (fun y => ((hw y).mono (rowSigma_le _) le_rfl).aemeasurable)]
  apply mul_le_mul' _ le_rfl
  calc
    (∫⁻ ω, ∑' y, w y ω ∂environmentLaw ν) ≤ ∫⁻ ω, A.indicator 1 ω ∂environmentLaw ν := by
      apply lintegral_mono
      intro ω
      by_cases hω : ω ∈ A
      · simp only [w, Set.indicator_of_mem hω, Pi.one_apply]
        have hh := Measure.tsum_indicator_apply_singleton (endpointLaw ℓ x H ω) Set.univ MeasurableSet.univ
        simp only [Set.indicator_univ] at hh
        rw [hh]
        exact endpointLaw_total_le_one ℓ x H ω
      · simp [w, hω]
    _ = environmentLaw ν A := lintegral_indicator_one (rowSigma_le _ _ hA)

lemma stopped_layer_small_ratio {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) {H : ℝ} (hH : 0 < H)
    {A : Set (Environment d)} (hA : MeasurableSet[rowSigma (Strip ℓ x H)] A)
    {s : ℝ≥0} (hs : 0 < s) :
    environmentLaw ν (A ∩ {ω | noDropQuenched ℓ x ω <
      (s : ℝ≥0∞) * crossingQuenched ℓ x H ω}) ≤
        2 * environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ 2 * (s : ℝ≥0∞)} *
          environmentLaw ν A := by
  let E := {ω | noDropQuenched ℓ x ω < (s : ℝ≥0∞) * crossingQuenched ℓ x H ω}
  have hE : MeasurableSet E := measurableSet_lt (measurable_noDropQuenched ℓ x)
    (measurable_const.mul ((measurable_crossingQuenched_rows ℓ x hH).mono (rowSigma_le _) le_rfl))
  have hA' : MeasurableSet A := rowSigma_le _ _ hA
  rw [← lintegral_indicator_one (hA'.inter hE)]
  calc
    (∫⁻ ω, (A ∩ E).indicator 1 ω ∂environmentLaw ν) ≤
        ∫⁻ ω, 2 * A.indicator (fun ω => endpointLaw ℓ x H ω
          {y | noDropQuenched ℓ y ω ≤ 2 * (s : ℝ≥0∞)}) ω ∂environmentLaw ν := by
      apply lintegral_mono
      intro ω
      change (A ∩ E).indicator 1 ω ≤ 2 * A.indicator (fun ω => endpointLaw ℓ x H ω
        {y | noDropQuenched ℓ y ω ≤ 2 * (s : ℝ≥0∞)}) ω
      by_cases hω : ω ∈ A ∩ E
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω.1]
        exact endpointLaw_small_ratio ℓ x hH.le ω hs hω.2
      · rw [Set.indicator_of_notMem hω]
        exact zero_le
    _ = 2 * ∫⁻ ω, A.indicator (fun ω => endpointLaw ℓ x H ω
          {y | noDropQuenched ℓ y ω ≤ 2 * (s : ℝ≥0∞)}) ω ∂environmentLaw ν :=
      lintegral_const_mul' _ _ ENNReal.ofNat_ne_top
    _ ≤ 2 * (environmentLaw ν A *
        environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ 2 * (s : ℝ≥0∞)}) :=
      mul_le_mul' le_rfl (endpointLaw_badmass ν ℓ x hH hA _)
    _ = _ := by ac_rfl

lemma crossingQuenched_mesh_tendsto {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) {m : ℝ} (hm : 0 < m)
    (htrans : ∀ᵐ X ∂quenchedKernel (ω, x), X ∈ TransientPaths ℓ) :
    Tendsto (fun n : ℕ => crossingQuenched ℓ x (n * m) ω) atTop
      (𝓝 (noDropQuenched ℓ x ω)) := by
  have he : (⋂ n : ℕ, Cross ℓ x (n * m)) =ᵐ[quenchedKernel (ω, x)] NoDrop ℓ x := by
    filter_upwards [htrans] with X hX
    apply propext
    constructor
    · intro h
      apply iInter_cross_subset_noDrop ℓ x
      apply Set.mem_iInter.mpr
      intro H
      obtain ⟨n, hn⟩ := exists_nat_ge ((H : ℝ) / m)
      exact cross_antitone ℓ x ((div_le_iff₀ hm).mp hn) (Set.mem_iInter.mp h n)
    · intro hD
      exact Set.mem_iInter.mpr fun n => noDrop_subset_cross_of_tendsto ℓ x X hX hD (n * m)
  have h := tendsto_measure_iInter_atTop
    (μ := quenchedKernel (ω, x)) (s := fun n : ℕ => Cross ℓ x (n * m))
    (fun n => (measurableSet_cross ℓ x (n * m)).nullMeasurableSet)
    (fun n k hnk => cross_antitone ℓ x (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnk) hm.le))
    ⟨0, measure_ne_top _ _⟩
  rw [measure_congr he] at h
  exact h

lemma noDrop_small_recursive {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (he : 0 < dot (realPosition (step e)) ℓ)
    (htrans : DirectionallyTransient ν ℓ) {κ : ℝ≥0}
    (hκ : ∀ᵐ ω ∂environmentLaw ν, ∀ x, κ ≤ (ω x).1 e)
    {t r s : ℝ≥0} (ht : t < 1) (hrt : r ≤ t) (hs : 0 < s)
    (hr : r ≤ s * κ * t) :
    environmentLaw ν {ω | noDropQuenched ℓ 0 ω < (r : ℝ≥0∞)} ≤
      (2 * environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ 2 * (s : ℝ≥0∞)}) *
        environmentLaw ν {ω | noDropQuenched ℓ 0 ω < (t : ℝ≥0∞)} := by
  let m := dot (realPosition (step e)) ℓ
  let a := fun (n : ℕ) (ω : Environment d) => crossingQuenched ℓ 0 (n * m) ω
  let A := fun n => {ω | FirstBelow (fun k => a k ω) (t : ℝ≥0∞) n}
  let B := {ω | noDropQuenched ℓ 0 ω < (r : ℝ≥0∞)}
  let C := {ω | noDropQuenched ℓ 0 ω < (t : ℝ≥0∞)}
  let ρ := 2 * environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ 2 * (s : ℝ≥0∞)}
  have hAm (n : ℕ) : MeasurableSet (A n) := rowSigma_le _ _
    (measurableSet_firstBelow_crossing ℓ 0 he t n)
  have hB : MeasurableSet B := measurableSet_lt (measurable_noDropQuenched ℓ 0) measurable_const
  have hpair : Pairwise (fun n k => Disjoint (A n) (A k)) := firstBelow_pairwise_disjoint a t
  have hlim : ∀ᵐ ω ∂environmentLaw ν, Tendsto (fun n => a n ω) atTop (𝓝 (noDropQuenched ℓ 0 ω)) := by
    filter_upwards [quenched_directionallyTransient_ae ν ℓ htrans] with ω hω
    exact crossingQuenched_mesh_tendsto ℓ 0 ω he (hω 0)
  have hAC : (⋃ n, A n) =ᵐ[environmentLaw ν] C := by
    filter_upwards [hlim] with ω hω
    apply propext
    change (ω ∈ ⋃ n, A n) ↔ ω ∈ C
    rw [Set.mem_iUnion]
    change (∃ n, FirstBelow (fun k => a k ω) (t : ℝ≥0∞) n) ↔ _
    rw [firstBelow_iff_exists (fun k => a k ω)]
    constructor
    · rintro ⟨n, hn⟩
      exact lt_of_le_of_lt ((show Antitone (fun k => a k ω) from fun i j hij =>
        crossingQuenched_antitone ℓ 0 ω (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) he.le)).le_of_tendsto hω n) hn
    · intro h
      exact (hω.eventually (eventually_lt_nhds h)).exists
  have hBA : (⋃ n, A n ∩ B) =ᵐ[environmentLaw ν] B := by
    filter_upwards [hAC] with ω hω
    apply propext
    constructor
    · intro h
      exact (Set.mem_iUnion.mp h).choose_spec.2
    · intro h
      have hc : ω ∈ C := lt_of_lt_of_le h (ENNReal.coe_le_coe.mpr hrt)
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hω.mpr hc)
      exact Set.mem_iUnion.mpr ⟨n, hn, h⟩
  have hstep (n : ℕ) : environmentLaw ν (A n ∩ B) ≤ ρ * environmentLaw ν (A n) := by
    by_cases hn : n = 0
    · subst n
      have heA : A 0 = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro ω hω
        have hh := hω.1
        simp only [a, Nat.cast_zero, zero_mul, crossingQuenched_zero] at hh
        exact (not_lt_of_ge (ENNReal.coe_le_coe.mpr ht.le)) hh
      simp [heA]
    · have hm : 0 < (n : ℝ) * m := mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) he
      apply le_trans (measure_mono_ae (t := A n ∩ {ω | noDropQuenched ℓ 0 ω <
        (s : ℝ≥0∞) * a n ω}) ?_) (stopped_layer_small_ratio ν ℓ 0 hm
          (measurableSet_firstBelow_crossing ℓ 0 he t n) hs)
      filter_upwards [hκ] with ω hω
      intro h
      refine ⟨h.1, ?_⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hprev : (t : ℝ≥0∞) ≤ a k ω := h.1.2 k (Nat.lt_succ_self k)
      have hstep := crossingQuenched_lower_step ℓ ω 0 e hω
        (show 0 ≤ (k : ℝ) * m from mul_nonneg (Nat.cast_nonneg _) he.le)
      have hlow : (κ : ℝ≥0∞) * (t : ℝ≥0∞) ≤ a (k + 1) ω := by
        apply (mul_le_mul' le_rfl hprev).trans
        simpa [a, Nat.cast_add, Nat.cast_one, add_mul] using hstep
      exact lt_of_lt_of_le h.2 ((ENNReal.coe_le_coe.mpr hr).trans (by
        push_cast
        rw [mul_assoc]
        exact mul_le_mul' le_rfl hlow))
  change environmentLaw ν B ≤ ρ * environmentLaw ν C
  rw [← measure_congr hBA, measure_iUnion
    (fun i j hij => (hpair hij).mono Set.inter_subset_left Set.inter_subset_left)
    (fun n => (hAm n).inter hB)]
  calc
    ∑' n, environmentLaw ν (A n ∩ B) ≤ ∑' n, ρ * environmentLaw ν (A n) := ENNReal.tsum_le_tsum hstep
    _ = ρ * ∑' n, environmentLaw ν (A n) := ENNReal.tsum_mul_left
    _ = ρ * environmentLaw ν C := by rw [← measure_iUnion hpair hAm, measure_congr hAC]

lemma noDrop_geometric_tail {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (e : Direction d)
    (he : 0 < dot (realPosition (step e)) ℓ) (htrans : DirectionallyTransient ν ℓ) :
    ∃ δ : ℝ≥0, ∃ ρ : ℝ≥0∞, 0 < δ ∧ δ < 1 ∧ ρ < 1 ∧
      ∀ j : ℕ, environmentLaw ν {ω | noDropQuenched ℓ 0 ω < ((δ ^ (j + 1) : ℝ≥0) : ℝ≥0∞)} ≤ ρ ^ j := by
  obtain ⟨κ, hκ, hκae⟩ := environment_uniform_elliptic ν hue
  have hκle : κ ≤ 1 := by
    obtain ⟨ω, hω⟩ := hκae.exists
    exact (hω 0 e).trans (row_entry_le_one _ e)
  have hp := noDropQuenched_positive_ae ν hue ℓ e he
    (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  obtain ⟨s, hs, hsle, hsμ⟩ := positive_random_small_set (environmentLaw ν)
    (noDropQuenched ℓ 0) (measurable_noDropQuenched ℓ 0) (hp.mono fun _ h => h 0)
  let δ := s * κ
  let ρ := 2 * environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ 2 * (s : ℝ≥0∞)}
  have hδ : 0 < δ := mul_pos hs hκ
  have hδle : δ < 1 := by
    have hle : δ ≤ 1 / 4 := (mul_le_mul' hsle hκle).trans (by norm_num)
    exact hle.trans_lt (by norm_num)
  have hρ : ρ < 1 := by
    apply lt_of_lt_of_le (b := (2 : ℝ≥0∞) * (1 / 4))
    · exact ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hsμ
    · rw [one_div, ENNReal.mul_inv_le_iff (by norm_num) (by norm_num)]
      norm_num
  refine ⟨δ, ρ, hδ, hδle, hρ, ?_⟩
  intro j
  induction j with
  | zero => rw [pow_zero]; exact prob_le_one
  | succ j ih =>
    have hrec := noDrop_small_recursive ν ℓ e he htrans
      (hκae.mono fun _ h x => h x e)
      (t := δ ^ (j + 1)) (r := δ ^ (j + 1 + 1)) (s := s)
      (pow_lt_one₀ hδ.le hδle (by omega))
      (by rw [pow_succ]; exact mul_le_of_le_one_right zero_le hδle.le) hs
      (by rw [pow_succ]; dsimp [δ]; ring_nf; rfl)
    calc
      _ ≤ ρ * environmentLaw ν {ω | noDropQuenched ℓ 0 ω < ((δ ^ (j + 1) : ℝ≥0) : ℝ≥0∞)} := hrec
      _ ≤ ρ * ρ ^ j := mul_le_mul' le_rfl ih
      _ = ρ ^ (j + 1) := (pow_succ' ρ j).symm

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_LowerClip
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma quenched_noDrop_positive_of_directionallyTransient {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ x, 0 < noDropQuenched ℓ x ω := by
  obtain ⟨e, he⟩ := exists_positive_step ℓ hℓ
  exact noDropQuenched_positive_ae ν hue ℓ e he
    (noDrop_positive_of_directionallyTransient ν ℓ htrans)

lemma noDrop_inverse_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) :
    ∃ lam : ℝ, 0 < lam ∧
      (∫⁻ ω, noDropQuenched ℓ 0 ω ^ (-lam) ∂environmentLaw ν) < ∞ := by
  obtain ⟨e, he⟩ := exists_positive_step ℓ hℓ
  obtain ⟨δ, ρ, hδ, hδ1, hρ, htail⟩ := noDrop_geometric_tail ν hue ℓ e he htrans
  apply inverse_moment_of_geometric_tail (environmentLaw ν) (noDropQuenched ℓ 0)
    (measurable_noDropQuenched ℓ 0) _ hδ hδ1 hρ htail
  filter_upwards [quenched_noDrop_positive_of_directionallyTransient ν hue ℓ hℓ htrans] with ω hω
  exact ⟨hω 0, measure_ne_top _ _⟩

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ClippedInverse
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def clippedNoDropProduct {d k : ℕ} (ℓ : Vector d) (δ : ℝ)
    (x : Fin k → Lattice d) (ω : Environment d) : ℝ :=
  ∏ i, max (noDropQuenched ℓ (x i) ω).toReal δ

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_RegenerationWords
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma recordIndexPrefix_prefix {d : ℕ} (ℓ : Vector d) (r n : ℕ) :
    PrefixDetermined n (RecordIndexPrefix ℓ r n) := by
  intro X Y hXY
  have hr := strictRecord_congr_prefix ℓ (le_refl n) hXY
  have hc := recordCount_congr_prefix ℓ hXY
  simp only [RecordIndexPrefix, Set.mem_ofPred_eq, hr, hc]
  have hh : (∀ j ≤ n, dot (realPosition (0 : Lattice d)) ℓ ≤ dot (realPosition (X j)) ℓ) ↔
      (∀ j ≤ n, dot (realPosition (0 : Lattice d)) ℓ ≤ dot (realPosition (Y j)) ℓ) :=
    forall_congr' fun j => forall_congr' fun hj => by rw [hXY j hj]
  rw [hh]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_FixedQuenchedKernel
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

instance fixedQuenchedKernel_markov {d : ℕ} (x : Lattice d) :
    IsMarkovKernel (fixedQuenchedKernel x) := by unfold fixedQuenchedKernel; infer_instance

noncomputable def annealedFrom {d : ℕ} (ν : Measure (Row d)) (x : Lattice d) :
    Measure (Path d) := fixedQuenchedKernel x ∘ₘ environmentLaw ν

instance annealedFrom_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (x : Lattice d) : IsProbabilityMeasure (annealedFrom ν x) := by
  unfold annealedFrom
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def conditionedFrom {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (x : Lattice d) : Measure (Path d) :=
  (annealedLaw ν (NoDrop ℓ 0))⁻¹ • (annealedFrom ν x).restrict (NoDrop ℓ x)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AlignedRecordPrefix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma recordOrZeroPrefix_prefix {d : ℕ} (ℓ : Vector d) (r n : ℕ) :
    PrefixDetermined n (RecordOrZeroPrefix ℓ r n) := by
  intro X Y hXY
  unfold RecordOrZeroPrefix
  split_ifs
  · rfl
  · exact recordIndexPrefix_prefix ℓ r n X Y hXY

noncomputable def commonBoundaryGap {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (h : ℕ) (P : Path d × Path d) : ℝ :=
  realPartialSum (fun k => commonIncrementProcess ℓ e k P)
    (renewalCount (fun k => commonWidthProcess ℓ k P) h)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_TubePrefix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma quenched_prefix_event_congr {d : ℕ} (S : Set (Lattice d))
    (ω η : Environment d) (hωη : Set.EqOn ω η S) (x : Lattice d) (n : ℕ)
    (A : Set (Path d)) (hA : PrefixDetermined n A)
    (hAS : ∀ X ∈ A, ∀ j < n, X j ∈ S) :
    quenchedKernel (ω,x) A = quenchedKernel (η,x) A := by
  let C : Set ((i : Finset.Iic n) → Lattice d) := {f | extendPrefix n f ∈ A}
  have he : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C = A := by
    ext X
    exact hA (extendPrefix n (Preorder.frestrictLe n X)) X
      (fun j hj => by rw [extendPrefix_apply _ _ _ hj]; rfl)
  have hm (f : (i : Finset.Iic n) → Lattice d) (_ : f ∈ C) :
      MeasurableSet ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' {f}) :=
    (Preorder.measurable_frestrictLe n) (measurableSet_singleton f)
  rw [← he,← tsum_measure_preimage_singleton C.to_countable hm,
    ← tsum_measure_preimage_singleton C.to_countable hm]
  apply tsum_congr
  intro f
  rw [restrict_prefix_fiber]
  exact pathCylinder_weight_locality S ω η hωη x (extendPrefix n f.val) n (hAS _ f.property)

lemma measurable_quenched_prefix_event_rows {d : ℕ} (S : Set (Lattice d))
    (x : Lattice d) (hx : x ∈ S) (n : ℕ) (A : Set (Path d))
    (hA : MeasurableSet A) (hprefix : PrefixDetermined n A)
    (hAS : ∀ X ∈ A, ∀ j < n, X j ∈ S) :
    @Measurable _ _ (rowSigma S) _ (fun ω : Environment d => quenchedKernel (ω,x) A) := by
  apply measurable_of_row_locality _
    ((Kernel.measurable_coe _ hA).comp (measurable_id.prodMk measurable_const)) S x hx
  intro ω η h
  exact quenched_prefix_event_congr S ω η h x n A hprefix hAS

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_TubePrefixMass
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def TubeThreat {d : ℕ} (ℓ : Vector d) (f : Direction d) (a θ z δ : ℝ)
    (H : ℕ) : Set (Measure (Lattice d) × Environment d) :=
  {p | ∃ s, 0 < s ∧ s ≤ H ∧ (tubeLayerMass ℓ f a θ z s p.1 p.2).toReal < δ}

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_TubeEndpoint
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def tubeEndpoint {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (θ z : ℝ) (s : ℕ) (ω : Environment d) : Measure (Lattice d) :=
  Measure.sum fun n => ((quenchedKernel (ω,x)).restrict (TubePrefixAt ℓ f x θ z s n)).map (fun X => X n)

noncomputable def tubeEndpointMixture {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ z : ℝ) (s : ℕ) (π : Measure (Lattice d)) (ω : Environment d) : Measure (Lattice d) :=
  Measure.sum fun x => π {x} • tubeEndpoint ℓ f x θ z s ω

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_StoppedTubeEndpoint
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def stoppedTubeEndpoint {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ z : ℝ) (s : ℕ) (π : Measure (Lattice d)) (ω : Environment d) : Measure (Lattice d) :=
  if s=0 then π else tubeEndpointMixture ℓ f θ z s π ω

noncomputable def bridgedRestart {d : ℕ} (e f : Direction d) (x₀ : Lattice d)
    (θ z : ℝ) (π : Measure (Lattice d)) (s : ℕ) (ω : Environment d) : Measure (Lattice d) :=
  if s=0 then π else probabilityNormalize
    (directBridge e (stoppedTubeEndpoint (realPosition (step e)) f θ z (s-1) π ω) ω)
    (x₀+s • step e)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePrefix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curvePrefixAt_prefix {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s n : ℕ) : PrefixDetermined n (CurvePrefixAt ℓ f x b z s n) := by
  have hdir (X Y : Path d) (hXY : ∀ j ≤ n, X j=Y j)
      (hX : X ∈ CurvePrefixAt ℓ f x b z s n) : Y ∈ CurvePrefixAt ℓ f x b z s n := by
    refine ⟨⟨by simpa only [← hXY n le_rfl] using hX.1.1,
      fun j hj => by simpa only [← hXY j hj.le] using hX.1.2 j hj⟩,?_⟩
    intro j hj
    obtain ⟨a,ha,hrec,hgood⟩ := hX.2 j hj
    refine ⟨a,ha,(recordOrZeroPrefix_prefix ℓ j a _ _
      (fun k hk => by rw [hXY k (hk.trans ha)])).mp hrec,?_⟩
    simpa only [← hXY a ha] using hgood
  intro X Y h
  exact ⟨hdir X Y h,hdir Y X (fun j hj => (h j hj).symm)⟩

lemma curveEndpoint_rows {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) {s : ℕ} (hs : 0 < s) :
    @Measurable _ _ (rowSigma (Strip ℓ x s)) _ (curveEndpoint ℓ f x b z s) := by
  let : MeasurableSpace (Environment d) := rowSigma (Strip ℓ x s)
  apply Measure.measurable_of_measurable_coe
  intro U _
  simp_rw [curveEndpoint_apply]
  apply Measurable.tsum; intro n
  apply measurable_quenched_prefix_event_rows (Strip ℓ x s) x
    (show x ∈ Strip ℓ x s from ⟨le_rfl,lt_add_of_pos_right _ (by exact_mod_cast hs)⟩) n
  · exact ((measurable_pi_apply n) U.to_countable.measurableSet).inter (measurableSet_curvePrefixAt ℓ f x b z s n)
  · intro X Y hXY
    exact and_congr (by rw [Set.mem_preimage,Set.mem_preimage,hXY n le_rfl])
      (curvePrefixAt_prefix ℓ f x b z s n X Y hXY)
  · exact fun _ hX => hX.2.1.2

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def curveWordEvent {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) : Lattice d → List (Lattice d) → Set (Path d)
  | _, [] => Set.univ
  | x, u::w => ⋃ n, CurvePrefixAt ℓ f x b B H n ∩
      FutureEvent (fun y => if y=x+u then curveWordEvent ℓ f b B H y w else ∅) n

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicy
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curveIncrement_rows {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) :
    @Measurable _ _ (rowSigma (Strip ℓ x H)) _ (curveIncrement ℓ f x b B H) := by
  exact (Measure.measurable_map _ (measurable_of_countable _)).comp (curveEndpoint_rows ℓ f x b B hH)

lemma curvePolicy_rows {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (E : Set (Lattice d))
    (δ α : ℝ≥0∞) (dummy : Lattice d) :
    @Measurable _ _ (rowSigma (Strip ℓ x H)) _ (curvePolicy ℓ f x b B H E δ α dummy) := by
  let : MeasurableSpace (Environment d) := rowSigma (Strip ℓ x H)
  have hm := curveIncrement_rows ℓ f x b B hH
  have hc := measurable_crossingQuenched_rows ℓ x (show (0:ℝ)<H by exact_mod_cast hH)
  exact selectedFiniteKernel_measurable _ hm E E.to_countable.measurableSet dummy _ _
    (measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp hm) measurable_const)
    (measurableSet_le (measurable_const.mul hc)
      ((Measure.measurable_coe E.to_countable.measurableSet).comp hm))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicyPMF
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curvePolicy_average_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) :
    IsProbabilityMeasure ((environmentLaw ν).bind (curvePolicy ℓ f 0 b B H E δ α dummy)) := by
  have hm := (curvePolicy_rows ℓ f 0 b B hH E δ α dummy).mono (rowSigma_le _) le_rfl
  have (ω : Environment d) := curvePolicy_probability ℓ f 0 b B H E hδ hα dummy ω
  constructor
  rw [Measure.bind_apply MeasurableSet.univ hm.aemeasurable]
  simp

noncomputable def curvePolicy_average {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) : PMF (Lattice d) :=
  let := curvePolicy_average_probability ν ℓ f b B hH E hδ hα dummy
  ((environmentLaw ν).bind (curvePolicy ℓ f 0 b B H E δ α dummy)).toPMF

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_CurvePolicyKernel
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

noncomputable def curvePolicyKernel {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) (δ α : ℝ≥0∞) (dummy : Lattice d) :
    Kernel (Environment d) (Lattice d) where
  toFun := curvePolicy ℓ f x b B H E δ α dummy
  measurable' := (curvePolicy_rows ℓ f x b B hH E δ α dummy).mono (rowSigma_le _) le_rfl

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_JointPastRestart
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

noncomputable def boundarySuffix {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d) :
    Path d × Path d := commonPairSuffix (boundaryTimes ℓ H P).1 (boundaryTimes ℓ H P).2 P

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ObservedCharges
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

noncomputable def allocatedSmallCuts {d : ℕ} (e f : Direction d) (s : ℝ)
    (P : Path d × Path d) (n : ℕ) : Finset ℕ :=
  (Finset.range (signedHeight e (P.1 n)-signedHeight e (P.1 0)).toNat).filter fun h =>
    P ∈ CommonLayer (realPosition (step e)) (signedHeight e) (signedHeight e (P.1 0)+h) ∧
      |physicalFirstHitGap (realPosition (step e)) f (P.1 0) (P.2 0) h P| ≤ s

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_ClippedPairGrowth
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
noncomputable def centralPrefixMass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ z : ℝ) (H : ℕ) (ω : Environment d) (x : Lattice d) : ℝ :=
  (quenchedKernel (ω,x)).real (TubePrefix ℓ f x θ z H)
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedProfile
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def seedHalfProfile {d : ℕ} (e f : Direction d) (a s : ℤ) (upper : Bool)
    (μ : SeedProfile e a) : SeedProfile e a :=
  ⟨seedHalf f s upper μ.val,seedHalf_inherits f s upper μ.val _ μ.property⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedOrder
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def seedCentralInput {d : ℕ} (e f : Direction d) (a s : ℤ) (k : ℕ)
    (q : SeedState e a) (i : ℕ) : SeedProfile e a :=
  if q.1 < k ∧ i=q.1-1 then seedHalfProfile e f a s false (q.2 i) else q.2 i

def SeedStateOrdered {d : ℕ} (f : Direction d) (s : ℤ) (g : ℝ) {e : Direction d} {a : ℤ}
    (q : SeedState e a) : Prop := ∀ i j, i < j → j < q.1 → SeedOrdered f s g (q.2 i).measure (q.2 j).measure

def SeedStateRetained {d : ℕ} (e : Direction d) (a : ℤ) (H : ℕ) (π : Measure (Lattice d))
    (ω : Environment d) (δ : ℝ≥0∞) (q : SeedState e a) : Prop :=
  ∀ i < q.1, δ • (q.2 i).measure ≤ seedEndpointRaw e H (fun _ _ => True) π ω

noncomputable def SeedPreserved {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z c : ℝ) (q : SeedState e a) (ω : Environment d) : Prop :=
  ∀ i < q.1, c ≤ (seedEndpointRaw e H (SeedCentral f H θ z)
    (seedCentralInput e f a s k q i).measure ω Set.univ).toReal

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayTopology
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace DirectionalTransience.StationaryCompact

variable {H R : Type*}
  [TopologicalSpace H] [DiscreteTopology H] [Countable H]
  [TopologicalSpace R] [CompactSpace R] [T2Space R] [SecondCountableTopology R]

instance array_metrizable : MetrizableSpace (EpisodeArray H R) := inferInstance

end DirectionalTransience.StationaryCompact

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_Array
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.annealedLaw_probability _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.environmentLaw_probability _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.initialLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.quenchedKernel_markov _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.stateTrajectory_markov _root_.OAI.DirectionalTransience.state_measurableEq _root_.OAI.DirectionalTransience.state_measurableSingleton _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped NNReal ENNReal BigOperators Classical
namespace DirectionalTransience

instance actualArray_metrizable {d : ℕ} (e : Direction d) : MetrizableSpace (ActualEpisodeArray e) := inferInstance

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_AnchorEntropy
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def currentStoppedProfile {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ) (ω : Environment d) : Measure (HorizontalSpace e) :=
  globalHorizontalProfile e (τ ω) ω

instance currentStoppedProfile_probability {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ) (ω : Environment d) :
    IsProbabilityMeasure (currentStoppedProfile e τ ω) := by
  unfold currentStoppedProfile
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma currentStoppedProfile_measurable {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ) (hτ : Measurable τ) :
    Measurable (currentStoppedProfile e τ) := by
  change Measurable (fun ω : Environment d => globalHorizontalProfile e (τ ω) ω)
  have h := (globalHorizontalProfile_joint_measurable e).comp (measurable_id.prodMk hτ)
  simpa only [Function.comp_def,id_eq] using h

noncomputable def currentAnchorKernel {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ) (hτ : Measurable τ) :
    Kernel (Environment d) (ℕ → HorizontalSpace e) where
  toFun ω := Measure.infinitePi (fun _ => currentStoppedProfile e τ ω)
  measurable' := AnchorSampling.measurable_infinitePi _
    (fun _ => currentStoppedProfile_measurable e τ hτ)

instance currentAnchorKernel_markov {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ) (hτ : Measurable τ) :
    IsMarkovKernel (currentAnchorKernel e τ hτ) where
  isProbabilityMeasure ω := by
    change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => currentStoppedProfile e τ ω))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_InputMarginal
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def currentInput {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ)
    (X : EpisodeInput e) : (Environment d × (ℕ → HorizontalSpace e)) × LocalUpperField e :=
  ((X.1.1,fun a => X.1.2 (i,a)),X.2 (i,m))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_WindowProjection
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def currentWindowReference {d : ℕ} (e : Direction d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] :
    Kernel (ReferenceClasses.Data (HorizontalSpace e) × CurrentProfiles e)
      (ReferenceClasses.AllFields (HorizontalSpace e) (Row d)) :=
  (ReferenceClasses.reference ν).comap Prod.fst measurable_fst

instance currentWindowReference_markov {d : ℕ} (e : Direction d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] : IsMarkovKernel (currentWindowReference e ν) := by
  unfold currentWindowReference
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def actualCurrentWindow {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (i : ℤ) (m : ℕ) (X : EpisodeInput e) : CurrentWindow e :=
  ((ReferenceClasses.anchorOffsets (fun a => X.1.2 (i,a)),
    fun p => globalHorizontalCoordinate e (t X.1.1 i) X.1.1 (X.1.2 (i,p.1)+p.2)),
    fun p => episodeSplicedRow e t X i m p.1 p.2.1 p.2.2)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayClosed
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def typedCurrentArrayWindow {d : ℕ} (e : Direction d) (j : ℤ) (m : ℕ)
    (Y : ActualEpisodeArray e) : CurrentWindow e :=
  ((if h : ReferenceClasses.Consistent (currentOffsets e j Y) then
      ⟨currentOffsets e j Y,h⟩ else ReferenceClasses.anchorOffsets (fun _ => 0),
    (currentArrayWindow e j m Y).1.2),(currentArrayWindow e j m Y).2)

lemma typedCurrentArrayWindow_measurable {d : ℕ} (e : Direction d) (j : ℤ) (m : ℕ) :
    Measurable (typedCurrentArrayWindow e j m) := by
  have hs : MeasurableSet {Y : ActualEpisodeArray e | ReferenceClasses.Consistent (currentOffsets e j Y)} :=
    (ReferenceClasses.consistent_closed.preimage (currentOffsets_continuous e j)).measurableSet
  have ho : Measurable (fun Y : ActualEpisodeArray e =>
    if h : ReferenceClasses.Consistent (currentOffsets e j Y) then
      (⟨currentOffsets e j Y,h⟩ : ReferenceClasses.Data (HorizontalSpace e))
    else ReferenceClasses.anchorOffsets (fun _ => 0)) := by
    apply (MeasurableEmbedding.subtype_coe ReferenceClasses.consistent_closed.measurableSet).measurable_comp_iff.mp
    simp only [Function.comp_def,apply_dite]
    change Measurable (fun Y => if ReferenceClasses.Consistent (currentOffsets e j Y) then
      currentOffsets e j Y else (ReferenceClasses.anchorOffsets (fun _ : ℕ => (0 : HorizontalSpace e))).1)
    exact Measurable.ite hs (currentOffsets_continuous e j).measurable measurable_const
  exact (ho.prodMk ((currentArrayWindow_continuous e j m).measurable.fst.snd)).prodMk
    (currentArrayWindow_continuous e j m).measurable.snd

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_WindowEntropy
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def actualCurrentLaw {d : ℕ} (e : Direction d) (m : ℕ)
    (L : ProbabilityMeasure (ActualEpisodeArray e)) : ProbabilityMeasure (CurrentWindow e) :=
  L.map (f := (typedCurrentArrayWindow e 0 m)) (by first | (apply Measurable.aemeasurable; apply typedCurrentArrayWindow_measurable <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellSchedule
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def cellRadius {d : ℕ} (ν : Measure (Row d)) (e f : Direction d)
    (C : ℝ) (w m i : ℕ) : ℝ :=
  fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0) ((cellWidth w m i:ℝ)/C)

lemma cellRadius_pos {d : ℕ} (ν : Measure (Row d)) (e f : Direction d)
    (C : ℝ) (w m i : ℕ) : 0 < cellRadius ν e f C w m i := fluctuationRadius_pos _ _ _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IndependentDyadic
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience.ReferenceClasses
variable {H R : Type*} [AddCommGroup H]

variable [MeasurableSpace R]

variable [Countable H] [TopologicalSpace H] [DiscreteTopology H]
  [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)]

lemma reference_dust_dyadic (ν : Measure R) [IsProbabilityMeasure ν]
    (O : Data H) (dust : ℕ → Prop)
    (hd : ∀ a, dust a → ∀ b, related O a b → a=b)
    (q : UpperField H R → ℝ) (hq : Measurable q) (hb : ∀ ξ, |q ξ|≤1) :
    ∀ᵐ φ ∂reference ν O, Tendsto (fun r : ℕ => dustWeight dust q (2^r) φ-
      (∫ ξ, q ξ ∂Measure.infinitePi (fun _ : ℕ×H => ν))*dustFrequency dust (2^r)) atTop (𝓝 0) := by
  let P := Measure.infinitePi (fun _ : ℕ×H => ν)
  let M := Measure.infinitePi (fun _ : ℕ => P)
  let X : ℕ → (ℕ → UpperField H R) → ℝ := fun a ξ => if dust a then q (ξ a) else 0
  have hXm (a : ℕ) : Measurable (X a) := by
    dsimp only [X]
    split_ifs
    · exact hq.comp (measurable_pi_apply a)
    · exact measurable_const
  have hXb (a : ℕ) (ξ : ℕ → UpperField H R) : |X a ξ|≤1 := by
    dsimp only [X]
    split_ifs
    · exact hb _
    · norm_num
  have hind : iIndepFun X M := iIndepFun_infinitePi
    (X:=fun a ξ => if dust a then q ξ else 0) (fun a => by split_ifs; exact hq; exact measurable_const)
  have hmean (a : ℕ) : (∫ ξ, X a ξ ∂M)=(∫ ξ, q ξ ∂P)*(if dust a then 1 else 0) := by
    dsimp only [X]
    split_ifs with ha
    · rw [mul_one]
      have hm := measurePreserving_eval_infinitePi (fun _ : ℕ => P) a
      rw [←hm.map_eq,integral_map hm.measurable.aemeasurable hq.aestronglyMeasurable]
    · simp
  have hav (n : ℕ) : (∫ ξ, sampleAverage X n ξ ∂M)=(∫ ξ, q ξ ∂P)*dustFrequency dust n := by
    simp only [sampleAverage]
    rw [integral_const_mul,integral_finsetSum _ (fun a _ =>
      (integrable_const (1:ℝ)).mono' (hXm a).aestronglyMeasurable (Eventually.of_forall (hXb a)))]
    simp only [hmean,←Finset.mul_sum,dustFrequency]
    ring
  have hLL := independent_dyadic_centered M X hXm hXb hind
  simp only [hav] at hLL
  rw [reference_apply,←Measure.infinitePi_map_curry_symm (fun (_ : ℕ) (_ : ℕ×H) => ν)]
  rw [Measure.map_map (show Measurable (fields O : AllFields H R → _) from measurable_fields.comp measurable_prodMk_left) (MeasurableEquiv.curry ℕ (ℕ×H) R).symm.measurable]
  apply (ae_map_iff (((show Measurable (fields O : AllFields H R → _) from measurable_fields.comp measurable_prodMk_left).comp (MeasurableEquiv.curry ℕ (ℕ×H) R).symm.measurable).aemeasurable) (measurableSet_tendsto (𝓝 (0:ℝ)) (fun r =>
    (dustWeight_measurable dust q hq (2^r)).sub_const _))).mpr
  filter_upwards [hLL] with ξ hξ
  convert hξ using 1
  all_goals try with_reducible_and_instances rfl
  funext r
  congr 1
  unfold dustWeight sampleAverage
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [X]
  split_ifs with ha
  · congr 1
    funext p
    simp only [Function.comp_def,fields,inputSite,representative_singleton O a (hd a ha),
      displacement_singleton O a (hd a ha),zero_add]
    rfl
  · rfl

end DirectionalTransience.ReferenceClasses

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

noncomputable def upperNoDrop {d : ℕ} (e : Direction d) (ξ : UpperRows e) : ℝ≥0∞ :=
  noDropQuenched (realPosition (step e)) 0 (upperEnvironment e ξ)

lemma upperNoDrop_measurable {d : ℕ} (e : Direction d) : Measurable (upperNoDrop e) :=
  (measurable_noDropQuenched _ _).comp (upperEnvironment_continuous e).measurable

lemma upperNoDrop_le_one {d : ℕ} (e : Direction d) (ξ : UpperRows e) : upperNoDrop e ξ≤1 := prob_le_one

lemma upperNoDrop_restrict {d : ℕ} (e : Direction d) (ω : Environment d) :
    upperNoDrop e (upperField e 0 ω)=noDropQuenched (realPosition (step e)) 0 ω := by
  apply quenched_stay_congr {x | dot (realPosition (0:Lattice d)) (realPosition (step e))≤
      dot (realPosition x) (realPosition (step e))}
  intro x hx
  apply upperEnvironment_restrict_eq e ω x
  simpa only [realPosition,Int.cast_zero,Pi.zero_apply,dot,zero_mul,Finset.sum_const_zero] using (show dot (realPosition (0:Lattice d)) (realPosition (step e)) ≤ dot (realPosition x) (realPosition (step e)) from hx)

lemma upperNoDrop_le_kernel_ae {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∀ᵐ ξ ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν),
      ∀ H : ℕ, upperNoDrop e ξ ≤ upperHorizontalKernel e H ξ 0 Set.univ := by
  rw [←upperField_map e ν 0]
  apply (ae_map_iff ((upperField_measurable_rows e 0).mono (rowSigma_le _) le_rfl).aemeasurable
    (by
      simp only [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro H
      exact measurableSet_le (upperNoDrop_measurable e)
        (upperHorizontalKernel_lowerSemicontinuous e H 0 Set.univ).measurable)).mpr
  filter_upwards [crossingQuenched_tendsto_ae ν _ htrans] with ω hω H
  rw [upperNoDrop_restrict,upperKernel_restrict]
  apply le_of_tendsto (hω 0)
  filter_upwards [eventually_ge_atTop H] with n hn
  exact crossingQuenched_antitone _ _ _ (by exact_mod_cast hn)

lemma upperNoDrop_inverse_moment {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ lam : ℝ, 0<lam ∧ (∫⁻ ξ, upperNoDrop e ξ ^ (-lam) ∂Measure.infinitePi
      (fun _ : ℕ×HorizontalSpace e => ν))<⊤ := by
  obtain ⟨lam,hlam,hlamfin⟩ := noDrop_inverse_moment ν hue _ (signed_direction_unit e) htrans
  refine ⟨lam,hlam,?_⟩
  rw [←upperField_map e ν 0,lintegral_map ((upperNoDrop_measurable e).pow_const (-lam))
    ((upperField_measurable_rows e 0).mono (rowSigma_le _) le_rfl)]
  simpa only [upperNoDrop_restrict] using hlamfin

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_Dust
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def currentDustWeight {d : ℕ} (e : Direction d) (n : ℕ) (W : CurrentWindow e) : ℝ :=
  ReferenceClasses.dustWeight (currentDust e W.1) (fun ξ => (upperNoDrop e ξ).toReal) n W.2

lemma currentDustWeight_measurable {d : ℕ} (e : Direction d) (n : ℕ) :
    Measurable (currentDustWeight e n) := by
  unfold currentDustWeight ReferenceClasses.dustWeight sampleAverage
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro a _
  exact Measurable.ite ((currentDust_measurable e a).preimage measurable_fst)
    ((upperNoDrop_measurable e).ennreal_toReal.comp (Measurable.of_eval fun position =>
      (measurable_pi_apply (a,position)).comp measurable_snd)) measurable_const

noncomputable def upperNoDropMean {d : ℕ} (e : Direction d) (ν : Measure (Row d)) : ℝ :=
  ∫ ξ, (upperNoDrop e ξ).toReal ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)

lemma upperNoDrop_toReal_bound {d : ℕ} (e : Direction d) (ξ : UpperRows e) :
    |(upperNoDrop e ξ).toReal|≤1 := by
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono ENNReal.one_ne_top (upperNoDrop_le_one e ξ)).trans_eq ENNReal.toReal_one

lemma current_reference_dust_law {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (W : Measure (CurrentWindow e)) [IsProbabilityMeasure W]
    (hisolated : ∀ᵐ A ∂W.fst, ∀ a, currentDust e A a → ∀ b,
      ReferenceClasses.related A.1 a b → a=b)
    (hentropy : klDiv W (W.fst.compProd (currentWindowReference e ν))≠⊤) :
    ∀ᵐ w ∂W, Tendsto (fun r : ℕ => currentDustWeight e (2^r) w-
      upperNoDropMean e ν*currentDustFrequency e (2^r) w.1) atTop (𝓝 0) := by
  apply (klDiv_ne_top_iff.mp hentropy).1.ae_le
  apply (Measure.ae_compProd_iff (measurableSet_tendsto (𝓝 (0:ℝ)) (fun r =>
    (currentDustWeight_measurable e (2^r)).sub
      (((currentDustFrequency_measurable e (2^r)).comp measurable_fst).const_mul _)))).mpr
  filter_upwards [hisolated] with A hA
  exact ReferenceClasses.reference_dust_dyadic ν A.1 (currentDust e A) hA
    (fun ξ => (upperNoDrop e ξ).toReal) (upperNoDrop_measurable e).ennreal_toReal
      (upperNoDrop_toReal_bound e)

lemma reference_ae_fields {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (O : ReferenceClasses.Data (HorizontalSpace e)) (P : UpperRows e → Prop)
    (hP : MeasurableSet {ξ | P ξ})
    (hp : ∀ᵐ ξ ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν), P ξ) :
    ∀ᵐ φ ∂ ReferenceClasses.reference ν O, ∀ a : ℕ, P (fun p => φ (a,p)) := by
  apply ae_all_iff.mpr
  intro a
  rw [←ReferenceClasses.reference_single_field ν O a] at hp
  exact (ae_map_iff (Measurable.of_eval (fun position =>
    measurable_pi_apply (a,position))).aemeasurable hP).mp hp

lemma current_reference_nodrop_le {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (W : Measure (CurrentWindow e)) [IsProbabilityMeasure W]
    (hentropy : klDiv W (W.fst.compProd (currentWindowReference e ν))≠⊤) :
    ∀ᵐ w ∂W, ∀ a H : ℕ, upperNoDrop e (fun p => w.2 (a,p))≤
      upperHorizontalKernel e H (fun p => w.2 (a,p)) 0 Set.univ := by
  have hm : MeasurableSet {ξ : UpperRows e | ∀ H : ℕ,
      upperNoDrop e ξ≤upperHorizontalKernel e H ξ 0 Set.univ} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun H => measurableSet_le (upperNoDrop_measurable e)
      (upperHorizontalKernel_lowerSemicontinuous e H 0 Set.univ).measurable
  apply (klDiv_ne_top_iff.mp hentropy).1.ae_le
  apply (Measure.ae_compProd_iff (by
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun H => ?_
    have heval : Measurable (fun w : CurrentWindow e => fun p => w.2 (a,p)) :=
      Measurable.of_eval fun position => (measurable_pi_apply (a,position)).comp measurable_snd
    exact measurableSet_le ((upperNoDrop_measurable e).comp heval)
      ((upperHorizontalKernel_lowerSemicontinuous e H 0 Set.univ).measurable.comp heval))).mpr
  exact Eventually.of_forall fun A => reference_ae_fields e ν A.1 _ hm (upperNoDrop_le_kernel_ae e ν htrans)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ClassSelection
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma currentClassSelection_measurable {d : ℕ} (e : Direction d) (n : ℕ) (r : ℝ)
    (a : Fin n → ℕ) : MeasurableSet {A : CurrentData e | CurrentClassSelection e n r A a} := by
  unfold CurrentClassSelection
  change MeasurableSet ({A : CurrentData e | ∀ j, r≤(A.2 (a j,0):ℝ)} ∩
    {A : CurrentData e | ∀ j k, j≠k → ¬ReferenceClasses.related A.1 (a j) (a k)})
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le measurable_const
      (((measurable_pi_apply (a j,0)).comp measurable_snd).subtype_val)
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      ((ReferenceClasses.measurable_related (a j) (a k)).preimage measurable_fst).compl

noncomputable def currentSelect {d : ℕ} (e : Direction d) (n : ℕ) (r : ℝ) : CurrentData e → Fin n → ℕ :=
  Classical.choose (measurable_countable_selection (CurrentClassSelection e n r)
    (currentClassSelection_measurable e n r))

lemma currentSelect_measurable {d : ℕ} (e : Direction d) (n : ℕ) (r : ℝ) :
    Measurable (currentSelect e n r) :=
  (Classical.choose_spec (measurable_countable_selection (CurrentClassSelection e n r)
    (currentClassSelection_measurable e n r))).1

lemma currentSelect_spec {d : ℕ} (e : Direction d) (n : ℕ) (r : ℝ) (A : CurrentData e)
    (h : ∃ a, CurrentClassSelection e n r A a) : CurrentClassSelection e n r A (currentSelect e n r A) :=
  (Classical.choose_spec (measurable_countable_selection (CurrentClassSelection e n r)
    (currentClassSelection_measurable e n r))).2 A h

lemma current_selection_event_measurable {d : ℕ} (e : Direction d) (n : ℕ) (r : ℝ) :
    MeasurableSet {A : CurrentData e | ∃ a, CurrentClassSelection e n r A a} := by
  simpa only [Set.ofPred_exists] using MeasurableSet.iUnion (currentClassSelection_measurable e n r)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience.ReferenceClasses
variable {H R : Type*} [AddCommGroup H] [Countable H] [TopologicalSpace H]
  [DiscreteTopology H] [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)] [MeasurableSpace R]

lemma reference_distinct_product {n : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (O : Data H) (a : Fin n → ℕ)
    (ha : ∀ i j, i≠j → ¬related O (a i) (a j))
    (F : UpperField H R → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ φ, ∏ j : Fin n, F (fun p => φ (a j,p)) ∂reference ν O)=
      (∫⁻ ξ, F ξ ∂Measure.infinitePi (fun _ : ℕ×H => ν))^n := by
  let g : AllFields H R → (Fin n × (ℕ×H) → R) := fun φ p => φ (a p.1,p.2)
  have hg : Measurable g := by unfold g; fun_prop
  let P := Measure.infinitePi (fun _ : ℕ×H => ν)
  let M := Measure.infinitePi (fun _ : Fin n => P)
  have he := reference_distinct_classes ν O a ha
  change (reference ν O).map g = _ at he
  have hprod : Measurable (fun ξ : (Fin n × (ℕ×H) → R) => ∏ j : Fin n, F (fun p => ξ (j,p))) :=
    Finset.measurable_prod Finset.univ fun j _ => hF.comp
      (Measurable.of_eval fun position => measurable_pi_apply (j,position))
  rw [show (∫⁻ φ, ∏ j : Fin n, F (fun p => φ (a j,p)) ∂reference ν O)=
      ∫⁻ ξ, ∏ j : Fin n, F (fun p => ξ (j,p)) ∂(reference ν O).map g from
      (lintegral_map hprod hg).symm,he]
  rw [←Measure.infinitePi_map_curry_symm (fun (_ : Fin n) (_ : ℕ×H) => ν),
    lintegral_map hprod (MeasurableEquiv.curry (Fin n) (ℕ×H) R).symm.measurable]
  change (∫⁻ ξ, ∏ j : Fin n, F (ξ j) ∂M)=_
  have hind : iIndepFun (fun j (ξ : Fin n → UpperField H R) => F (ξ j)) M :=
    iIndepFun_infinitePi (X := fun (_ : Fin n) ξ => F ξ) (fun _ => hF)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun j (ξ : Fin n → UpperField H R) => F (ξ j)) hind
      (fun j => hF.comp (measurable_pi_apply j))]
  have hm (j : Fin n) : (∫⁻ ξ, F (ξ j) ∂M)=∫⁻ ξ, F ξ ∂P := by
    have hp := measurePreserving_eval_infinitePi (fun _ : Fin n => P) j
    rw [←lintegral_map hF hp.measurable,hp.map_eq]
  simp only [hm,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rfl

end DirectionalTransience.ReferenceClasses

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FiniteClasses
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma currentFiniteClasses_measurable {d : ℕ} (e : Direction d) :
    MeasurableSet {A : CurrentData e | CurrentFiniteClasses e A} := by
  have he : {A : CurrentData e | CurrentFiniteClasses e A} =
      {A | ∃ N : ℕ, ∀ a, ReferenceClasses.representative A.1 a≤N} := by
    ext A
    change CurrentFiniteClasses e A ↔ _
    rw [CurrentFiniteClasses,Set.finite_iff_bddAbove]
    constructor
    · rintro ⟨N,hN⟩
      exact ⟨N,fun a => hN (Set.mem_range_self a)⟩
    · rintro ⟨N,hN⟩
      exact ⟨N,by rintro _ ⟨a,rfl⟩; exact hN a⟩
  rw [he]
  simp only [Set.ofPred_exists,Set.ofPred_forall]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun a =>
    measurableSet_le ((ReferenceClasses.measurable_representative a).comp measurable_fst) measurable_const

lemma infinite_current_selection_eventually {d : ℕ} (e : Direction d) (A : CurrentData e)
    (hfin : ¬CurrentFiniteClasses e A) (hproper : ∀ a, 0<(A.2 (a,0):ℝ)) (n : ℕ) :
    ∀ᶠ (k : ℕ) in atTop, ∃ a, CurrentClassSelection e n (1/((k:ℝ)+1)) A a := by
  let S := Set.range (ReferenceClasses.representative A.1)
  have hS : S.Infinite := hfin
  let emb := hS.natEmbedding S
  let a : Fin n → ℕ := fun j => (emb j.val).val
  have ha (j : Fin n) : ReferenceClasses.representative A.1 (a j)=a j := by
    obtain ⟨b,hb⟩ := (emb j.val).property
    change ReferenceClasses.representative A.1 ((emb j.val).val)=(emb j.val).val
    rw [←hb]
    exact (ReferenceClasses.representative_eq_iff A.1 _ _).mpr (ReferenceClasses.representative_related A.1 b)
  have hsep (j k : Fin n) (hjk : j≠k) : ¬ReferenceClasses.related A.1 (a j) (a k) := by
    intro h
    have hh := (ReferenceClasses.representative_eq_iff A.1 _ _).mpr h
    rw [ha,ha] at hh
    have hjk' := emb.injective (Subtype.ext hh)
    exact hjk (Fin.ext hjk')
  have ht : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
    have hn : Tendsto (fun k : ℕ => (k:ℝ)+1) atTop atTop := (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    exact hn.const_div_atTop 1
  have hj (j : Fin n) : ∀ᶠ (k : ℕ) in atTop, 1/((k:ℝ)+1)≤(A.2 (a j,0):ℝ) :=
    ht.eventually (ge_mem_nhds (hproper (a j)))
  filter_upwards [eventually_all.mpr hj] with k hk
  exact ⟨a,hk,hsep⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ClassFinset
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped Classical
namespace DirectionalTransience

lemma currentClassFinset_mem {d : ℕ} (e : Direction d) (A : CurrentData e)
    (h : CurrentFiniteClasses e A) (a : ℕ) :
    a∈currentClassFinset e A ↔ ReferenceClasses.representative A.1 a=a := by
  rw [currentClassFinset,dite_eq_left h]
  change a∈(show (Set.range (ReferenceClasses.representative A.1)).Finite from h).toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨b,rfl⟩
    exact (ReferenceClasses.representative_eq_iff A.1 _ _).mpr (ReferenceClasses.representative_related A.1 b)
  · intro ha
    exact ⟨a,ha⟩

lemma currentClassFinset_measurable {d : ℕ} (e : Direction d) : Measurable (currentClassFinset e) := by
  rw [measurable_finset_iff]
  intro a
  apply measurableSet_setOfPred.mp
  have he : {A : CurrentData e | a∈currentClassFinset e A}=
      ({A | CurrentFiniteClasses e A} ∩ {A | ReferenceClasses.representative A.1 a=a}) ∪
      ({A | ¬CurrentFiniteClasses e A} ∩ {A | a=0}) := by
    ext A
    by_cases h : CurrentFiniteClasses e A
    · simp only [Set.mem_ofPred_eq,Set.mem_union,Set.mem_inter_iff,h,not_true_eq_false,false_and,
        or_false,true_and,currentClassFinset_mem e A h]
    · simp [currentClassFinset,h]
  rw [he]
  exact ((currentFiniteClasses_measurable e).inter
    (measurableSet_eq_fun ((ReferenceClasses.measurable_representative a).comp measurable_fst) measurable_const)).union
    ((currentFiniteClasses_measurable e).compl.inter (by by_cases h : a=0 <;> simp [h]))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ClassMoment
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def selectedClassProduct {d : ℕ} (e : Direction d) (n : ℕ) (r lam : ℝ)
    (w : CurrentWindow e) : ℝ≥0∞ :=
  if ∃ a, CurrentClassSelection e n r w.1 a then
    ∏ j : Fin n, upperNoDrop e (fun p => w.2 (currentSelect e n r w.1 j,p)) ^ (-lam)
  else 0

lemma selectedClassProduct_measurable {d : ℕ} (e : Direction d) (n : ℕ) (r lam : ℝ) :
    Measurable (selectedClassProduct e n r lam) := by
  unfold selectedClassProduct
  apply Measurable.ite ((current_selection_event_measurable e n r).preimage measurable_fst) _ measurable_const
  apply Finset.measurable_prod
  intro j _
  apply Measurable.pow_const
  apply (upperNoDrop_measurable e).comp
  apply Measurable.of_eval
  intro p
  have hm : Measurable (fun z : ReferenceClasses.AllFields (HorizontalSpace e) (Row d) × ℕ => z.1 (z.2,p)) :=
    measurable_from_prod_countable_left fun a => measurable_pi_apply (a,p)
  exact hm.comp (measurable_snd.prodMk (((currentSelect_measurable e n r).comp measurable_fst).eval))

lemma selectedClassProduct_lintegral {d : ℕ} (e : Direction d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (δ : Measure (CurrentData e)) [IsProbabilityMeasure δ]
    (n : ℕ) (r lam : ℝ) :
    (∫⁻ w, selectedClassProduct e n r lam w ∂δ.compProd (currentWindowReference e ν))≤
      (∫⁻ ξ, upperNoDrop e ξ ^ (-lam) ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν))^n := by
  rw [Measure.lintegral_compProd (selectedClassProduct_measurable e n r lam)]
  calc
    _ ≤ ∫⁻ _ : CurrentData e, (∫⁻ ξ, upperNoDrop e ξ ^ (-lam) ∂Measure.infinitePi
        (fun _ : ℕ×HorizontalSpace e => ν))^n ∂δ := by
      apply lintegral_mono
      intro A
      by_cases h : ∃ a, CurrentClassSelection e n r A a
      · simp only [selectedClassProduct,ite_eq_left h,currentWindowReference,Kernel.comap_apply]
        exact le_of_eq (ReferenceClasses.reference_distinct_product ν A.1 (currentSelect e n r A)
          (currentSelect_spec e n r A h).2 _ ((upperNoDrop_measurable e).pow_const (-lam)))
      · simp [selectedClassProduct,h]
    _ = _ := by simp

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeGlobalRetention
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def episodeStageCount {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (ω : Environment d) : ℕ :=
  episodeSteps e f hef r fexp g χ b sfloor N (episodeInitial (k:=k) e f hef r sfloor hR t ω) ω N

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMassSurvival
attribute [-instance] _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma arraySelfMass_mul_q_le_discount {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hP : ArrayProfilesConsistent e Y) (hc : ArrayContinuation e Y)
    (i : ℤ) (m a H : ℕ) (hH : arrayWindowHeight e i m Y=H)
    (hq : upperNoDrop e (arrayUpperRows e i m a Y)≤upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ) :
    arrayProfileMass e i (i,a) 0 Y * upperNoDrop e (arrayUpperRows e i m a Y)≤
      expNeg (arrayWindowCost e i m Y) := by
  apply le_trans (mul_le_mul_right hq _)
  exact (ENNReal.le_tsum 0).trans (arrayKernelImage_total_le_discount e Y hP hc i m a H hH)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def arrayCurrentData {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e) : CurrentData e :=
  (typedCurrentArrayWindow e i 0 Y).1
lemma arrayCurrentData_measurable {d : ℕ} (e : Direction d) (i : ℤ) : Measurable (arrayCurrentData e i) :=
  (typedCurrentArrayWindow_measurable e i 0).fst
lemma typedCurrentArrayWindow_data {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ) (Y : ActualEpisodeArray e) :
    (typedCurrentArrayWindow e i m Y).1=arrayCurrentData e i Y := rfl

lemma array_selectedProduct_lower {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hP : ArrayProfilesConsistent e Y) (hc : ArrayContinuation e Y) (i : ℤ) (m H n : ℕ)
    (hH : arrayWindowHeight e i m Y=H) (hfin : arrayWindowCost e i m Y≠⊤)
    (hq : ∀ a, upperNoDrop e (arrayUpperRows e i m a Y)≤
      upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ)
    {r lam t : ℝ} (hr : 0 < r) (hlam : 0≤lam) (ht : 2*t≤(arrayWindowCost e i m Y).toReal)
    (hrt : Real.exp (-t) ≤ r) (hs : ∃ a, CurrentClassSelection e n r (arrayCurrentData e i Y) a) :
    ENNReal.ofReal (Real.exp ((n:ℝ)*lam*t))≤ selectedClassProduct e n r lam (typedCurrentArrayWindow e i m Y) := by
  have hs' := hs
  rw [←typedCurrentArrayWindow_data e i m Y] at hs'
  simp only [selectedClassProduct,ite_eq_left hs']
  calc
    _ = ∏ _j : Fin n, ENNReal.ofReal (Real.exp (lam*t)) := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←ENNReal.ofReal_pow (Real.exp_nonneg _),
        ←Real.exp_nat_mul,mul_assoc]
    _ ≤ _ := by
      apply Finset.prod_le_prod'
      intro j _
      apply ennreal_negative_power_exp_lower hlam
      apply selfmass_nodrop_bound hr _ hfin ht hrt
        (arraySelfMass_mul_q_le_discount e Y hP hc i m _ H hH (hq _))
      exact ENNReal.ofReal_le_ofReal ((currentSelect_spec e n r _ hs').1 j)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_WindowWeak
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace Filter
open scoped ENNReal Classical Topology
namespace DirectionalTransience

instance currentDataProfiles_compact {d : ℕ} (e : Direction d) :
    CompactSpace (ReferenceClasses.Data (HorizontalSpace e) × CurrentProfiles e) := inferInstance
instance currentWindow_compact {d : ℕ} (e : Direction d) : CompactSpace (CurrentWindow e) := inferInstance

noncomputable def currentReferenceLaw {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (W : ProbabilityMeasure (CurrentWindow e)) :
    ProbabilityMeasure (CurrentWindow e) :=
  Entropy.compProdProb (W.map (f := Prod.fst) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (currentWindowReference e ν)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayDust
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma arrayDust_current_isolated {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ) (Y : ActualEpisodeArray e)
    (hO : ArrayOffsetsConsistent e Y) (hP : ArrayProfilesConsistent e Y)
    (hzero : ∀ p q z, p≠q → arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0) :
    ∀ a, currentDust e (typedCurrentArrayWindow e i m Y).1 a → ∀ b,
      ReferenceClasses.related (typedCurrentArrayWindow e i m Y).1.1 a b → a=b := by
  intro a ha b hr
  by_contra hab
  obtain ⟨z,hz⟩ := hr
  have ho : ReferenceClasses.Consistent (currentOffsets e i Y) := hO (fun a => (i,a))
  have hz' : Y.2.1 ((i,a),(i,b))=(z:OnePoint (HorizontalSpace e)) := by
    simpa only [typedCurrentArrayWindow,dite_eq_left ho,currentOffsets] using hz
  exact dust_isolated e Y hO hP hzero (i,a) (i,b) (by simpa using hab) ha z hz'

lemma array_dust_reference_facts {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (μ : Measure (ActualEpisodeArray e)) [IsProbabilityMeasure μ]
    (hconsistent : ∀ᵐ Y ∂μ, ArrayOffsetsConsistent e Y ∧ ArrayProfilesConsistent e Y)
    (hzero : ∀ᵐ Y ∂μ, ∀ p q z, p≠q → arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0)
    (hentropy : ∀ i m, let W:=μ.map (typedCurrentArrayWindow e i m)
      klDiv W (W.fst.compProd (currentWindowReference e ν))≠⊤) :
    ∀ᵐ Y ∂μ, ∀ (i : ℤ) (m : ℕ),
      Tendsto (fun r : ℕ => currentDustWeight e (2^r) (typedCurrentArrayWindow e i m Y)-
        upperNoDropMean e ν*arrayDustFrequency e i (2^r) Y) atTop (𝓝 0) ∧
      ∀ a H : ℕ, upperNoDrop e (arrayUpperRows e i m a Y)≤
        upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro m
  let F := typedCurrentArrayWindow e i m
  let W := μ.map F
  have hm : Measurable F := typedCurrentArrayWindow_measurable e i m
  have : IsProbabilityMeasure W := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have hi : ∀ᵐ A ∂W.fst, ∀ a, currentDust e A a → ∀ b, ReferenceClasses.related A.1 a b → a=b := by
    change ∀ᵐ A ∂(μ.map F).map Prod.fst, _
    rw [Measure.map_map measurable_fst hm]
    apply (ae_map_iff ((measurable_fst.comp hm).aemeasurable) _).mpr
    · filter_upwards [hconsistent,hzero] with Y hY hz
      exact arrayDust_current_isolated e i m Y hY.1 hY.2 hz
    · simp only [Set.ofPred_forall]
      refine MeasurableSet.iInter fun a => (currentDust_measurable e a).imp ?_
      simp only [Set.ofPred_forall]
      refine MeasurableSet.iInter fun b => ((ReferenceClasses.measurable_related a b).preimage measurable_fst).imp ?_
      by_cases hab : a=b <;> simp [hab]
  have hc := current_reference_dust_law e ν W hi (hentropy i m)
  have hq := current_reference_nodrop_le e ν htrans W (hentropy i m)
  have hv := ae_of_ae_map hm.aemeasurable (hc.and hq)
  exact hv

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryArrayLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

structure StationaryArrayLaw {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] (e : Direction d) where
  law : ProbabilityMeasure (ActualEpisodeArray e)
  preserving : MeasurePreserving StationaryCompact.shift (law : Measure (ActualEpisodeArray e)) (law : Measure (ActualEpisodeArray e))
  symmetric : ∀ σ, MeasurePreserving (arrayPerm e σ) (law : Measure (ActualEpisodeArray e)) (law : Measure (ActualEpisodeArray e))
  consistent : ∀ᵐ Y ∂(law : Measure (ActualEpisodeArray e)), ArrayOffsetsConsistent e Y ∧ ArrayProfilesConsistent e Y
  sampling : ∀ᵐ Y ∂(law : Measure (ActualEpisodeArray e)), ∀ p j z,
    Tendsto (fun n => arraySamplingError e p j z (2^n) Y) atTop (𝓝 0)
  zero_sampling : ∀ᵐ Y ∂(law : Measure (ActualEpisodeArray e)), ∀ p q z, p≠q →
    arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0
  finite_marks : ∀ᵐ Y ∂(law : Measure (ActualEpisodeArray e)), ∀ i,
    0<(Y.1 i).1 ∧ (Y.1 i).1<⊤ ∧ (Y.1 i).2.1<⊤ ∧ (Y.1 i).2.2<⊤
  integrable_cost : Integrable (arrayRealCost e) (law : Measure (ActualEpisodeArray e))
  positive_cost : 0<∫ Y, arrayRealCost e Y ∂(law : Measure (ActualEpisodeArray e))
  integrable_logheight : Integrable (fun Y => Real.log (1+((Y.1 0).1.toNat:ℝ))) (law : Measure (ActualEpisodeArray e))
  continuation : ∀ᵐ Y ∂(law : Measure (ActualEpisodeArray e)), ArrayContinuation e Y
  survival : ∀ᵐ Y ∂(law : Measure (ActualEpisodeArray e)), ArrayAveragedSurvival e Y
  κ : ℝ≥0
  κ_pos : 0<κ
  elliptic : ∀ᵐ Y ∂(law : Measure (ActualEpisodeArray e)), ArrayElliptic e κ Y
  entropyConstant : ℝ
  entropy : ∀ i m, let W:=(law : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e i m)
    klDiv W (W.fst.compProd (currentWindowReference e ν))≤ENNReal.ofReal ((m:ℝ)*entropyConstant)

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}
lemma entropy_finite (L : StationaryArrayLaw ν e) (i : ℤ) (m : ℕ) :
    let W:=(L.law : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e i m)
    klDiv W (W.fst.compProd (currentWindowReference e ν))≠⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (L.entropy i m)
end StationaryArrayLaw

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayClassProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience
namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma class_selection_probability (L : StationaryArrayLaw ν e)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e)))
    {lam : ℝ} (hlam : 0<lam) (hmean : (∫⁻ ξ, upperNoDrop e ξ ^ (-lam) ∂Measure.infinitePi
      (fun _ : ℕ×HorizontalSpace e => ν))<⊤) (n : ℕ) (hn : 0<n) (r : ℝ) (hr : 0 < r) :
    (L.law : Measure (ActualEpisodeArray e)).real
      (G.event ∩ {Y | ∃ a, CurrentClassSelection e n r (arrayCurrentData e 0 Y) a}) ≤
      max L.entropyConstant 0 / ((n:ℝ)*lam*G.ζ/2) := by
  let μ := (L.law : Measure (ActualEpisodeArray e))
  let a : ℝ := (n:ℝ)*lam*G.ζ/2
  have ha : 0<a := div_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hn) hlam) G.positive_ζ) (by norm_num)
  let M := (∫⁻ ξ, upperNoDrop e ξ ^ (-lam) ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν))^n
  have hM : M≠⊤ := ENNReal.pow_ne_top hmean.ne
  let B : ℕ → Set (ActualEpisodeArray e) := fun k => {Y |
    ENNReal.ofReal (Real.exp (a*(G.sequence k:ℝ)))≤ selectedClassProduct e n r lam
      (typedCurrentArrayWindow e 0 (G.sequence k) Y)}
  have hB (k : ℕ) : MeasurableSet (B k) := measurableSet_le measurable_const
    ((selectedClassProduct_measurable e n r lam).comp (typedCurrentArrayWindow_measurable e 0 _))
  have hbound (k : ℕ) : μ.real (B k)*(a*(G.sequence k:ℝ))≤
      max L.entropyConstant 0*(G.sequence k:ℝ)+M.toReal := by
    let F := typedCurrentArrayWindow e 0 (G.sequence k)
    let W := μ.map F
    have hmF : Measurable F := typedCurrentArrayWindow_measurable e 0 _
    have : IsProbabilityMeasure W :=
      (Measure.isProbabilityMeasure_map_iff hmF.aemeasurable).mpr inferInstance
    have he : klDiv W (W.fst.compProd (currentWindowReference e ν))≤
        ENNReal.ofReal (max L.entropyConstant 0*(G.sequence k:ℝ)) := by
      apply (L.entropy 0 (G.sequence k)).trans
      apply ENNReal.ofReal_le_ofReal
      nlinarith [le_max_left L.entropyConstant 0,show (0:ℝ)≤(G.sequence k:ℝ) from Nat.cast_nonneg _]
    have hh := Entropy.event_moment_budget W (W.fst.compProd (currentWindowReference e ν))
      (mul_nonneg (le_max_right _ _) (Nat.cast_nonneg _)) he _ (selectedClassProduct_measurable e n r lam) hM
      (selectedClassProduct_lintegral e ν W.fst n r lam) (a*(G.sequence k:ℝ))
    change ((μ.map F) {w | ENNReal.ofReal (Real.exp (a*(G.sequence k:ℝ)))≤ selectedClassProduct e n r lam w}).toReal * _ ≤ _ at hh
    rw [Measure.map_apply hmF (measurableSet_le measurable_const
      (selectedClassProduct_measurable e n r lam))] at hh
    exact hh
  apply event_rate μ _ (G.measurable_event.inter
    ((current_selection_event_measurable e n r).preimage (arrayCurrentData_measurable e 0))) B hB
      G.sequence G.strictMono.tendsto_atTop ha (le_max_right _ _) hbound
  have hq := array_dust_reference_facts e ν htrans μ L.consistent L.zero_sampling L.entropy_finite
  have hexp : ∀ᶠ k in atTop, Real.exp (-(G.ζ*(G.sequence k:ℝ)/2)) ≤ r := by
    have ht : Tendsto (fun k => G.ζ*(G.sequence k:ℝ)/2) atTop atTop := by
      have hh := (tendsto_natCast_atTop_atTop.comp G.strictMono.tendsto_atTop).const_mul_atTop G.positive_ζ
      exact Tendsto.atTop_div_const (by norm_num) hh
    exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).eventually (ge_mem_nhds hr)
  filter_upwards [L.consistent,L.continuation,L.finite_marks,hq,G.growth] with Y hP hc hf hq hg hY
  filter_upwards [hg hY.1,hexp] with k hk hkr
  have hHfin : arrayWindowHeight e 0 (G.sequence k) Y≠⊤ :=
    ENat.sum_ne_top.mpr fun j _ => (hf (0+j)).2.1.ne
  have hcfin : arrayWindowCost e 0 (G.sequence k) Y≠⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ => (hf (0+j)).2.2.2.ne
  have hh := array_selectedProduct_lower e Y hP.2 hc 0 (G.sequence k)
    (arrayWindowHeight e 0 (G.sequence k) Y).toNat n (ENat.natCast_toNat hHfin).symm hcfin
    (fun a => (hq 0 (G.sequence k)).2 a _) hr hlam.le (by linarith) hkr hY.2
  change ENNReal.ofReal (Real.exp (a*(G.sequence k:ℝ)))≤_
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  unfold a
  ring

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayFiniteClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience
namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma finite_current_classes (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) :
    ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event → CurrentFiniteClasses e (arrayCurrentData e 0 Y) := by
  let μ := (L.law : Measure (ActualEpisodeArray e))
  let A := G.event ∩ {Y | ¬CurrentFiniteClasses e (arrayCurrentData e 0 Y)}
  have hA : MeasurableSet A := G.measurable_event.inter
    (((currentFiniteClasses_measurable e).preimage (arrayCurrentData_measurable e 0)).compl)
  obtain ⟨lam,hlam,hmean⟩ := upperNoDrop_inverse_moment e ν hue htrans
  have hprob (n : ℕ) (hn : 0<n) : μ.real A≤ max L.entropyConstant 0 / ((n:ℝ)*lam*G.ζ/2) := by
    let B : ℕ → Set (ActualEpisodeArray e) := fun k => G.event ∩
      {Y | ∃ a, CurrentClassSelection e n (1/((k:ℝ)+1)) (arrayCurrentData e 0 Y) a}
    have hB (k : ℕ) : MeasurableSet (B k) := G.measurable_event.inter
      ((current_selection_event_measurable e n _).preimage (arrayCurrentData_measurable e 0))
    have he : ∀ᵐ Y ∂μ, Y∈A → ∀ᶠ k in atTop, Y∈B k := by
      filter_upwards [G.no_dust] with Y hY hy
      have hp (a : ℕ) : 0<((arrayCurrentData e 0 Y).2 (a,0):ℝ) := by
        have hn : ((arrayCurrentData e 0 Y).2 (a,0):ℝ)≠0 := hY hy.1 0 a
        exact lt_of_le_of_ne ((arrayCurrentData e 0 Y).2 (a,0)).property.1 hn.symm
      have hh := infinite_current_selection_eventually e (arrayCurrentData e 0 Y) hy.2 hp n
      filter_upwards [hh] with k hk
      exact ⟨hy.1,hk⟩
    have hb (k : ℕ) : μ (B k)≤ENNReal.ofReal (max L.entropyConstant 0 / ((n:ℝ)*lam*G.ζ/2)) := by
      rw [←ENNReal.ofReal_toReal (measure_ne_top μ (B k))]
      exact ENNReal.ofReal_le_ofReal (L.class_selection_probability htrans G hlam hmean n hn _ (by positivity))
    have hh := (measure_le_liminf_of_ae_eventually μ A hA B hB he).trans
      (liminf_le_liminf (Eventually.of_forall hb))
    rw [liminf_const] at hh
    exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (le_max_right _ _)
      (div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hlam.le) G.positive_ζ.le) (by norm_num))) hh
  have ht : Tendsto (fun n : ℕ => max L.entropyConstant 0 / ((n:ℝ)*lam*G.ζ/2)) atTop (𝓝 (0:ℝ)) := by
    have hi : Tendsto (fun n : ℕ => (n:ℝ)*lam*G.ζ/2) atTop atTop :=
      Tendsto.atTop_div_const (by norm_num) (((tendsto_natCast_atTop_atTop).atTop_mul_const hlam).atTop_mul_const G.positive_ζ)
    exact hi.const_div_atTop _
  have hz : μ.real A=0 := le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds ht
    ((eventually_gt_atTop 0).mono fun n hn => hprob n hn)) measureReal_nonneg
  have hmzero : μ A=0 := ((ENNReal.toReal_eq_zero_iff (μ A)).mp hz).resolve_right (measure_ne_top μ A)
  have hnot : ∀ᵐ Y ∂μ, Y∉A := ae_iff.mpr (by simpa using hmzero)
  exact hnot.mono (by intro Y hY hE; by_contra hf; exact hY ⟨hE,hf⟩)

lemma finite_classes_all_times (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) :
    ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event →
      ∀ i, CurrentFiniteClasses e (arrayCurrentData e i Y) := by
  have hh := stationary_ae_integer_family (L.law : Measure (ActualEpisodeArray e)) L.preserving
    (fun i Y => Y∈G.event → CurrentFiniteClasses e (arrayCurrentData e i Y))
    (fun i => G.measurable_event.imp ((currentFiniteClasses_measurable e).preimage
      (arrayCurrentData_measurable e i)))
    (fun i => G.invariant.mono fun Y hY => by rw [hY]; rfl)
    (L.finite_current_classes hue htrans G)
  filter_upwards [hh] with Y hY hy i
  exact hY i hy

end StationaryArrayLaw
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical BigOperators Topology
namespace DirectionalTransience

lemma arrayRelated_current {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) (i : ℤ) (a b : ℕ) :
    ReferenceClasses.related (arrayCurrentData e i Y).1 a b ↔ ArrayRelated e Y (i,a) (i,b) := by
  have ho : ReferenceClasses.Consistent (currentOffsets e i Y) := h (fun a => (i,a))
  simp only [arrayCurrentData,typedCurrentArrayWindow,dite_eq_left ho,ReferenceClasses.related,
    ArrayRelated,currentOffsets]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryMonotone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def arrayClassFinset {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e) : Finset ℕ :=
  currentClassFinset e (arrayCurrentData e i Y)
lemma arrayClassFinset_measurable {d : ℕ} (e : Direction d) (i : ℤ) : Measurable (arrayClassFinset e i) :=
  (currentClassFinset_measurable e).comp (arrayCurrentData_measurable e i)
lemma arrayClassFinset_shift {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e) :
    arrayClassFinset e i (StationaryCompact.shift Y)=arrayClassFinset e (i+1) Y := rfl

noncomputable def arrayTransport {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e) (a : ℕ) : ℕ :=
  ReferenceClasses.representative (arrayCurrentData e (i+1) Y).1 (arrayLink e i Y a)

lemma arrayTransport_measurable {d : ℕ} (e : Direction d) (i : ℤ) (a : ℕ) :
    Measurable (fun Y => arrayTransport e i Y a) := by
  exact (measurable_from_prod_countable_left (f := fun p : ActualEpisodeArray e × ℕ =>
    ReferenceClasses.representative (arrayCurrentData e (i+1) p.1).1 p.2)
      (fun b => (ReferenceClasses.measurable_representative b).comp
        (arrayCurrentData_measurable e (i+1)).fst)).comp
    (measurable_id.prodMk (arrayLink_measurable e i a))

lemma arrayTransport_related {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e)
    (ho : ArrayOffsetsConsistent e Y) (a : ℕ) (h : ∃ b, ArrayRelated e Y (i,a) (i+1,b)) :
    ArrayRelated e Y (i,a) (i+1,arrayTransport e i Y a) := by
  apply arrayRelated_trans e Y ho (arrayLink_related e i Y a h)
  apply (arrayRelated_current e Y ho (i+1) _ _).mp
  exact ReferenceClasses.related_symm (ReferenceClasses.representative_related _ _)

lemma arrayTransport_mem {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e)
    (hf : CurrentFiniteClasses e (arrayCurrentData e (i+1) Y)) (a : ℕ) :
    arrayTransport e i Y a∈arrayClassFinset e (i+1) Y :=
  currentClassFinset_rep_mem e _ hf _

lemma arrayTransport_injOn {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e)
    (ho : ArrayOffsetsConsistent e Y) (hf : CurrentFiniteClasses e (arrayCurrentData e i Y))
    (hs : ∀ a, ∃ b, ArrayRelated e Y (i,a) (i+1,b)) :
    Set.InjOn (arrayTransport e i Y) (arrayClassFinset e i Y) := by
  intro a ha b hb hab
  have ha' := arrayTransport_related e i Y ho a (hs a)
  rw [hab] at ha'
  have hr := arrayRelated_trans e Y ho ha'
    (arrayRelated_symm e Y ho (arrayTransport_related e i Y ho b (hs b)))
  have hh : ReferenceClasses.related (arrayCurrentData e i Y).1 a b :=
    (arrayRelated_current e Y ho i a b).mpr (by simpa only [hab] using hr)
  have he := (ReferenceClasses.representative_eq_iff _ a b).mpr hh
  rw [(currentClassFinset_mem e _ hf a).mp ha,(currentClassFinset_mem e _ hf b).mp hb] at he
  exact he

lemma arrayClassFinset_card_le {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e)
    (ho : ArrayOffsetsConsistent e Y) (hf : ∀ i, CurrentFiniteClasses e (arrayCurrentData e i Y))
    (hs : ∀ a, ∃ b, ArrayRelated e Y (i,a) (i+1,b)) :
    (arrayClassFinset e i Y).card≤(arrayClassFinset e (i+1) Y).card := by
  calc
    _ = ((arrayClassFinset e i Y).image (arrayTransport e i Y)).card :=
      (Finset.card_image_iff.mpr (arrayTransport_injOn e i Y ho (hf i) hs)).symm
    _ ≤ _ := Finset.card_le_card (by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
      exact arrayTransport_mem e i Y (hf (i+1)) a)

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma class_card_constant (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) :
    ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event → ∀ i,
      (arrayClassFinset e (i+1) Y).card=(arrayClassFinset e i Y).card := by
  let N := fun Y => if Y∈G.event then (arrayClassFinset e 0 Y).card else 0
  have hm : Measurable N := Measurable.ite G.measurable_event
    ((measurable_of_countable Finset.card).comp (arrayClassFinset_measurable e 0)) measurable_const
  have hf := L.finite_classes_all_times hue htrans G
  have hle : ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), N Y≤N (StationaryCompact.shift Y) := by
    filter_upwards [L.consistent,L.sampling,L.elliptic,L.continuation,L.finite_marks,G.no_dust,hf,G.invariant]
      with Y hO hs he hc hm hd hf hi
    by_cases hY : Y∈G.event
    · simp only [N,ite_eq_left hY,ite_eq_left (hi.mpr hY),arrayClassFinset_shift]
      exact arrayClassFinset_card_le e 0 Y hO.1 (hf hY)
        (array_forward_survives e Y hs L.κ L.κ_pos he hc (fun i => ⟨(hm i).1,(hm i).2.1⟩) (hd hY) 0)
    · simp only [N,ite_eq_right hY,ite_eq_right (mt hi.mp hY),le_refl]
  have heq := stationary_nat_monotone _ L.preserving N hm hle
  have h0 : ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event →
      (arrayClassFinset e (0+1) Y).card=(arrayClassFinset e 0 Y).card := by
    filter_upwards [heq,G.invariant] with Y hY hi hy
    simpa only [N,ite_eq_left hy,ite_eq_left (hi.mpr hy),arrayClassFinset_shift] using hY
  have hall := stationary_ae_integer_family _ L.preserving
    (fun i Y => Y∈G.event → (arrayClassFinset e (i+1) Y).card=(arrayClassFinset e i Y).card)
    (fun i => G.measurable_event.imp (measurableSet_eq_fun
      ((measurable_of_countable Finset.card).comp (arrayClassFinset_measurable e (i+1)))
      ((measurable_of_countable Finset.card).comp (arrayClassFinset_measurable e i))))
    (fun i => G.invariant.mono fun Y hi => by rw [hi]; rfl) h0
  filter_upwards [hall] with Y hY hy i
  exact hY i hy

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma arrayTransport_image {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e)
    (ho : ArrayOffsetsConsistent e Y) (hf : ∀ i, CurrentFiniteClasses e (arrayCurrentData e i Y))
    (hs : ∀ a, ∃ b, ArrayRelated e Y (i,a) (i+1,b))
    (hcard : (arrayClassFinset e (i+1) Y).card=(arrayClassFinset e i Y).card) :
    (arrayClassFinset e i Y).image (arrayTransport e i Y)=arrayClassFinset e (i+1) Y := by
  apply Finset.eq_of_subset_of_card_le
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    exact arrayTransport_mem e i Y (hf (i+1)) a
  · rw [Finset.card_image_iff.mpr (arrayTransport_injOn e i Y ho (hf i) hs),hcard]

lemma array_backward_survives {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e)
    (ho : ArrayOffsetsConsistent e Y) (hf : ∀ i, CurrentFiniteClasses e (arrayCurrentData e i Y))
    (hs : ∀ a, ∃ b, ArrayRelated e Y (i,a) (i+1,b))
    (hcard : (arrayClassFinset e (i+1) Y).card=(arrayClassFinset e i Y).card) (b : ℕ) :
    ∃ a, ArrayRelated e Y (i,a) (i+1,b) := by
  have hm : ReferenceClasses.representative (arrayCurrentData e (i+1) Y).1 b ∈
      arrayClassFinset e (i+1) Y := currentClassFinset_rep_mem e _ (hf (i+1)) b
  rw [←arrayTransport_image e i Y ho hf hs hcard] at hm
  obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp hm
  refine ⟨a,arrayRelated_trans e Y ho (arrayTransport_related e i Y ho a (hs a)) ?_⟩
  rw [heq]
  exact (arrayRelated_current e Y ho (i+1) _ _).mp (ReferenceClasses.representative_related _ b)

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma full_profiles (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) :
    ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event → ∀ i a z,
      0<(Y.2.2.1 (i,(i,a),z):ℝ) := by
  filter_upwards [L.consistent,L.sampling,L.elliptic,L.continuation,L.finite_marks,
    G.no_dust,L.finite_classes_all_times hue htrans G,L.class_card_constant hue htrans G]
    with Y hO hs he hc hm hd hf hcard hY i b z
  have hsurv (j : ℤ) := array_forward_survives e Y hs L.κ L.κ_pos he hc
    (fun j => ⟨(hm j).1,(hm j).2.1⟩) (hd hY) j
  obtain ⟨a,w,hw⟩ := array_backward_survives e (i-1) Y hO.1 (hf hY) (hsurv (i-1)) (hcard hY (i-1)) b
  have ha : 0<(Y.2.2.1 (i-1,(i-1,a),0):ℝ) :=
    lt_of_le_of_ne (Y.2.2.1 (i-1,(i-1,a),0)).property.1
      (show (Y.2.2.1 (i-1,(i-1,a),0):ℝ)≠0 from hd hY (i-1) a).symm
  have hp := array_next_full e Y L.κ L.κ_pos he hc
    (fun j => ⟨(hm j).1,(hm j).2.1⟩) (i-1) a ha (w+z)
  have hc' := hO.2.1 i (i-1,a) (i-1+1,b) w z hw
  simp only [sub_add_cancel] at hp hc'
  rwa [hc'] at hp

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

noncomputable def currentClassKernel {d : ℕ} (e : Direction d) : Kernel (CurrentData e) ℕ :=
  uniformFinsetKernel (currentClassFinset e) (currentClassFinset_measurable e) (currentClassFinset_nonempty e)
instance currentClassKernel_markov {d : ℕ} (e : Direction d) : IsMarkovKernel (currentClassKernel e) := by
  unfold currentClassKernel; infer_instance

noncomputable def arrayClassKernel {d : ℕ} (e : Direction d) (i : ℤ) : Kernel (ActualEpisodeArray e) ℕ :=
  (currentClassKernel e).comap (arrayCurrentData e i) (arrayCurrentData_measurable e i)
instance arrayClassKernel_markov {d : ℕ} (e : Direction d) (i : ℤ) : IsMarkovKernel (arrayClassKernel e i) := by
  unfold arrayClassKernel; infer_instance

noncomputable def markedShift {d : ℕ} (e : Direction d) (p : MarkedArray e) : MarkedArray e :=
  (StationaryCompact.shift p.1,arrayTransport e 0 p.1 p.2)

noncomputable def markedArrayLaw {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    (E : Set (ActualEpisodeArray e)) : Measure (MarkedArray e) := μ[|E].compProd (arrayClassKernel e 0)

lemma markedArrayLaw_probability {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    [IsProbabilityMeasure μ] (E : Set (ActualEpisodeArray e)) (hE : μ E≠0) :
    IsProbabilityMeasure (markedArrayLaw e μ E) := by
  have := cond_isProbabilityMeasure hE
  unfold markedArrayLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma markedArrayLaw_fst {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    [IsProbabilityMeasure μ] (E : Set (ActualEpisodeArray e)) :
    (markedArrayLaw e μ E).fst=μ[|E] := Measure.fst_compProd _ _

lemma markedArrayLaw_ae {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    [IsProbabilityMeasure μ] (E : Set (ActualEpisodeArray e)) (hE : MeasurableSet E)
    {P : ActualEpisodeArray e → Prop} (hP : ∀ᵐ Y ∂μ, Y∈E → P Y) :
    ∀ᵐ p ∂markedArrayLaw e μ E, P p.1 := by
  have h : ∀ᵐ Y ∂μ[|E], P Y := by
    filter_upwards [(show μ[|E]≪μ from cond_absolutelyContinuous).ae_le hP,ae_cond_mem hE] with Y hY hy
    exact hY hy
  have hp : MeasurePreserving Prod.fst (markedArrayLaw e μ E) μ[|E] :=
    ⟨measurable_fst,markedArrayLaw_fst e μ E⟩
  exact hp.quasiMeasurePreserving.ae h

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma marked_preserving (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) :
    MeasurePreserving (markedShift e) (markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event)
      (markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event) := by
  apply preserving_marking _ (preserving_cond _ L.preserving G.event G.measurable_event G.invariant)
    (arrayClassKernel e 0) (fun p => arrayTransport e 0 p.1 p.2)
    (measurable_from_prod_countable_left (arrayTransport_measurable e 0))
  have h : ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event →
      ((arrayClassKernel e 0) Y).map (arrayTransport e 0 Y)=
        (arrayClassKernel e 0) (StationaryCompact.shift Y) := by
    filter_upwards [L.consistent,L.sampling,L.elliptic,L.continuation,L.finite_marks,
      G.no_dust,L.finite_classes_all_times hue htrans G,L.class_card_constant hue htrans G]
      with Y hO hs he hc hm hd hf hcard hY
    have hsurv := array_forward_survives e Y hs L.κ L.κ_pos he hc
      (fun j => ⟨(hm j).1,(hm j).2.1⟩) (hd hY) 0
    exact uniformFinset_map (arrayClassFinset e 0 Y) (arrayClassFinset e 1 Y)
      (currentClassFinset_nonempty e _) (currentClassFinset_nonempty e _)
      (arrayTransport e 0 Y) (arrayTransport_injOn e 0 Y hO.1 (hf hY 0) hsurv)
      (by
        apply Finset.coe_injective
        simpa only [Finset.coe_image, zero_add] using congrArg (fun s : Finset ℕ => (s : Set ℕ))
          (arrayTransport_image e 0 Y hO.1 (hf hY) hsurv (hcard hY 0)))
  filter_upwards [(show (L.law : Measure (ActualEpisodeArray e))[|G.event]≪(L.law : Measure (ActualEpisodeArray e)) from cond_absolutelyContinuous).ae_le h,ae_cond_mem G.measurable_event] with Y hY hy
  exact hY hy

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMarkedEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

noncomputable def markedData {d : ℕ} (e : Direction d) (p : MarkedArray e) : MarkedCurrentData e :=
  (arrayCurrentData e 0 p.1,p.2)
lemma markedData_measurable {d : ℕ} (e : Direction d) : Measurable (markedData e) :=
  ((arrayCurrentData_measurable e 0).comp measurable_fst).prodMk measurable_snd

noncomputable def markedUpper {d : ℕ} (e : Direction d) (n : ℕ) (p : MarkedArray e) : UpperRows e :=
  arrayUpperRows e 0 n p.2 p.1
lemma markedUpper_measurable {d : ℕ} (e : Direction d) (n : ℕ) : Measurable (markedUpper e n) :=
  measurable_from_prod_countable_left (fun a => (arrayUpperRows_continuous e 0 n a).measurable)

lemma marked_window_law {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    [IsProbabilityMeasure μ] (E : Set (ActualEpisodeArray e)) (n : ℕ) :
    (markedArrayLaw e μ E).map (fun p => (markedData e p,markedUpper e n p)) =
      StoppedWindow.selectedKernel (currentClassKernel e) (selectUpperField e) (selectUpperField_measurable e) ∘ₘ
        (μ[|E].map (typedCurrentArrayWindow e 0 n)) := by
  have hf := (typedCurrentArrayWindow_measurable e 0 n).snd
  have hp : Measurable (fun p : (CurrentData e × ℕ) × ReferenceClasses.AllFields (HorizontalSpace e) (Row d) =>
      (p.1,selectUpperField e (p.1.2,p.2))) :=
    measurable_fst.prodMk ((selectUpperField_measurable e).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have h := congrArg (fun M => M.map (fun p : (CurrentData e × ℕ) × ReferenceClasses.AllFields (HorizontalSpace e) (Row d) =>
      (p.1,selectUpperField e (p.1.2,p.2))))
    (StoppedWindow.sample_data_map μ[|E] (arrayCurrentData e 0) (arrayCurrentData_measurable e 0)
      (fun Y => (typedCurrentArrayWindow e 0 n Y).2) hf (currentClassKernel e))
  have hw : Measurable (fun p : ActualEpisodeArray e × ℕ =>
      ((arrayCurrentData e 0 p.1,p.2),(typedCurrentArrayWindow e 0 n p.1).2)) :=
    (((arrayCurrentData_measurable e 0).comp measurable_fst).prodMk measurable_snd).prodMk
      (hf.comp measurable_fst)
  rw [Measure.map_map hp hw,Measure.map_comp _ _ hp] at h
  exact h

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma marked_upper_entropy (L : StationaryArrayLaw ν e)
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) (n : ℕ) :
    let μ := markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event
    let W := μ.map (fun p => (markedData e p,markedUpper e n p))
    klDiv W (W.fst.prod (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)))≠∞ := by
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let μ := (L.law : Measure (ActualEpisodeArray e))
  have : IsProbabilityMeasure μ[|G.event] := cond_isProbabilityMeasure G.positive_event.ne'
  let W := μ.map (typedCurrentArrayWindow e 0 n)
  let Q := μ[|G.event].map (typedCurrentArrayWindow e 0 n)
  have : IsProbabilityMeasure W := by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply typedCurrentArrayWindow_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure Q := by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply typedCurrentArrayWindow_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hdom : Q≤ENNReal.ofReal ((μ G.event)⁻¹).toReal • W := by
    rw [ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr G.positive_event.ne')]
    have h : μ[|G.event]≤(μ G.event)⁻¹ • μ := smul_le_smul_left _ Measure.restrict_le_self
    simpa only [Measure.map_smul] using
      Measure.map_mono h (typedCurrentArrayWindow_measurable e 0 n)
  have hk := Entropy.finite_kl_of_domination Q W (W.fst.compProd (currentWindowReference e ν))
    (L.entropy_finite 0 n) _ ENNReal.toReal_nonneg hdom
  have h := StoppedWindow.selected_kl_finite Q W.fst (currentWindowReference e ν) (currentClassKernel e)
    (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)) (selectUpperField e)
    (selectUpperField_measurable e) (fun A a => ReferenceClasses.reference_single_field ν A.1 a) hk
  rw [←marked_window_law e μ G.event n] at h
  exact h

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_ProfileGrowth2
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

instance instCountableHorizontalLayer {d : ℕ} (e : Direction d) : Countable (HorizontalLayer e) := inferInstanceAs (Countable {x : Lattice d // x e.1 = 0})
instance instMeasurableSpaceHorizontalLayer {d : ℕ} (e : Direction d) : MeasurableSpace (HorizontalLayer e) := inferInstanceAs (MeasurableSpace {x : Lattice d // x e.1 = 0})
instance instMeasurableSingletonClassHorizontalLayer {d : ℕ} (e : Direction d) : MeasurableSingletonClass (HorizontalLayer e) := inferInstanceAs (MeasurableSingletonClass {x : Lattice d // x e.1 = 0})

noncomputable def horizontalCoordinateKernel {d : ℕ} (e : Direction d) (f : Fin d)
    (H : ℕ) (ω : Environment d) : Kernel (HorizontalLayer e) ℤ :=
  ((variableHitKernel (realPosition (step e)) H).comap
    (fun x : HorizontalLayer e => (ω,x.1)) (measurable_of_countable _)).map (fun x => x f)

lemma horizontalCoordinateKernel_apply {d : ℕ} (e : Direction d) (f : Fin d)
    (H : ℕ) (ω : Environment d) (x : HorizontalLayer e) :
    horizontalCoordinateKernel e f H ω x =
      (hitKernel (Strip (realPosition (step e)) x.1 H)
        (Upper (realPosition (step e)) x.1 H) (ω,x.1)).map (fun y => y f) := by
  rw [horizontalCoordinateKernel, Kernel.map_apply _ (measurable_of_countable _), Kernel.comap_apply]
  rfl

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProperProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def horizontalLayerEquiv {d : ℕ} (e : Direction d) : HorizontalSpace e ≃ HorizontalLayer e where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma isProperProfile_measurable {d : ℕ} (e : Direction d) :
    MeasurableSet {w | IsProperProfile e w} := by
  simp only [IsProperProfile,Set.ofPred_and,Set.ofPred_forall]
  exact (MeasurableSet.iInter fun z => measurableSet_lt measurable_const (measurable_pi_apply z)).inter
    (measurableSet_le (Measurable.tsum fun z => measurable_pi_apply z) measurable_const)

noncomputable def properProfileKernel {d : ℕ} (e : Direction d) : Kernel (ProperProfile e) (HorizontalLayer e) :=
  Kernel.mk (fun w => Measure.sum (fun z : HorizontalSpace e => w.1 z • Measure.dirac (horizontalLayerEquiv e z))) (by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.sum_apply _ hs,Measure.smul_apply,smul_eq_mul]
    exact Measurable.tsum fun z => ((measurable_pi_apply z).comp measurable_subtype_coe).mul_const _)

lemma properProfileKernel_apply {d : ℕ} (e : Direction d) (w : ProperProfile e) (z : HorizontalSpace e) :
    properProfileKernel e w {horizontalLayerEquiv e z}=w.1 z := by
  change (Measure.sum (fun y : HorizontalSpace e => w.1 y • Measure.dirac (horizontalLayerEquiv e y))) {horizontalLayerEquiv e z}=_
  rw [Measure.sum_apply _ (measurableSet_singleton _)]
  simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ (measurableSet_singleton _)]
  rw [tsum_eq_single z]
  · simp
  · intro y hy
    simp [hy,(horizontalLayerEquiv e).injective.eq_iff]

lemma properProfileKernel_total {d : ℕ} (e : Direction d) (w : ProperProfile e) :
    properProfileKernel e w Set.univ≤1 := by
  change (Measure.sum (fun z : HorizontalSpace e => w.1 z • Measure.dirac (horizontalLayerEquiv e z))) Set.univ≤1
  simpa only [Measure.sum_apply _ MeasurableSet.univ,Measure.smul_apply,smul_eq_mul,Measure.dirac_apply_of_mem (Set.mem_univ _),mul_one] using w.2.2

lemma properProfileKernel_full {d : ℕ} (e : Direction d) (w : ProperProfile e) (z : HorizontalLayer e) :
    0<(properProfileKernel e w).real {z} := by
  change 0<(properProfileKernel e w {z}).toReal
  rw [←(horizontalLayerEquiv e).apply_symm_apply z,properProfileKernel_apply]
  exact ENNReal.toReal_pos (w.2.1 _).ne' (ne_top_of_le_ne_top ENNReal.one_ne_top ((ENNReal.le_tsum _).trans w.2.2))

noncomputable def markedProfile {d : ℕ} (e : Direction d) (p : MarkedCurrentData e) : HorizontalSpace e → ℝ≥0∞ :=
  fun z => ENNReal.ofReal (p.1.2 (p.2,z):ℝ)

lemma markedProfile_measurable {d : ℕ} (e : Direction d) : Measurable (markedProfile e) := by
  apply Measurable.of_eval
  intro z
  exact Measurable.ennreal_ofReal ((measurable_from_prod_countable_left fun a =>
    ((measurable_pi_apply (a,z)).comp measurable_snd).subtype_val))

noncomputable def properData {d : ℕ} (e : Direction d) (w₀ : ProperProfile e) (p : MarkedCurrentData e) : ProperProfile e :=
  if h : IsProperProfile e (markedProfile e p) then ⟨markedProfile e p,h⟩ else w₀

lemma properData_measurable {d : ℕ} (e : Direction d) (w₀ : ProperProfile e) : Measurable (properData e w₀) := by
  apply Measurable.subtype_mk
  have he : (fun p => (properData e w₀ p).val)=(fun p => if IsProperProfile e (markedProfile e p) then markedProfile e p else w₀.1) := by
    funext p
    by_cases hp : IsProperProfile e (markedProfile e p) <;> simp [properData,hp]
  change Measurable (fun p => (properData e w₀ p).val)
  rw [he]
  exact Measurable.ite ((isProperProfile_measurable e).preimage (markedProfile_measurable e))
    (markedProfile_measurable e) measurable_const

lemma properData_eq {d : ℕ} (e : Direction d) (w₀ : ProperProfile e) (p : MarkedCurrentData e)
    (hp : IsProperProfile e (markedProfile e p)) : (properData e w₀ p).1=markedProfile e p := by
  simp only [properData,dite_eq_left hp]

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma marked_profile_proper (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) :
    ∀ᵐ p ∂markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event,
      IsProperProfile e (markedProfile e (markedData e p)) := by
  have h := markedArrayLaw_ae e (L.law : Measure (ActualEpisodeArray e)) G.event G.measurable_event
    (show ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event →
      ArrayProfilesConsistent e Y ∧ ∀ i a z, 0<(Y.2.2.1 (i,(i,a),z):ℝ) from by
        filter_upwards [L.consistent,L.full_profiles hue htrans G] with Y hO hF hY
        exact ⟨hO.2,hF hY⟩)
  filter_upwards [h] with p hp
  exact ⟨fun z => ENNReal.ofReal_pos.mpr (hp.2 0 p.2 z),arrayProfileMass_total_le_one e p.1 hp.1 0 (0,p.2)⟩

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProfileMeasureUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators
namespace DirectionalTransience

lemma properProfileKernel_eq_map {d : ℕ} (e : Direction d) (w : ProperProfile e) :
    properProfileKernel e w=(Measure.sum (fun z => w.1 z • Measure.dirac z)).map (horizontalLayerEquiv e) := by
  rw [Measure.map_sum (measurable_of_countable _).aemeasurable]
  simp only [Measure.map_smul,
    Measure.map_dirac' (measurable_of_countable _)]
  rfl

lemma properData_kernel_eq {d : ℕ} (e : Direction d) (w₀ : ProperProfile e) (p : MarkedArray e)
    (hp : IsProperProfile e (markedProfile e (markedData e p))) :
    properProfileKernel e (properData e w₀ (markedData e p))=
      (arrayProfileMeasure e 0 (0,p.2) p.1).map (horizontalLayerEquiv e) := by
  rw [properProfileKernel_eq_map,properData_eq _ _ _ hp]
  rfl

lemma horizontalKernel_fill {d : ℕ} (e : Direction d) (f : Fin d) (hef : e.1≠f)
    (H : ℕ) (ξ : UpperRows e) (ω : Environment d) (z : HorizontalSpace e) :
    horizontalCoordinateKernel e f H (fillUpper e (ξ,ω)) (horizontalLayerEquiv e z)=
      (upperHorizontalKernel e H ξ z).map (fun x => x.1 f) := by
  rw [horizontalCoordinateKernel_apply]
  change (hitKernel (Strip _ z.val H) (Upper _ z.val H) (fillUpper e (ξ,ω),z.val)).map _=
    ((variableHitKernel _ H (upperEnvironment e ξ,horizontalLift e 0 z)).map (horizontalProjection e)).map _
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have hz : horizontalLift e 0 z=z.val := by simp [horizontalLift]
  rw [hz]
  have hk : hitKernel (Strip (realPosition (step e)) z.val H) (Upper (realPosition (step e)) z.val H)
      (fillUpper e (ξ,ω),z.val)=
      hitKernel (Strip (realPosition (step e)) z.val H) (Upper (realPosition (step e)) z.val H)
      (upperEnvironment e ξ,z.val) := by
    apply hitKernel_congr
    intro x hx
    apply fillUpper_eq
    have h0 : dot (realPosition z.val) (realPosition (step e))=0 := by
      rw [signedHeight_projection]
      have hz0 : z.val e.1=0 := z.property
      simp [signedHeight,hz0]
    have hh := hx.1
    rw [h0,signedHeight_projection] at hh
    exact_mod_cast hh
  rw [hk]
  apply congrArg (fun k => Measure.map k (hitKernel (Strip (realPosition (step e)) z.val H)
    (Upper (realPosition (step e)) z.val H) (upperEnvironment e ξ,z.val)))
  funext x
  simp [Function.comp_apply,horizontalProjection,Ne.symm hef]

lemma horizontalProfileImage_fill {d : ℕ} (e : Direction d) (f : Fin d) (hef : e.1≠f)
    (H : ℕ) (ξ : UpperRows e) (ω : Environment d) (μ : Measure (HorizontalSpace e)) :
    horizontalCoordinateKernel e f H (fillUpper e (ξ,ω)) ∘ₘ μ.map (horizontalLayerEquiv e)=
      (upperHorizontalKernel e H ξ ∘ₘ μ).map (fun x => x.1 f) := by
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),
    lintegral_map ((horizontalCoordinateKernel e f H (fillUpper e (ξ,ω))).measurable_coe hA)
      (measurable_of_countable _),Measure.map_apply (measurable_of_countable _) hA,
    Measure.bind_apply ((measurable_of_countable _) hA) (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro z
  rw [horizontalKernel_fill e f hef,Measure.map_apply (measurable_of_countable _) hA]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMarkedIterate
attribute [-instance] _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma markedShift_iterate_fst {d : ℕ} (e : Direction d) (p : MarkedArray e) (n : ℕ) :
    ((markedShift e)^[n] p).1=StationaryCompact.shift^[n] p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    change StationaryCompact.shift ((markedShift e)^[n] p).1=_
    rw [ih]

lemma marked_related_iterate {d : ℕ} (e : Direction d) (p : MarkedArray e)
    (ho : ArrayOffsetsConsistent e p.1)
    (hs : ∀ n, ArrayRelated e ((markedShift e)^[n] p).1 (0,((markedShift e)^[n] p).2)
      (1,((markedShift e)^[n+1] p).2)) (n : ℕ) :
    ArrayRelated e p.1 (0,p.2) (n,((markedShift e)^[n] p).2) := by
  induction n with
  | zero => exact arrayRelated_refl e p.1 ho _
  | succ n ih =>
    apply arrayRelated_trans e p.1 ho ih
    obtain ⟨z,hz⟩ := hs n
    rw [markedShift_iterate_fst,arrayOffset_iterate] at hz
    refine ⟨z,?_⟩
    simpa only [zero_add,add_zero,Nat.cast_add,Nat.cast_one,add_comm] using hz

noncomputable def markedDisplacement {d : ℕ} (e : Direction d) (n : ℕ) (p : MarkedArray e) : HorizontalSpace e :=
  if h : ArrayRelated e p.1 (0,p.2) (n,((markedShift e)^[n] p).2) then Classical.choose h else 0

lemma markedDisplacement_spec {d : ℕ} (e : Direction d) (n : ℕ) (p : MarkedArray e)
    (h : ArrayRelated e p.1 (0,p.2) (n,((markedShift e)^[n] p).2)) :
    p.1.2.1 ((0,p.2),(n,((markedShift e)^[n] p).2))=(markedDisplacement e n p : OnePoint (HorizontalSpace e)) := by
  rw [markedDisplacement,dite_eq_left h]
  exact Classical.choose_spec h

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma marked_related (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) :
    ∀ᵐ p ∂markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event,
      ∀ n : ℕ, ArrayRelated e p.1 (0,p.2) (n,((markedShift e)^[n] p).2) := by
  have h0 := markedArrayLaw_ae e (L.law : Measure (ActualEpisodeArray e)) G.event G.measurable_event
    (show ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event →
      ArrayOffsetsConsistent e Y ∧ ∀ a, ArrayRelated e Y (0,a) (1,arrayTransport e 0 Y a) from by
      filter_upwards [L.consistent,L.sampling,L.elliptic,L.continuation,L.finite_marks,G.no_dust]
        with Y hO hs he hc hm hd hY
      refine ⟨hO.1,fun a => arrayTransport_related e 0 Y hO.1 a ?_⟩
      exact array_forward_survives e Y hs L.κ L.κ_pos he hc
        (fun i => ⟨(hm i).1,(hm i).2.1⟩) (hd hY) 0 a)
  have hall := ae_all_iff.mpr fun n =>
    ((L.marked_preserving hue htrans G).iterate n).quasiMeasurePreserving.ae h0
  filter_upwards [h0,hall] with p hp hh n
  apply marked_related_iterate e p hp.1 _ n
  intro k
  simpa only [Function.iterate_succ_apply',markedShift] using (hh k).2 ((markedShift e)^[k] p).2

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryProfile
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

noncomputable def coordinateProfile {d : ℕ} (e : Direction d) (f : Fin d)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) : Kernel D ℤ :=
  w.map (fun x => x.1 f)

instance coordinateProfile_finite {d : ℕ} (e : Direction d) (f : Fin d)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w] :
    IsFiniteKernel (coordinateProfile e f w) := by
  unfold coordinateProfile
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma coordinateProfile_apply {d : ℕ} (e : Direction d) (f : Fin d)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) (z : D) :
    coordinateProfile e f w z = (w z).map (fun x => x.1 f) :=
  Kernel.map_apply _ (measurable_of_countable _) _

structure StationaryProfileSystem {d : ℕ} (ν : Measure (Row d))
    (e : Direction d) (f : Fin d)
    (Ω D : Type) [MeasurableSpace Ω] [MeasurableSpace D]
    (μ : Measure Ω) (w : Kernel D (HorizontalLayer e)) where
  T : Ω → Ω
  preserving : MeasurePreserving T μ μ
  data : Ω → D
  measurable_data : Measurable data
  full : ∀ z x, 0 < (w z).real {x}
  total : ∀ z, w z Set.univ ≤ 1
  c : Ω → ℝ
  measurable_c : Measurable c
  nonneg_c : ∀ᵐ ω ∂μ, 0 ≤ c ω
  integrable_c : Integrable c μ
  h : Ω → ℕ
  measurable_h : Measurable h
  positive_h : ∀ᵐ ω ∂μ, 1 ≤ h ω
  integrable_log_h : Integrable (fun ω => Real.log (1+(h ω:ℝ))) μ
  field : ℕ → Ω → Environment d
  measurable_field : ∀ n, Measurable (field n)
  finite_entropy : ∀ n : ℕ, 0 < n →
    ∃ g : D × Environment d → ℝ,
      Measurable g ∧ (∀ z, 0 ≤ g z) ∧
      Integrable g ((μ.map data).prod (environmentLaw ν)) ∧
      (∫ z, g z ∂(μ.map data).prod (environmentLaw ν)) = 1 ∧
      Integrable (fun z => TailDecorrelation.entropyPlus (g z))
        ((μ.map data).prod (environmentLaw ν)) ∧
      μ.map (fun ω => (data ω,field n ω)) =
        ((μ.map data).prod (environmentLaw ν)).withDensity (fun z => ENNReal.ofReal (g z))
  offset : ℕ → Ω → ℤ
  update : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂μ,
    ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, c (T^[i] ω))) •
      (horizontalCoordinateKernel e f (∑ i ∈ Finset.range n, h (T^[i] ω)) (field n ω) ∘ₘ
        w (data ω)) ≤
      (coordinateProfile e f w (data (T^[n] ω))).map (fun x => x+offset n ω)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_MarkedObservables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma markedArrayLaw_integrable {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    [IsProbabilityMeasure μ] (E : Set (ActualEpisodeArray e)) (hE : μ E≠0)
    (F : ActualEpisodeArray e → ℝ) (hF : Measurable F) (hFi : Integrable F μ) :
    Integrable (fun p : MarkedArray e => F p.1) (markedArrayLaw e μ E) := by
  have hi : Integrable F μ[|E] := hFi.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr hE)
  apply (integrable_map_measure hF.aestronglyMeasurable measurable_fst.aemeasurable).mp
  change Integrable F (markedArrayLaw e μ E).fst
  rwa [markedArrayLaw_fst]

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma marked_proper_entropy (L : StationaryArrayLaw ν e)
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e)))
    (w₀ : ProperProfile e) (n : ℕ) :
    let μ := markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event
    let data := fun p => properData e w₀ (markedData e p)
    klDiv (μ.map (fun p => (data p,markedUpper e n p)))
      ((μ.map data).prod (Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)))≠∞ := by
  let μ := markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event
  have := markedArrayLaw_probability e (L.law : Measure (ActualEpisodeArray e)) G.event G.positive_event.ne'
  let U := Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)
  have hk := L.marked_upper_entropy G n
  dsimp only at hk ⊢
  rw [Measure.fst_map_prodMk (markedUpper_measurable e n)] at hk
  have h := klDiv_map_le (μ.map (fun p => (markedData e p,markedUpper e n p)))
    ((μ.map (markedData e)).prod U) ((properData_measurable e w₀).prodMap measurable_id)
  have hprod := Measure.map_prod_map (μ.map (markedData e)) U (properData_measurable e w₀) measurable_id
  rw [Measure.map_id] at hprod
  rw [←hprod,Measure.map_map (properData_measurable e w₀) (markedData_measurable e),
    Measure.map_map ((properData_measurable e w₀).prodMap measurable_id)
      ((markedData_measurable e).prodMk (markedUpper_measurable e n))] at h
  exact ne_top_of_le_ne_top hk h

lemma marked_full_entropy (L : StationaryArrayLaw ν e)
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e)))
    (w₀ : ProperProfile e) (n : ℕ) :
    let μ := markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event
    let data := fun p : MarkedArray e × Environment d => properData e w₀ (markedData e p.1)
    let field := fun p : MarkedArray e × Environment d => fillUpper e (markedUpper e n p.1,p.2)
    ∃ g : ProperProfile e × Environment d → ℝ, Measurable g ∧ (∀ z,0≤g z) ∧
      Integrable g (((μ.prod (environmentLaw ν)).map data).prod (environmentLaw ν)) ∧
      (∫ z, g z ∂((μ.prod (environmentLaw ν)).map data).prod (environmentLaw ν))=1 ∧
      Integrable (fun z => TailDecorrelation.entropyPlus (g z))
        (((μ.prod (environmentLaw ν)).map data).prod (environmentLaw ν)) ∧
      (μ.prod (environmentLaw ν)).map (fun p => (data p,field p))=
        (((μ.prod (environmentLaw ν)).map data).prod (environmentLaw ν)).withDensity (fun z => ENNReal.ofReal (g z)) := by
  let μ := markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event
  have := markedArrayLaw_probability e (L.law : Measure (ActualEpisodeArray e)) G.event G.positive_event.ne'
  let data := fun p : MarkedArray e => properData e w₀ (markedData e p)
  have hd : Measurable data := (properData_measurable e w₀).comp (markedData_measurable e)
  have hf : Measurable (fun p : MarkedArray e × Environment d => fillUpper e (markedUpper e n p.1,p.2)) :=
    (fillUpper_measurable e).comp (((markedUpper_measurable e n).comp measurable_fst).prodMk measurable_snd)
  have hkl := fillUpper_finite_entropy e ν μ data hd (markedUpper e n) (markedUpper_measurable e n)
    (L.marked_proper_entropy G w₀ n)
  have hdata : (μ.prod (environmentLaw ν)).map (fun p => data p.1)=μ.map data := by
    rw [show (fun p : MarkedArray e × Environment d => data p.1)=data ∘ Prod.fst from rfl,
      ←Measure.map_map hd measurable_fst,Measure.map_fst_prod,measure_univ,one_smul]
  have : IsProbabilityMeasure ((μ.prod (environmentLaw ν)).map
      (fun p => (data p.1,fillUpper e (markedUpper e n p.1,p.2)))) :=
    (Measure.isProbabilityMeasure_map_iff
      ((hd.comp measurable_fst).prodMk hf).aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (μ.map data) :=
    (Measure.isProbabilityMeasure_map_iff hd.aemeasurable).mpr inferInstance
  have h := Entropy.density_of_finite_kl _ _ hkl
  dsimp only [μ,data] at hdata h ⊢
  simpa only [hdata] using h

end StationaryArrayLaw
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators
namespace DirectionalTransience

lemma markedCoordinateProfile_eq {d : ℕ} (e : Direction d) (f : Fin d) (w₀ : ProperProfile e)
    (p : MarkedArray e) (hp : IsProperProfile e (markedProfile e (markedData e p))) :
    coordinateProfile e f (properProfileKernel e) (properData e w₀ (markedData e p))=
      (arrayProfileMeasure e 0 (0,p.2) p.1).map (fun x => x.1 f) := by
  rw [coordinateProfile_apply,properData_kernel_eq e w₀ p hp,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

lemma markedProfile_update {d : ℕ} (e : Direction d) (f : Fin d) (hef : e.1≠f)
    (w₀ : ProperProfile e) (p : MarkedArray e) (ω : Environment d) (n : ℕ)
    (hp : ArrayProfilesConsistent e p.1) (hc : ArrayContinuation e p.1)
    (hh : ∀ j, (p.1.1 j).1<⊤) (hcost : ∀ j, (p.1.1 j).2.2≠⊤)
    (hrel : ArrayRelated e p.1 (0,p.2) (n,((markedShift e)^[n] p).2))
    (h0 : IsProperProfile e (markedProfile e (markedData e p)))
    (hn : IsProperProfile e (markedProfile e (markedData e ((markedShift e)^[n] p)))) :
    ENNReal.ofReal (Real.exp (∑ i∈Finset.range n, arrayRealCost e (((markedShift e)^[i] p).1))) •
      (horizontalCoordinateKernel e f (∑ i∈Finset.range n, arrayNatHeight e (((markedShift e)^[i] p).1))
        (fillUpper e (markedUpper e n p,ω)) ∘ₘ properProfileKernel e (properData e w₀ (markedData e p))) ≤
      (coordinateProfile e f (properProfileKernel e) (properData e w₀ (markedData e ((markedShift e)^[n] p)))).map
        (fun x => x+(markedDisplacement e n p).val f) := by
  simp only [markedShift_iterate_fst]
  rw [properData_kernel_eq e w₀ p h0,horizontalProfileImage_fill e f hef]
  have hu := arrayProfile_measure_update e 0 n p.2 _ p.1 hc (arrayHeight_sum e p.1 hh n)
  have hu' := smul_le_smul_left (ENNReal.ofReal (Real.exp (∑ i∈Finset.range n, arrayRealCost e (StationaryCompact.shift^[i] p.1)))) hu
  rw [smul_smul,exp_sum_discount e p.1 hcost n,one_smul] at hu'
  have hu'' := Measure.map_mono hu' (measurable_of_countable (fun x : HorizontalSpace e => x.1 f))
  rw [Measure.map_smul] at hu''
  change _≤(arrayProfileMeasure e (0+n) (0,p.2) p.1).map (fun x => x.1 f) at hu''
  simp only [zero_add] at hu''
  refine hu''.trans_eq ?_
  rw [markedCoordinateProfile_eq e f w₀ _ hn,markedShift_iterate_fst,arrayProfileMeasure_iterate]
  rw [←arrayProfileMeasure_translation e p.1 hp n (0,p.2) (n,((markedShift e)^[n] p).2)
    (markedDisplacement e n p) (markedDisplacement_spec e n p hrel)]
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryProfile2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def fullMarkedShift {d : ℕ} (e : Direction d) : FullMarkedArray e → FullMarkedArray e :=
  Prod.map (markedShift e) id

lemma fullMarkedShift_iterate_fst {d : ℕ} (e : Direction d) (p : FullMarkedArray e) (n : ℕ) :
    ((fullMarkedShift e)^[n] p).1=(markedShift e)^[n] p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    change markedShift e (((fullMarkedShift e)^[n] p).1)=_
    rw [ih]

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

noncomputable def actualProfileSystem (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e)))
    (w₀ : ProperProfile e) (f : Fin d) (hef : e.1≠f) :
    StationaryProfileSystem ν e f (FullMarkedArray e) (ProperProfile e)
      ((markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event).prod (environmentLaw ν))
      (properProfileKernel e) := by
  let μ := markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event
  haveI := markedArrayLaw_probability e (L.law : Measure (ActualEpisodeArray e)) G.event G.positive_event.ne'
  have hT := L.marked_preserving hue htrans G
  have hF := Measure.quasiMeasurePreserving_fst (μ := μ) (ν := environmentLaw ν)
  have hmarks := markedArrayLaw_ae e (L.law : Measure (ActualEpisodeArray e)) G.event G.measurable_event
    (L.finite_marks.mono fun Y h _ => h)
  have hp := L.marked_profile_proper hue htrans G
  refine {
    T := fullMarkedShift e
    preserving := hT.prod (MeasurePreserving.id (environmentLaw ν))
    data := fun p => properData e w₀ (markedData e p.1)
    measurable_data := (properData_measurable e w₀).comp ((markedData_measurable e).comp measurable_fst)
    full := properProfileKernel_full e
    total := properProfileKernel_total e
    c := fun p => arrayRealCost e p.1.1
    measurable_c := (arrayRealCost_measurable e).comp measurable_fst.fst
    nonneg_c := ae_of_all _ fun p => arrayRealCost_nonneg e p.1.1
    integrable_c := (markedArrayLaw_integrable e _ G.event G.positive_event.ne' _
      (arrayRealCost_measurable e) L.integrable_cost).comp_fst (environmentLaw ν)
    h := fun p => arrayNatHeight e p.1.1
    measurable_h := (arrayNatHeight_measurable e).comp measurable_fst.fst
    positive_h := ?_
    integrable_log_h := ?_
    field := fun n p => fillUpper e (markedUpper e n p.1,p.2)
    measurable_field := fun n => (fillUpper_measurable e).comp
      (((markedUpper_measurable e n).comp measurable_fst).prodMk measurable_snd)
    finite_entropy := fun n _ => L.marked_full_entropy G w₀ n
    offset := fun n p => (markedDisplacement e n p.1).val f
    update := ?_
  }
  · filter_upwards [hF.ae hmarks] with p hm
    exact arrayNatHeight_positive e p.1.1 (hm 0).1 (hm 0).2.1
  · have hm : Measurable (fun Y : ActualEpisodeArray e => Real.log (1+(arrayNatHeight e Y:ℝ))) :=
      Real.measurable_log.comp (measurable_const.add ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
        (arrayNatHeight_measurable e)))
    exact (markedArrayLaw_integrable e _ G.event G.positive_event.ne' _ hm
      L.integrable_logheight).comp_fst (environmentLaw ν)
  · intro n hn
    have hcont := markedArrayLaw_ae e (L.law : Measure (ActualEpisodeArray e)) G.event G.measurable_event
      (show ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event →
        ArrayProfilesConsistent e Y ∧ ArrayContinuation e Y from by
          filter_upwards [L.consistent,L.continuation] with Y ho hc _
          exact ⟨ho.2,hc⟩)
    have hrel := L.marked_related hue htrans G
    have hpn := (hT.iterate n).quasiMeasurePreserving.ae hp
    filter_upwards [hF.ae hcont,hF.ae hmarks,hF.ae hrel,hF.ae hp,hF.ae hpn] with p hco hm hr hp0 hpn0
    simp only [fullMarkedShift_iterate_fst]
    exact markedProfile_update e f hef w₀ p.1 p.2 n hco.1 hco.2
      (fun j => (hm j).2.1) (fun j => (hm j).2.2.2.ne) (hr n) hp0 hpn0

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
end


