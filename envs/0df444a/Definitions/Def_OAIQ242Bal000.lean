-- Prove2me | Definitions.Def_OAIQ242Bal000
-- name    : OAIQ242Bal000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:43:58.17354+00:00
-- url     : https://prove2.me/theorems/079f940f-0dc2-4ff3-8363-39307040d27a
-- title:
--   Definitions bundle OAIQ242Bal000 of the split of OpenAI, Directional transience implies ballisticity
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 329 declarations of OpenAI's Lean: 197 definitions, 6 inductive types or structures, 12 instances and 114 theorems. The definitions and types are `OAI.DirectionalTransience.ActualEpisodeArray`, `OAI.DirectionalTransience.AdaptedBufferNode`, `OAI.DirectionalTransience.AdmissibleBoundaryPrefix`, `OAI.DirectionalTransience.AdmissibleCommonWords`, `OAI.DirectionalTransience.AdmissibleHighWord`, `OAI.DirectionalTransience.AdmissiblePrefix`, `OAI.DirectionalTransience.AdmissibleStep`, `OAI.DirectionalTransience.AdmissibleTrueWord`, `OAI.DirectionalTransience.AlignedRecordPrefix`, `OAI.DirectionalTransience.AmbientCurrentWindow`, `OAI.DirectionalTransience.AnchorSampling.anchorKernel`, `OAI.DirectionalTransience.AnchorSampling.atomError`, `OAI.DirectionalTransience.ArrayAveragedSurvival`, `OAI.DirectionalTransience.ArrayContinuation`, `OAI.DirectionalTransience.ArrayElliptic`, `OAI.DirectionalTransience.ArrayGrowthSector`, `OAI.DirectionalTransience.ArrayOffsetsConsistent`, `OAI.DirectionalTransience.ArrayProfilesConsistent`, `OAI.DirectionalTransience.ArrayRelated`, `OAI.DirectionalTransience.BelowHeight`, `OAI.DirectionalTransience.BlockDecoration`, `OAI.DirectionalTransience.BoundaryAt`, `OAI.DirectionalTransience.BoundaryData`, `OAI.DirectionalTransience.BoundaryData.endpoints`, `OAI.DirectionalTransience.BoundedCommonGaps`, `OAI.DirectionalTransience.BoundedHeightPrefix`, `OAI.DirectionalTransience.BoundedInjection.injectTuple`, `OAI.DirectionalTransience.BoundedInjection.injectionChoice`, `OAI.DirectionalTransience.BoundedInjection.injectionMultiplier`, `OAI.DirectionalTransience.BoundedInjection.injectionOffset`, `OAI.DirectionalTransience.BoundedInjection.injectionProfile`, `OAI.DirectionalTransience.BoxStrip`, `OAI.DirectionalTransience.BudgetProfile`, `OAI.DirectionalTransience.BudgetProfile.toLayerProfile`, `OAI.DirectionalTransience.BudgetProfile.toSupported`, `OAI.DirectionalTransience.BufferChanceData`, `OAI.DirectionalTransience.BufferNodeValid`, `OAI.DirectionalTransience.BufferStageEvent`, `OAI.DirectionalTransience.BufferStageSuccess`, `OAI.DirectionalTransience.BufferWords` and 163 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `Ballisticity_Coupling_StageSeedProfile`, `Ballisticity_Crossings_CommonCutCounting`, `Ballisticity_Crossings_CoordinateHitExact`, `Ballisticity_Crossings_CrossingGap`, `Ballisticity_Crossings_FiniteBoxExit`, `Ballisticity_Crossings_FirstHitUpward`, `Ballisticity_Crossings_Hit`, `Ballisticity_Crossings_HitWord`, `Ballisticity_Entropy_DominatedEntropy`, `Ballisticity_Entropy_EntropyDensity`, `Ballisticity_Entropy_EntropyEvent`, `Ballisticity_Entropy_EntropyPlus`, `Ballisticity_Entropy_EntropyVariational`, `Ballisticity_Entropy_OccupationEntropy`, `Ballisticity_Estimates_AlignedRecordPrefix`, `Ballisticity_Estimates_AllOffsetConsistency`, `Ballisticity_Estimates_AnchorMoments`, `Ballisticity_Estimates_BudgetAdapted`, `Ballisticity_Estimates_BudgetClipping`, `Ballisticity_Estimates_BudgetEndpoint`, `Ballisticity_Estimates_BudgetMeasurable`, `Ballisticity_Estimates_BudgetNormalize`, `Ballisticity_Estimates_BufferChanceData`, `Ballisticity_Estimates_BufferChildNode`, `Ballisticity_Estimates_BufferFirstFailure`, `Ballisticity_Estimates_BufferRestorationScript`, `Ballisticity_Estimates_BufferStageSuccess`, `Ballisticity_Estimates_BufferTree`, `Ballisticity_Estimates_ClassSelection`, `Ballisticity_Estimates_CommonBoundaryRestart`, `Ballisticity_Estimates_CommonLayer`, `Ballisticity_Estimates_CommonTrueRecord`, `Ballisticity_Estimates_CommonWordIncrement`, `Ballisticity_Estimates_CurvePolicyMaximal`, `Ballisticity_Estimates_CurvePrefix`, `Ballisticity_Estimates_DescendingTrials`, `Ballisticity_Estimates_DirectBridge`, `Ballisticity_Estimates_Dust`, `Ballisticity_Estimates_EndpointPrefix`, `Ballisticity_Estimates_FiniteClasses`, `Ballisticity_Estimates_FinitePolicyFailure`, `Ballisticity_Estimates_FirstHighRecord`, `Ballisticity_Estimates_FirstWordEvent`, `Ballisticity_Estimates_FixedPairSuffix`, `Ballisticity_Estimates_GlobalProfile`, `Ballisticity_Estimates_GlobalTuple`, `Ballisticity_Estimates_GridOscillation`, `Ballisticity_Estimates_GridTrials`, `Ballisticity_Estimates_IndependentPairLaw`, `Ballisticity_Estimates_JointPastRestart`, `Ballisticity_Estimates_LocalStoppedSplice`, `Ballisticity_Estimates_PairPrefix`, `Ballisticity_Estimates_PolicyGoodMass`, `Ballisticity_Estimates_RawPairEndpoint`, `Ballisticity_Estimates_RawPairLocality`, `Ballisticity_Estimates_RawPairRetention`, `Ballisticity_Estimates_RecordIndexTime`, `Ballisticity_Estimates_ReferenceFeller`, `Ballisticity_Estimates_RelativeBudget`, `Ballisticity_Estimates_SelectedBoundaryRestart`, `Ballisticity_Estimates_SharedWordCylinderLower`, `Ballisticity_Estimates_StageClassification`, `Ballisticity_Estimates_StageRetention`, `Ballisticity_Estimates_StageStopping`, `Ballisticity_Estimates_StrictRecord`, `Ballisticity_Estimates_SuccessfulWords`, `Ballisticity_Estimates_SurvivalLimit`, `Ballisticity_Estimates_SymmetricTruncate`, `Ballisticity_Estimates_TupleEndpoint`, `Ballisticity_Estimates_WordConcatenation`, `Ballisticity_Estimates_WordDepartures`, `Ballisticity_Geometry_CurvePolicyTubeMass`, `Ballisticity_Geometry_FiniteCoordinateApproximation`, `Ballisticity_Geometry_FiniteWordGeometry`, `Ballisticity_Geometry_HeightSlab`, `Ballisticity_Geometry_LatticeVector`, `Ballisticity_Geometry_SignedCoordinate`, `Ballisticity_Geometry_SignedHeight`, `Ballisticity_Geometry_WindowProjection`, `Ballisticity_Geometry_WordCoordinate`, `Ballisticity_Geometry_WordHeightGain`, `Ballisticity_Renewal_Regeneration`, `Ballisticity_Renewal_RegenerationWords`, `Ballisticity_Stationary_Array`, `Ballisticity_Stationary_ArrayClosed`, `Ballisticity_Stationary_ArrayDust`, `Ballisticity_Stationary_ArrayFiniteClasses`, `Ballisticity_Stationary_ArrayMap`, `Ballisticity_Stationary_ArrayPermutation`, `Ballisticity_Stationary_ArrayProfileConsistency`, `Ballisticity_Stationary_ArraySurvival`, `Ballisticity_Stationary_ArrayTopology`, `Ballisticity_Stationary_ArrayWindowMarks`, `Ballisticity_Stationary_EpisodeAdapted`, `Ballisticity_Stationary_EpisodeCharts`, `Ballisticity_Stationary_EpisodeInjection`, `Ballisticity_Stationary_OperationalEpisode`, `Ballisticity_Stationary_StationaryWindowEntropy`, `Ballisticity_Walk_ArrayGrowthEvent`, `Ballisticity_Walk_FixedQuenchedKernel`, `Ballisticity_Walk_RawPairKernel`, `Ballisticity_Walk_StateTrajectory`, `Ballisticity_Walk_UpperKernel`.
--
--   **Imports.** It imports the published bundle `Def_DirectionalBallisticity`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ242Bal002`, `OAIQ242Bal003` and `OAIQ242Bal004`; the statements `OAI.DirectionalTransience.crossing_failure_rapidDecay`, `OAI.DirectionalTransience.independent_commonWordIncrement_integrable`, `OAI.DirectionalTransience.recordFluctuationScale_tendsto` and `OAI.DirectionalTransience.seed_mass_at_scale`; the proof of `OAI.DirectionalTransience.normalJointPast_product_identification`.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_DirectionalBallisticity

section
-- module Solutions.OAIQ242_BAL.Compat
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
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_StateTrajectory
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

noncomputable def stateTrajectory {d : ℕ} : Kernel (State d) (ℕ → State d) :=
  (Kernel.traj (historyTransition (d := d)) 0).comap
    (fun z _ => z) (Measurable.of_eval fun _ => measurable_id)

instance stateTrajectory_markov {d : ℕ} : IsMarkovKernel (stateTrajectory (d := d)) := by
  unfold stateTrajectory
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def quenchedKernel {d : ℕ} : Kernel (State d) (Path d) :=
  stateTrajectory.map (fun z n => (z n).2)

instance quenchedKernel_markov {d : ℕ} : IsMarkovKernel (quenchedKernel (d := d)) := by
  apply Kernel.IsMarkovKernel.map
  exact Measurable.of_eval fun n => measurable_snd.comp (measurable_pi_apply n)

lemma stateTrajectory_initial {d : ℕ} (z : State d) :
    (stateTrajectory z).map (fun X => X 0) = Measure.dirac z := by
  rw [stateTrajectory, Kernel.comap_apply]
  have h := Kernel.traj_map_frestrictLe_apply (X := fun _ => State d)
    (κ := historyTransition (d := d))
    0 0 (fun _ => z)
  rw [Kernel.partialTraj_self, Kernel.id_apply] at h
  have hm : Measurable (fun X : (i : Finset.Iic 0) → State d =>
      X ⟨0, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
  have := congrArg (fun μ => μ.map
    (fun X : (i : Finset.Iic 0) → State d => X ⟨0, Finset.mem_Iic.mpr le_rfl⟩)) h
  rw [Measure.map_map hm (Preorder.measurable_frestrictLe 0), Measure.map_dirac' hm] at this
  exact this

lemma quenched_initial {d : ℕ} (z : State d) :
    (quenchedKernel z).map (fun X => X 0) = Measure.dirac z.2 := by
  have hm : Measurable (fun z : ℕ → State d => fun n => (z n).2) := by fun_prop
  rw [quenchedKernel, Kernel.map_apply _ hm, Measure.map_map (measurable_pi_apply 0) hm]
  have h := congrArg (fun μ => μ.map Prod.snd) (stateTrajectory_initial z)
  rw [Measure.map_map measurable_snd (measurable_pi_apply 0),
    Measure.map_dirac' measurable_snd] at h
  exact h

lemma quenched_initial_ae {d : ℕ} (z : State d) :
    ∀ᵐ X ∂quenchedKernel z, X 0 = z.2 := by
  have h : ∀ᵐ x ∂(quenchedKernel z).map (fun X => X 0), x = z.2 := by
    rw [quenched_initial]
    exact ae_dirac_iff (measurableSet_singleton _ ) |>.mpr rfl
  exact (ae_map_iff (measurable_pi_apply 0).aemeasurable
    (measurableSet_singleton _)).mp h

instance state_measurableSingleton {d : ℕ} : MeasurableSingletonClass (State d) := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def AdmissibleStep {d : ℕ} (z z' : State d) : Prop :=
  ∃ e : Direction d, z' = (z.1, z.2 + step e)

lemma measurableSet_admissibleStep {d : ℕ} :
    MeasurableSet {zz : State d × State d | AdmissibleStep zz.1 zz.2} := by
  simp only [AdmissibleStep, Prod.ext_iff, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro e
  exact (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
    (measurable_fst.comp measurable_fst)).inter
    (measurableSet_eq_fun (measurable_snd.comp measurable_snd)
      ((measurable_snd.comp measurable_fst).add_const (step e)))

lemma transition_admissible {d : ℕ} (z : State d) :
    ∀ᵐ z' ∂transition z, AdmissibleStep z z' := by
  change ∀ᵐ z' ∂∑ e : Direction d,
    ((z.1 z.2).1 e : ℝ≥0∞) • Measure.dirac (z.1, z.2 + step e), AdmissibleStep z z'
  apply ae_finsetSum_measure_iff.mpr
  intro e _
  apply Measure.ae_smul_measure
  apply (ae_dirac_iff _).mpr
  · exact ⟨e, rfl⟩
  · exact measurableSet_admissibleStep.preimage (measurable_const.prodMk measurable_id)

lemma stateTrajectory_admissible {d : ℕ} (z : State d) :
    ∀ᵐ X ∂stateTrajectory z, ∀ n, AdmissibleStep (X n) (X (n + 1)) := by
  rw [stateTrajectory, Kernel.comap_apply]
  apply ae_all_iff.mpr
  intro n
  let p := fun zz : ((i : Finset.Iic n) → State d) × State d =>
    AdmissibleStep (zz.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) zz.2
  have hm : Measurable (fun zz : ((i : Finset.Iic n) → State d) × State d =>
      (zz.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩, zz.2)) := by fun_prop
  have hp : MeasurableSet {zz | p zz} :=
    measurableSet_admissibleStep.preimage hm
  have h : ∀ᵐ zz ∂(Kernel.partialTraj (X := fun _ => State d) (historyTransition (d := d)) 0 n (fun _ => z))
      ⊗ₘ historyTransition (d := d) n, p zz := by
    apply Measure.ae_compProd_of_ae_ae hp
    exact ae_of_all _ fun x => transition_admissible _
  rw [Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le n)] at h
  exact (ae_map_iff (by fun_prop) hp).mp h

lemma stateTrajectory_environment {d : ℕ} (z : State d) :
    ∀ᵐ X ∂stateTrajectory z, ∀ n, (X n).1 = z.1 := by
  have h0 : ∀ᵐ X ∂stateTrajectory z, X 0 = z := by
    have h : ∀ᵐ y ∂(stateTrajectory z).map (fun X => X 0), y = z := by
      rw [stateTrajectory_initial]
      exact (ae_dirac_iff (measurableSet_singleton _)).mpr rfl
    exact (ae_map_iff (measurable_pi_apply 0).aemeasurable
      (measurableSet_singleton _)).mp h
  filter_upwards [h0, stateTrajectory_admissible z] with X hX hstep n
  induction n with
  | zero => rw [hX]
  | succ n ih =>
    obtain ⟨e, he⟩ := hstep n
    rw [he]
    exact ih

lemma quenched_nearest_neighbor {d : ℕ} (z : State d) :
    ∀ᵐ X ∂quenchedKernel z, ∀ n, ∃ e : Direction d, X (n + 1) = X n + step e := by
  have hm : Measurable (fun z : ℕ → State d => fun n => (z n).2) := by fun_prop
  rw [quenchedKernel, Kernel.map_apply _ hm]
  apply (ae_map_iff hm.aemeasurable _).mpr
  · filter_upwards [stateTrajectory_admissible z] with X hX n
    obtain ⟨e, he⟩ := hX n
    exact ⟨e, congrArg Prod.snd he⟩
  · simp only [Set.ofPred_forall, Set.ofPred_exists]
    apply MeasurableSet.iInter
    intro n
    apply MeasurableSet.iUnion
    intro e
    exact measurableSet_eq_fun (measurable_pi_apply _) ((measurable_pi_apply _).add_const _)

lemma step_injective {d : ℕ} : Function.Injective (step (d := d)) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ he
  have hij : i = j := by
    by_contra hne
    have hi := congrFun he i
    cases b <;> simp [step, hne] at hi
  subst j
  have hi := congrFun he i
  cases b <;> cases c <;> simp_all [step]

lemma transition_singleton_step {d : ℕ} (z : State d) (e : Direction d) :
    transition z {(z.1, z.2 + step e)} = ((z.1 z.2).1 e : ℝ≥0∞) := by
  change (∑ f : Direction d,
    ((z.1 z.2).1 f : ℝ≥0∞) • Measure.dirac (z.1, z.2 + step f))
      {(z.1, z.2 + step e)} = _
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f _ hne
    have hh : (z.1, z.2 + step f) ∉ ({(z.1, z.2 + step e)} : Set (State d)) := by
      intro he
      apply hne
      exact step_injective (add_left_cancel (congrArg Prod.snd (Set.mem_singleton_iff.mp he)))
    simp [Measure.dirac_apply' _ (measurableSet_singleton _), hh]
  · simp

def stateCylinder {d : ℕ} (f : ℕ → State d) (n : ℕ) : Set (ℕ → State d) :=
  {X | ∀ i ≤ n, X i = f i}

lemma stateCylinder_eq_preimage {d : ℕ} (f : ℕ → State d) (n : ℕ) :
    stateCylinder f n = (fun X : ℕ → State d => Preorder.frestrictLe n X) ⁻¹' {fun i : Finset.Iic n => f i} := by
  ext X
  simp only [stateCylinder, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    exact h i (Finset.mem_Iic.mp i.2)
  · intro h i hi
    exact congrFun h ⟨i, Finset.mem_Iic.mpr hi⟩

lemma stateTrajectory_cylinder_succ {d : ℕ} (z : State d) (f : ℕ → State d) (n : ℕ) :
    stateTrajectory z (stateCylinder f (n + 1)) =
      transition (f n) {f (n + 1)} * stateTrajectory z (stateCylinder f n) := by
  rw [stateTrajectory, Kernel.comap_apply]
  have h := Kernel.partialTraj_compProd_eq_map_traj (X := fun _ => State d)
    (κ := historyTransition (d := d)) (x₀ := fun _ => z) (Nat.zero_le n)
  have hm : Measurable (fun X : ℕ → State d => (Preorder.frestrictLe n X, X (n + 1))) := by
    fun_prop
  have he : (fun X : ℕ → State d => (Preorder.frestrictLe n X, X (n + 1))) ⁻¹'
      ({fun i : Finset.Iic n => f i} ×ˢ {f (n + 1)}) = stateCylinder f (n + 1) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
      stateCylinder, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h₁, h₂⟩ i hi
      obtain hi | rfl := Nat.lt_or_eq_of_le hi
      · exact congrFun h₁ ⟨i, Finset.mem_Iic.mpr (by omega)⟩
      · exact h₂
    · intro hX
      exact ⟨funext fun i => hX i (by have := Finset.mem_Iic.mp i.2; omega), hX _ le_rfl⟩
  have hs := congrArg (fun μ : Measure (((i : Finset.Iic n) → State d) × State d) =>
    μ ({fun i : Finset.Iic n => f i} ×ˢ {f (n + 1)})) h
  rw [Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton, Measure.map_apply hm
      ((measurableSet_singleton _).prod (measurableSet_singleton _)), he] at hs
  rw [← hs]
  congr 1
  rw [stateCylinder_eq_preimage, ← Measure.map_apply (Preorder.measurable_frestrictLe n)
    (measurableSet_singleton _), Kernel.traj_map_frestrictLe_apply]

lemma stateTrajectory_cylinder {d : ℕ} (z : State d) (f : ℕ → State d)
    (hf : f 0 = z) (n : ℕ) :
    stateTrajectory z (stateCylinder f n) =
      ∏ i ∈ Finset.range n, transition (f i) {f (i + 1)} := by
  induction n with
  | zero =>
    have he : stateCylinder f 0 = (fun X : ℕ → State d => X 0) ⁻¹' {z} := by
      ext X
      simp [stateCylinder, hf]
    rw [he, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton _),
      stateTrajectory_initial]
    simp
  | succ n ih =>
    rw [stateTrajectory_cylinder_succ, ih, Finset.prod_range_succ, mul_comm]

abbrev rowSigma {d : ℕ} (S : Set (Lattice d)) : MeasurableSpace (Environment d) :=
  ⨆ x ∈ S, MeasurableSpace.comap (fun ω : Environment d => ω x) inferInstance

lemma rowSigma_le {d : ℕ} (S : Set (Lattice d)) : rowSigma S ≤ (inferInstance : MeasurableSpace (Environment d)) := by
  exact iSup_le fun x => iSup_le fun _ => (measurable_pi_apply x).comap_le

lemma measurable_row_on {d : ℕ} {S : Set (Lattice d)} {x : Lattice d} (hx : x ∈ S) :
    @Measurable _ _ (rowSigma S) _ (fun ω : Environment d => ω x) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)

lemma rowSigma_mono {d : ℕ} {S T : Set (Lattice d)} (hST : S ⊆ T) :
    rowSigma S ≤ rowSigma T :=
  iSup₂_le fun x hx => le_iSup_of_le x (le_iSup_of_le (hST hx) le_rfl)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordDepartures
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

def wordDepartures {d : ℕ} (x : Lattice d) : List (Direction d) → Finset (Lattice d)
  | [] => ∅
  | e :: w => insert x (wordDepartures (x + step e) w)

noncomputable def wordWeight {d : ℕ} (ω : Environment d) (x : Lattice d) :
    List (Direction d) → ℝ
  | [] => 1
  | e :: w => ((ω x).1 e : ℝ) * wordWeight ω (x + step e) w

lemma measurable_wordWeight_on {d : ℕ} {S : Set (Lattice d)} (x : Lattice d)
    (w : List (Direction d)) (hS : ∀ y ∈ wordDepartures x w, y ∈ S) :
    @Measurable _ _ (rowSigma S) _ (fun ω => wordWeight ω x w) := by
  induction w generalizing x with
  | nil => exact measurable_const
  | cons e w ih =>
    have hx : x ∈ S := hS x (Finset.mem_insert_self _ _)
    have he : @Measurable _ _ (rowSigma S) _
        (fun ω : Environment d => ((ω x).1 e : ℝ)) :=
      ((measurable_pi_apply e).comp
        (measurable_subtype_coe.comp (measurable_row_on hx))).coe_nnreal_real
    exact he.mul (ih _ (fun y hy => hS y (Finset.mem_insert_of_mem hy)))

def wordPath {d : ℕ} (x : Lattice d) : List (Direction d) → Path d
  | [], _ => x
  | _ :: _, 0 => x
  | e :: w, n + 1 => wordPath (x + step e) w n

@[simp] lemma wordPath_zero {d : ℕ} (x : Lattice d) (w : List (Direction d)) :
    wordPath x w 0 = x := by cases w <;> rfl

def wordCylinder {d : ℕ} (x : Lattice d) (w : List (Direction d)) : Set (Path d) :=
  {X | ∀ i ≤ w.length, X i = wordPath x w i}

lemma measurableSet_wordCylinder {d : ℕ} (x : Lattice d) (w : List (Direction d)) :
    MeasurableSet (wordCylinder x w) := by
  simp only [wordCylinder, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_eq_fun (measurable_pi_apply i : Measurable (fun X : Path d => X i))
      measurable_const

lemma wordPath_transition_product {d : ℕ} (ω : Environment d) (x : Lattice d)
    (w : List (Direction d)) :
    (∏ i ∈ Finset.range w.length,
      transition (ω, wordPath x w i) {(ω, wordPath x w (i + 1))}) =
    ENNReal.ofReal (wordWeight ω x w) := by
  induction w generalizing x with
  | nil => simp [wordWeight]
  | cons e w ih =>
    rw [List.length_cons, Finset.prod_range_succ']
    simp only [wordPath, wordPath_zero]
    rw [ih, transition_singleton_step, wordWeight, ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    simp [mul_comm]

lemma quenched_wordCylinder {d : ℕ} (ω : Environment d) (x : Lattice d)
    (w : List (Direction d)) :
    quenchedKernel (ω, x) (wordCylinder x w) = ENNReal.ofReal (wordWeight ω x w) := by
  have hm : Measurable (fun z : ℕ → State d => fun n => (z n).2) := by fun_prop
  rw [quenchedKernel, Kernel.map_apply _ hm, Measure.map_apply hm (measurableSet_wordCylinder x w)]
  have he : (fun z : ℕ → State d => fun n => (z n).2) ⁻¹' wordCylinder x w
      =ᵐ[stateTrajectory (ω, x)] stateCylinder (fun n => (ω, wordPath x w n)) w.length := by
    filter_upwards [stateTrajectory_environment (ω, x)] with X hX
    apply propext
    change (∀ i ≤ w.length, (X i).2 = wordPath x w i) ↔
      (∀ i ≤ w.length, X i = (ω, wordPath x w i))
    constructor
    · intro hh n hn
      exact Prod.ext (hX n) (hh n hn)
    · intro hh n hn
      exact congrArg Prod.snd (hh n hn)
  rw [measure_congr he, stateTrajectory_cylinder _ _ (by simp), wordPath_transition_product]

def NoDrop {d : ℕ} (ℓ : Vector d) (x : Lattice d) : Set (Path d) :=
  {X | ∀ n, dot (realPosition x) ℓ ≤ dot (realPosition (X n)) ℓ}

def FutureNoDrop {d : ℕ} (ℓ : Vector d) (n : ℕ) : Set (Path d) :=
  {X | ∀ i, dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n + i))) ℓ}

def extendPrefix {d : ℕ} (n : ℕ) (f : (i : Finset.Iic n) → Lattice d) : Path d :=
  fun i => if hi : i ≤ n then f ⟨i, Finset.mem_Iic.mpr hi⟩ else 0

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_Hit
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

def HitAt {d : ℕ} (S T : Set (Lattice d)) (n : ℕ) : Set (Path d) :=
  {X | X n ∈ T ∧ ∀ i < n, X i ∈ S}

def Hit {d : ℕ} (S T : Set (Lattice d)) : Set (Path d) := ⋃ n, HitAt S T n

lemma measurableSet_hitAt {d : ℕ} (S T : Set (Lattice d)) (n : ℕ) :
    MeasurableSet (HitAt S T n) := by
  apply MeasurableSet.inter ((measurable_pi_apply n) T.to_countable.measurableSet)
  change MeasurableSet {X : Path d | ∀ i < n, X i ∈ S}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    (measurable_pi_apply i) S.to_countable.measurableSet

lemma hitAt_pairwise_disjoint {d : ℕ} {S T : Set (Lattice d)} (hST : Disjoint S T) :
    Pairwise (fun n m => Disjoint (HitAt S T n) (HitAt S T m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro X hn hm
  rcases lt_or_gt_of_ne hnm with h | h
  · exact Set.disjoint_left.mp hST (hm.2 n h) hn.1
  · exact Set.disjoint_left.mp hST (hn.2 m h) hm.1

noncomputable def hitKernel {d : ℕ} (S T : Set (Lattice d)) : Kernel (State d) (Lattice d) :=
  Kernel.sum fun n => (quenchedKernel.restrict (measurableSet_hitAt S T n)).map (fun X => X n)

lemma hitKernel_apply {d : ℕ} (S T U : Set (Lattice d)) (z : State d) :
    hitKernel S T z U = ∑' n, quenchedKernel z (HitAt S (T ∩ U) n) := by
  rw [hitKernel, Kernel.sum_apply' _ _ U.to_countable.measurableSet]
  apply tsum_congr
  intro n
  rw [Kernel.map_apply' _ (measurable_pi_apply n) _ U.to_countable.measurableSet,
    Kernel.restrict_apply' _ _ _ ((measurable_pi_apply n) U.to_countable.measurableSet)]
  congr 1
  ext X
  simp only [Set.mem_inter_iff, Set.mem_preimage, HitAt, Set.mem_ofPred_eq]
  tauto

lemma hitKernel_total {d : ℕ} {S T : Set (Lattice d)} (hST : Disjoint S T) (z : State d) :
    hitKernel S T z Set.univ = quenchedKernel z (Hit S T) := by
  rw [hitKernel_apply, Set.inter_univ]
  exact (measure_iUnion (hitAt_pairwise_disjoint hST) (measurableSet_hitAt S T)).symm

lemma hitKernel_total_le_one {d : ℕ} {S T : Set (Lattice d)} (hST : Disjoint S T) (z : State d) :
    hitKernel S T z Set.univ ≤ 1 := by
  rw [hitKernel_total hST]
  exact prob_le_one

def Cross {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) : Set (Path d) :=
  {X | ∃ n, dot (realPosition x) ℓ + H ≤ dot (realPosition (X n)) ℓ ∧
    ∀ i < n, dot (realPosition x) ℓ ≤ dot (realPosition (X i)) ℓ}

def Strip {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) : Set (Lattice d) :=
  {y | dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ ∧
    dot (realPosition y) ℓ < dot (realPosition x) ℓ + H}

def Upper {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) : Set (Lattice d) :=
  {y | dot (realPosition x) ℓ + H ≤ dot (realPosition y) ℓ}

lemma disjoint_strip_upper {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    Disjoint (Strip ℓ x H) (Upper ℓ x H) := by
  apply Set.disjoint_left.mpr
  intro y hy hu
  exact (not_lt_of_ge hu) hy.2

noncomputable def crossingQuenched {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ)
    (ω : Environment d) : ℝ≥0∞ := quenchedKernel (ω, x) (Cross ℓ x H)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightSlab
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

lemma hitKernel_apply_eq_hit {d : ℕ} {S T : Set (Lattice d)}
    (hST : Disjoint S T) (U : Set (Lattice d)) (z : State d) :
    hitKernel S T z U = quenchedKernel z (Hit S (T ∩ U)) := by
  rw [hitKernel_apply]
  exact (measure_iUnion (hitAt_pairwise_disjoint (hST.mono_right Set.inter_subset_left))
    (measurableSet_hitAt S (T ∩ U))).symm

noncomputable def normalizedMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) : Measure α := (μ Set.univ)⁻¹ • μ

lemma normalizedMeasure_probability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (hμ : μ Set.univ ≠ 0) :
    IsProbabilityMeasure (normalizedMeasure μ) := by
  constructor
  simp only [normalizedMeasure, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hμ (measure_ne_top μ Set.univ)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StrictRecord
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

def StrictRecord {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) : Prop :=
  ∀ j < n, dot (realPosition (X j)) ℓ < dot (realPosition (X n)) ℓ

def TrueRecord {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) : Prop :=
  StrictRecord ℓ X n ∧ X ∈ FutureNoDrop ℓ n

def FirstTrueRecord {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) : Prop :=
  0 < n ∧ TrueRecord ℓ X n ∧ ∀ j, 0 < j → j < n → ¬ TrueRecord ℓ X j

lemma wordDepartures_mem_iff {d : ℕ} (x y : Lattice d) (w : List (Direction d)) :
    y ∈ wordDepartures x w ↔ ∃ j < w.length, y = wordPath x w j := by
  induction w generalizing x with
  | nil => simp [wordDepartures]
  | cons e w ih =>
    rw [wordDepartures, Finset.mem_insert, ih]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨j + 1, by simpa using hj, rfl⟩
    · rintro ⟨j, hj, he⟩
      cases j with
      | zero => exact Or.inl (by simpa using he)
      | succ j => exact Or.inr ⟨j, by simpa using hj, he⟩

def AdmissibleTrueWord {d : ℕ} (ℓ : Vector d) (w : List (Direction d)) : Prop :=
  0 < w.length ∧
  (∀ j < w.length, 0 ≤ dot (realPosition (wordPath 0 w j)) ℓ ∧
    dot (realPosition (wordPath 0 w j)) ℓ <
      dot (realPosition (wordPath 0 w w.length)) ℓ) ∧
  ∀ j, 0 < j → j < w.length → StrictRecord ℓ (wordPath 0 w) j →
    ∃ k, j < k ∧ k < w.length ∧ dot (realPosition (wordPath 0 w k)) ℓ <
      dot (realPosition (wordPath 0 w j)) ℓ

noncomputable def conditionedLaw {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) :
    Measure (Path d) :=
  (annealedLaw ν (NoDrop ℓ 0))⁻¹ • (annealedLaw ν).restrict (NoDrop ℓ 0)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FirstWordEvent
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

lemma exists_word_prefix {d : ℕ} (X : Path d)
    (hX : ∀ n, ∃ e : Direction d, X (n + 1) = X n + step e) (N : ℕ) :
    ∃ w : List (Direction d), w.length = N ∧ X ∈ wordCylinder (X 0) w := by
  induction N generalizing X with
  | zero =>
    refine ⟨[], rfl, ?_⟩
    intro j hj
    have : j = 0 := by simpa using hj
    subst j
    rfl
  | succ N ih =>
    obtain ⟨e, he⟩ := hX 0
    obtain ⟨w, hw, hwp⟩ := ih (fun j => X (j + 1)) (fun n => hX (n + 1))
    refine ⟨e :: w, by simp [hw], ?_⟩
    intro j hj
    cases j with
    | zero => rfl
    | succ j =>
      have hh := hwp j (by simpa only [List.length_cons, Nat.add_le_add_iff_right] using hj)
      simpa only [wordPath, he] using hh

lemma word_eq_of_paths {d : ℕ} (x : Lattice d) (u v : List (Direction d))
    (hlen : u.length = v.length)
    (hpath : ∀ j ≤ u.length, wordPath x u j = wordPath x v j) : u = v := by
  induction u generalizing v x with
  | nil =>
    have : v = [] := List.length_eq_zero_iff.mp hlen.symm
    exact this.symm
  | cons e u ih =>
    cases v with
    | nil => simp at hlen
    | cons f v =>
      have he : e = f := by
        apply step_injective
        apply add_left_cancel (a := x)
        simpa only [wordPath, wordPath_zero] using hpath 1 (by simp)
      subst f
      congr 1
      apply ih (x + step e) v (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen)
      intro j hj
      simpa only [wordPath] using hpath (j + 1) (by simpa only [List.length_cons,
        Nat.add_le_add_iff_right] using hj)

lemma word_eq_of_cylinders {d : ℕ} (x : Lattice d) (u v : List (Direction d))
    (X : Path d) (hu : X ∈ wordCylinder x u) (hv : X ∈ wordCylinder x v)
    (hlen : u.length = v.length) : u = v := by
  apply word_eq_of_paths x u v hlen
  intro j hj
  exact (hu j hj).symm.trans (hv j (hlen ▸ hj))

def FirstWordEvent {d : ℕ} (ℓ : Vector d) (w : List (Direction d)) : Set (Path d) :=
  NoDrop ℓ 0 ∩ (wordCylinder 0 w ∩ {X | FirstTrueRecord ℓ X w.length})

instance wordMeasurableSpace {d : ℕ} : MeasurableSpace (List (Direction d)) := ⊤

instance wordDiscreteMeasurable {d : ℕ} : DiscreteMeasurableSpace (List (Direction d)) := ⟨fun _ => trivial⟩

open scoped Classical in
noncomputable def firstWord {d : ℕ} (ℓ : Vector d) (X : Path d) : List (Direction d) :=
  if h : ∃ w, X ∈ FirstWordEvent ℓ w then h.choose else []

noncomputable def renewSuffix {d : ℕ} (ℓ : Vector d) (X : Path d) : Path d :=
  fun j => X ((firstWord ℓ X).length + j) - X (firstWord ℓ X).length

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_RegenerationWords
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

noncomputable def regenerationWords {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) :
    List (Direction d) := firstWord ℓ ((renewSuffix ℓ)^[n] X)

noncomputable def regenerationTimes {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, (regenerationWords ℓ X i).length

@[simp] lemma regenerationTimes_zero {d : ℕ} (ℓ : Vector d) (X : Path d) :
    regenerationTimes ℓ X 0 = 0 := by simp [regenerationTimes]

open scoped Classical in
noncomputable def recordCount {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, if StrictRecord ℓ X (j + 1) then 1 else 0

@[simp] lemma recordCount_zero {d : ℕ} (ℓ : Vector d) (X : Path d) :
    recordCount ℓ X 0 = 0 := by simp [recordCount]

def RecordIndexPrefix {d : ℕ} (ℓ : Vector d) (r n : ℕ) : Set (Path d) :=
  {X | 0 < n ∧ StrictRecord ℓ X n ∧ recordCount ℓ X n = r ∧
    ∀ j ≤ n, dot (realPosition (0 : Lattice d)) ℓ ≤ dot (realPosition (X j)) ℓ}

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_WordHeightGain
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

lemma dot_step {d : ℕ} (ℓ : Vector d) (e : Direction d) :
    dot (realPosition (step e)) ℓ = if e.2 then ℓ e.1 else -ℓ e.1 := by
  classical
  simp only [dot, realPosition, step, Int.cast_ite, Int.cast_one, Int.cast_neg,
    Int.cast_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, if_true]
  split <;> simp_all

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_LatticeVector
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

noncomputable def latticeVector {d : ℕ} (x : Lattice d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (realPosition x)

@[simp] lemma latticeVector_zero {d : ℕ} : latticeVector (0 : Lattice d) = 0 := by
  ext i
  simp [latticeVector, realPosition]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_SignedCoordinate
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

def signedCoordinate {d : ℕ} (e : Direction d) (x : Lattice d) : ℝ :=
  if e.2 then (x e.1 : ℝ) else -(x e.1 : ℝ)

lemma signedCoordinate_add {d : ℕ} (e : Direction d) (x y : Lattice d) :
    signedCoordinate e (x+y) = signedCoordinate e x + signedCoordinate e y := by
  simp only [signedCoordinate, Pi.add_apply, Int.cast_add]
  split <;> ring

def AdmissiblePrefix {d : ℕ} (n : ℕ) : Set (Path d) :=
  {X | X 0 = 0 ∧ ∀ j < n, ∃ e : Direction d, X (j+1) = X j+step e}

def BoundedHeightPrefix {d : ℕ} (ℓ : Vector d) (H : ℝ) (n : ℕ) : Set (Path d) :=
  {X | ∀ j ≤ n, 0 ≤ dot (realPosition (X j)) ℓ ∧ dot (realPosition (X j)) ℓ ≤ H}

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_Regeneration
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

lemma signedCoordinate_nsmul {d : ℕ} (u : Direction d) (x : Lattice d) (n : ℕ) :
    signedCoordinate u (n • x) = n * signedCoordinate u x := by
  induction n with
  | zero => simp [signedCoordinate]
  | succ n ih => rw [succ_nsmul, signedCoordinate_add, ih, Nat.cast_add, Nat.cast_one]; ring

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_WordCoordinate
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

noncomputable def wordCoordinate {d : ℕ} (e : Direction d) (w : List (Direction d)) : ℝ :=
  signedCoordinate e (wordPath 0 w w.length)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_FixedQuenchedKernel
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

lemma dot_comm {d : ℕ} (v w : Vector d) : dot v w = dot w v := by
  simp only [dot, mul_comm]

lemma dot_signed_direction {d : ℕ} (e : Direction d) (x : Lattice d) :
    dot (realPosition x) (realPosition (step e)) = signedCoordinate e x := by
  rw [dot_comm, dot_step]
  rfl

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonTrueRecord
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

def CommonTrueRecord {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) (n m : ℕ) : Prop :=
  TrueRecord ℓ P.1 n ∧ TrueRecord ℓ P.2 m ∧
    dot (realPosition (P.1 n)) ℓ = dot (realPosition (P.2 m)) ℓ

def FirstCommonTrueRecord {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧ CommonTrueRecord ℓ P n m ∧
    ∀ j k, 0 < j → j < n → 0 < k → k < m → ¬ CommonTrueRecord ℓ P j k

def AdmissibleCommonWords {d : ℕ} (ℓ : Vector d) (x y : Lattice d)
    (w v : List (Direction d)) : Prop :=
  0 < w.length ∧ 0 < v.length ∧
  dot (realPosition (wordPath x w w.length)) ℓ =
    dot (realPosition (wordPath y v v.length)) ℓ ∧
  StrictRecord ℓ (wordPath x w) w.length ∧
  StrictRecord ℓ (wordPath y v) v.length ∧
  (∀ j ≤ w.length, dot (realPosition x) ℓ ≤ dot (realPosition (wordPath x w j)) ℓ) ∧
  (∀ k ≤ v.length, dot (realPosition y) ℓ ≤ dot (realPosition (wordPath y v k)) ℓ) ∧
  ∀ j k, 0 < j → j < w.length → 0 < k → k < v.length →
    StrictRecord ℓ (wordPath x w) j → StrictRecord ℓ (wordPath y v) k →
    dot (realPosition (wordPath x w j)) ℓ = dot (realPosition (wordPath y v k)) ℓ →
    (∃ a, j < a ∧ a < w.length ∧ dot (realPosition (wordPath x w a)) ℓ <
      dot (realPosition (wordPath x w j)) ℓ) ∨
    (∃ b, k < b ∧ b < v.length ∧ dot (realPosition (wordPath y v b)) ℓ <
      dot (realPosition (wordPath y v k)) ℓ)

def commonWordEvent {d : ℕ} (ℓ : Vector d) (x y : Lattice d)
    (w v : List (Direction d)) : Set (Path d × Path d) :=
  (wordCylinder x w ×ˢ wordCylinder y v) ∩
    {P | FirstCommonTrueRecord ℓ P w.length v.length}

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PairPrefix
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

def FirstLayerHit {d : ℕ} (h : Lattice d → ℤ) (H : ℤ) (n : ℕ) : Set (Path d) :=
  {X | h (X n) = H ∧ ∀ j < n, h (X j) < H}

def CommonTrueAbove {d : ℕ} (ℓ : Vector d) (K : ℤ) : Set (Path d × Path d) :=
  {P | ∃ n m, (K : ℝ) < dot (realPosition (P.1 n)) ℓ ∧ CommonTrueRecord ℓ P n m}

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IndependentPairLaw
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

def FirstPairWordEvent {d : ℕ} (ℓ : Vector d)
    (wv : List (Direction d) × List (Direction d)) : Set (Path d × Path d) :=
  (NoDrop ℓ 0 ×ˢ NoDrop ℓ 0) ∩ commonWordEvent ℓ 0 0 wv.1 wv.2

noncomputable def independentConditionedPairLaw {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) :
    Measure (Path d × Path d) := (conditionedLaw ν ℓ).prod (conditionedLaw ν ℓ)

open scoped Classical in
noncomputable def firstPairWord {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) :
    List (Direction d) × List (Direction d) :=
  if h : ∃ wv, P ∈ FirstPairWordEvent ℓ wv then h.choose else ([],[])

noncomputable def renewPairSuffix {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) :
    Path d × Path d :=
  ((fun j => P.1 ((firstPairWord ℓ P).1.length+j) - P.1 (firstPairWord ℓ P).1.length),
   (fun j => P.2 ((firstPairWord ℓ P).2.length+j) - P.2 (firstPairWord ℓ P).2.length))

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FixedPairSuffix
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

noncomputable def commonWords {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) (n : ℕ) :=
  firstPairWord ℓ ((renewPairSuffix ℓ)^[n] P)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWordIncrement
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

noncomputable def commonWordIncrement {d : ℕ} (e : Direction d)
    (wv : List (Direction d) × List (Direction d)) : ℝ :=
  wordCoordinate e wv.1-wordCoordinate e wv.2

lemma signedCoordinate_step_self {d : ℕ} (e : Direction d) :
    signedCoordinate e (step e) = 1 := by
  simp only [signedCoordinate,step,ite_true, if_true,Int.cast_ite,Int.cast_one,Int.cast_neg]
  cases e.2 <;> norm_num

noncomputable def truncatedVariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (r : ℝ) : ℝ := ∫ x, min ((S x)^2) (r^2) ∂μ
noncomputable def fluctuationScale {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (r : ℝ) : ℝ := r^2 / truncatedVariance μ S r

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SymmetricTruncate
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

noncomputable def commonIncrementProcess {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (n : ℕ) (P : Path d × Path d) : ℝ :=
  commonWordIncrement e (commonWords ℓ P n)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RecordIndexTime
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

noncomputable def recordIndexTime {d : ℕ} (ℓ : Vector d) (r : ℕ) (X : Path d) : ℕ := by
  classical
  exact if h : ∃ n, X ∈ RecordIndexPrefix ℓ r n then Nat.find h else 0

noncomputable def recordIndexPosition {d : ℕ} (ℓ : Vector d) (r : ℕ) (X : Path d) : Lattice d :=
  X (recordIndexTime ℓ r X)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_SignedHeight
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

def signedHeight {d : ℕ} (e : Direction d) (x : Lattice d) : ℤ :=
  if e.2 then x e.1 else -x e.1

lemma signedHeight_projection {d : ℕ} (e : Direction d) (x : Lattice d) :
    dot (realPosition x) (realPosition (step e)) = (signedHeight e x : ℝ) := by
  rw [dot_signed_direction]
  simp only [signedCoordinate,signedHeight,Int.cast_ite,Int.cast_neg]

lemma signedHeight_step_le {d : ℕ} (e : Direction d) (x : Lattice d) (f : Direction d) :
    signedHeight e (x+step f) ≤ signedHeight e x+1 := by
  simp only [signedHeight,Pi.add_apply,step]
  split <;> split <;> (try split) <;> omega

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GridOscillation
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

def ContinuousOscillation (ε δ : ℝ) : Set C(unitInterval,ℝ) :=
  {f | ∃ s t : unitInterval, dist s t ≤ δ ∧ ε < |f s-f t|}

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AlignedRecordPrefix
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

def AlignedRecordPrefix {d : ℕ} (ℓ : Vector d) (q : ℕ × ℕ) : Set (Path d × Path d) :=
  {P | (∃ r, 0 < r ∧ P.1 ∈ RecordIndexPrefix ℓ r q.1 ∧
    P.2 ∈ RecordIndexPrefix ℓ r q.2) ∧
    dot (realPosition (P.1 q.1)) ℓ = dot (realPosition (P.2 q.2)) ℓ}

def RecordOrZeroPrefix {d : ℕ} (ℓ : Vector d) (r n : ℕ) : Set (Path d) :=
  if r = 0 then {_X | n = 0} else RecordIndexPrefix ℓ r n

def BlockDecoration {Ω : Type*} (F B : ℕ → Ω → ℝ) (M b : ℕ) (z : ℝ) : Set Ω :=
  {ω | ∃ j ≤ M, z < |F (j*b) ω-B (j*b) ω|}

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_DirectBridge
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
namespace DirectionalTransience

lemma signedHeight_add_step_self {d : ℕ} (e : Direction d) (y : Lattice d) :
    signedHeight e (y+step e) = signedHeight e y+1 := by
  simp only [signedHeight,Pi.add_apply,step]
  cases e.2 <;> simp <;> ring

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CoordinateHitExact
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
namespace DirectionalTransience

lemma coordinate_hitAt_exact {d : ℕ} (e : Direction d) (x : Lattice d) (X : Path d)
    (h0 : X 0=x) (hnn : ∀ n, ∃ g, X (n+1)=X n+step g) (s n : ℕ)
    (hX : X ∈ HitAt (Strip (realPosition (step e)) x s) (Upper (realPosition (step e)) x s) n) :
    signedHeight e (X n) = signedHeight e x+s := by
  have hu : signedHeight e x+(s:ℤ) ≤ signedHeight e (X n) := by
    have hh := hX.1
    change dot (realPosition x) (realPosition (step e))+(s:ℝ) ≤ dot (realPosition (X n)) (realPosition (step e)) at hh
    simp only [signedHeight_projection] at hh
    exact_mod_cast hh
  cases n with
  | zero => rw [h0] at *; omega
  | succ n =>
    have hl : signedHeight e (X n) < signedHeight e x+(s:ℤ) := by
      have hh := (hX.2 n (Nat.lt_succ_self n)).2
      change dot (realPosition (X n)) (realPosition (step e)) < dot (realPosition x) (realPosition (step e))+(s:ℝ) at hh
      simp only [signedHeight_projection] at hh
      exact_mod_cast hh
    obtain ⟨g,hg⟩ := hnn n
    have hh := signedHeight_step_le e (X n) g
    rw [← hg] at hh
    omega

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FirstHighRecord
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
namespace DirectionalTransience

def AdmissibleHighWord {d : ℕ} (ℓ : Vector d) (J : ℝ) (w : List (Direction d)) : Prop :=
  StrictRecord ℓ (wordPath 0 w) w.length ∧
  J < dot (realPosition (wordPath 0 w w.length)) ℓ ∧
  (∀ j ≤ w.length, 0 ≤ dot (realPosition (wordPath 0 w j)) ℓ) ∧
  ∀ j < w.length, J < dot (realPosition (wordPath 0 w j)) ℓ →
    StrictRecord ℓ (wordPath 0 w) j →
      ∃ k, j < k ∧ k < w.length ∧ dot (realPosition (wordPath 0 w k)) ℓ <
        dot (realPosition (wordPath 0 w j)) ℓ

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_EndpointPrefix
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
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

def EndpointPrefix {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℕ)
    (A : Set (Lattice d)) : Set (Path d) := Hit (Strip ℓ x H) (Upper ℓ x H ∩ A)

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_HitWord
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
namespace DirectionalTransience

abbrev HitWord {d : ℕ} (x : Lattice d) (S T : Set (Lattice d)) :=
  {w : List (Direction d) // wordPath x w ∈ HitAt S T w.length}

lemma hitWord_prefix {d : ℕ} (x : Lattice d) (S T : Set (Lattice d))
    (w : HitWord x S T) {X : Path d} (hX : X ∈ wordCylinder x w.val) :
    X ∈ HitAt S T w.val.length := by
  exact ⟨by simpa only [hX _ le_rfl] using w.property.1,
    fun j hj => by simpa only [hX j hj.le] using w.property.2 j hj⟩

lemma hitWord_cylinders_disjoint {d : ℕ} (x : Lattice d) (S T : Set (Lattice d))
    (hST : Disjoint S T) :
    Pairwise (fun u v : HitWord x S T => Disjoint (wordCylinder x u.val) (wordCylinder x v.val)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro X hu hv
  by_cases he : u.val.length = v.val.length
  · exact huv (Subtype.ext (word_eq_of_cylinders x u.val v.val X hu hv he))
  · exact Set.disjoint_left.mp (hitAt_pairwise_disjoint hST he)
      (hitWord_prefix x S T u hu) (hitWord_prefix x S T v hv)

lemma hitWord_cover {d : ℕ} (x : Lattice d) (S T : Set (Lattice d))
    (X : Path d) (hx : X 0 = x)
    (hnn : ∀ n, ∃ e : Direction d, X (n+1) = X n + step e) :
    X ∈ Hit S T ↔ ∃ w : HitWord x S T, X ∈ wordCylinder x w.val := by
  constructor
  · intro hX
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
    obtain ⟨w,hw,hcy⟩ := exists_word_prefix X hnn n
    rw [hx] at hcy
    have hp : wordPath x w ∈ HitAt S T w.length := by
      rw [hw]
      exact ⟨by simpa only [← hcy n (by omega)] using hn.1,
        fun j hj => by simpa only [← hcy j (by omega)] using hn.2 j hj⟩
    exact ⟨⟨w,hp⟩,hcy⟩
  · rintro ⟨w,hw⟩
    exact Set.mem_iUnion.mpr ⟨w.val.length,hitWord_prefix x S T w hw⟩

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonLayer
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
namespace DirectionalTransience

def CommonLayer {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ) (H : ℤ) :
    Set (Path d × Path d) :=
  {P | ∃ a b, P.1 ∈ FirstLayerHit height H a ∧ P.2 ∈ FirstLayerHit height H b ∧
    P.1 ∈ FutureNoDrop ℓ a ∧ P.2 ∈ FutureNoDrop ℓ b}

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

def CurvePrefixAt {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s n : ℕ) : Set (Path d) :=
  HitAt (Strip ℓ x s) (Upper ℓ x s) n ∩
    {X | ∀ j ≤ s, ∃ a ≤ n,
      (fun k => X k-x) ∈ RecordOrZeroPrefix ℓ j a ∧
      |signedCoordinate f (X a-x)-b j| ≤ z}

def CurvePrefix {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) : Set (Path d) := ⋃ n, CurvePrefixAt ℓ f x b z s n

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicyMaximal
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

local instance CurvePolicyMaximalMs {d : ℕ} : MeasurableSpace (List (Lattice d)) := ⊤

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FinitePolicyFailure
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

local instance CurvePolicyFailureMs {d : ℕ} : MeasurableSpace (List (Lattice d)) := ⊤

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
local instance CurveActualFailureMs {d : ℕ} : MeasurableSpace (List (Lattice d)) := ⊤

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PolicyGoodMass
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
local instance CurvePolicyMeasurableMs {d : ℕ} : MeasurableSpace (List (Lattice d)) := ⊤

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_CurvePolicyTubeMass
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
local instance CurvePolicyTubeMassMs {d : ℕ} : MeasurableSpace (List (Lattice d)) := ⊤

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
local instance CurvePolicyTubeProbabilityMs {d : ℕ} : MeasurableSpace (List (Lattice d)) := ⊤

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonBoundaryRestart
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

def BoundaryAt {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d)
    (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧ CommonTrueRecord ℓ P n m ∧
    H ≤ dot (realPosition (P.1 n)) ℓ ∧
    ∀ j k, 0 < j → j < n → 0 < k → k < m →
      H ≤ dot (realPosition (P.1 j)) ℓ → ¬ CommonTrueRecord ℓ P j k

def AdmissibleBoundaryPrefix {d : ℕ} (ℓ : Vector d) (H : ℝ) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧
    dot (realPosition (f n)) ℓ = dot (realPosition (g m)) ℓ ∧
    StrictRecord ℓ f n ∧ StrictRecord ℓ g m ∧
    (∀ j ≤ n, dot (realPosition x) ℓ ≤ dot (realPosition (f j)) ℓ) ∧
    (∀ k ≤ m, dot (realPosition y) ℓ ≤ dot (realPosition (g k)) ℓ) ∧
    H ≤ dot (realPosition (f n)) ℓ ∧
    ∀ j k, 0 < j → j < n → 0 < k → k < m →
      H ≤ dot (realPosition (f j)) ℓ → StrictRecord ℓ f j → StrictRecord ℓ g k →
      dot (realPosition (f j)) ℓ = dot (realPosition (g k)) ℓ →
      (∃ a, j < a ∧ a < n ∧ dot (realPosition (f a)) ℓ < dot (realPosition (f j)) ℓ) ∨
      (∃ b, k < b ∧ b < m ∧ dot (realPosition (g b)) ℓ < dot (realPosition (g k)) ℓ)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_JointPastRestart
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

def BoundaryData (d : ℕ) := Σ q : ℕ × ℕ,
  (((i : Finset.Iic q.1) → Lattice d) × ((i : Finset.Iic q.2) → Lattice d))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SharedWordCylinderLower
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
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

lemma signedHeight_add_step_other {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1) (x : Lattice d) :
    signedHeight e (x+step f)=signedHeight e x := by
  simp [signedHeight,Pi.add_apply,step,hef]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SelectedBoundaryRestart
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

def BoundaryData.endpoints {d : ℕ} (F : BoundaryData d) : Lattice d × Lattice d :=
  (extendPrefix F.1.1 F.2.1 F.1.1,extendPrefix F.1.2 F.2.2 F.1.2)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CommonCutCounting
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

def BoundedCommonGaps {d : ℕ} (e f : Direction d) (R : ℝ) (H : ℕ)
    (P : Path d × Path d) : Prop :=
  ∀ j < H, ∀ n m,
    P.1 ∈ FirstLayerHit (signedHeight e) (signedHeight e (P.1 0)+j) n →
    P.2 ∈ FirstLayerHit (signedHeight e) (signedHeight e (P.1 0)+j) m →
    P.1 ∈ FutureNoDrop (realPosition (step e)) n →
    P.2 ∈ FutureNoDrop (realPosition (step e)) m →
    |signedCoordinate f (P.1 n-P.2 m)| < R

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RawPairEndpoint
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

noncomputable def prefixEndpoint {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (H : ℕ) (X : Path d) : Lattice d :=
  x + recordIndexPosition ℓ H (fun j => X j-x)

def PairEndpointEvent {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x y : Lattice d) (H : ℕ) (z : ℝ) : Set (Path d × Path d) :=
  {p | p.1 ∈ Hit (Strip ℓ x H) (Upper ℓ x H) ∧
    p.2 ∈ Hit (Strip ℓ y H) (Upper ℓ y H) ∧
    z ≤ signedCoordinate f (prefixEndpoint ℓ y H p.2-prefixEndpoint ℓ x H p.1)}

noncomputable def rawPairEndpointMass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) : ℝ :=
  ∫ x, ((quenchedKernel (ω,x.1)).prod (quenchedKernel (ω,x.2))).real
    (PairEndpointEvent ℓ f x.1 x.2 H z) ∂π

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_RawPairKernel
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

noncomputable def rawPairEndpointLaw {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d × Lattice d) : Measure (Lattice d × Lattice d) :=
  (hitKernel (Strip ℓ x.1 H) (Upper ℓ x.1 H) (ω,x.1)).prod
    (hitKernel (Strip ℓ x.2 H) (Upper ℓ x.2 H) (ω,x.2))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RawPairLocality
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

noncomputable def variableHitKernel {d : ℕ} (ℓ : Vector d) (H : ℕ) :
    Kernel (Environment d × Lattice d) (Lattice d) where
  toFun p := hitKernel (Strip ℓ p.2 H) (Upper ℓ p.2 H) p
  measurable' := measurable_from_prod_countable_left fun x =>
    (hitKernel (Strip ℓ x H) (Upper ℓ x H)).measurable.comp (measurable_id.prodMk measurable_const)

instance variableHitKernel_finite {d : ℕ} (ℓ : Vector d) (H : ℕ) :
    IsFiniteKernel (variableHitKernel ℓ H) where
  exists_univ_le := by
    refine ⟨1,ENNReal.one_lt_top,fun p => ?_⟩
    change hitKernel (Strip ℓ p.2 H) (Upper ℓ p.2 H) p Set.univ ≤ 1
    exact hitKernel_total_le_one (disjoint_strip_upper ℓ p.2 H) p

noncomputable def pairKernelMass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) : ℝ≥0∞ :=
  ∫⁻ x, rawPairEndpointLaw ℓ H ω x {y | z ≤ signedCoordinate f (y.2-y.1)} ∂π

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

abbrev SupportedPairMeasures {d : ℕ} (C : Set (Lattice d × Lattice d)) :=
  {π : Measure (Lattice d × Lattice d) // π Cᶜ = 0}

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstHitUpward
attribute [-instance] _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma coordinate_hitKernel_supported {d : ℕ} (e : Direction d) (x : Lattice d)
    (H : ℕ) (ω : Environment d) :
    ∀ᵐ y ∂hitKernel (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) (ω,x),
      signedHeight e y = signedHeight e x+H := by
  rw [ae_iff,hitKernel_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  intro hbad
  have hh : X ∈ HitAt (Strip (realPosition (step e)) x H)
      (Upper (realPosition (step e)) x H) n := ⟨hbad.1.1,hbad.2⟩
  exact hbad.1.2 (coordinate_hitAt_exact e x X h0 hnn H n hh)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TupleEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience
namespace TupleKernel

lemma measurable_countable_measure {A Ω : Type*} [MeasurableSpace A]
    [MeasurableSpace Ω] [Countable A] [MeasurableSingletonClass A]
    (μ : Ω → Measure A) (h : ∀ x, Measurable (fun ω => μ ω {x})) : Measurable μ := by
  have he (ω) : μ ω = Measure.sum (fun x => μ ω {x} • Measure.dirac x) :=
    (Measure.sum_smul_dirac _).symm
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hf : (fun ω => μ ω s) = (fun ω => ∑' x, μ ω {x} * Measure.dirac x s) := by
    funext ω
    conv_lhs => rw [he ω]
    simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
  rw [hf]
  exact Measurable.tsum fun x => (h x).mul_const _

end TupleKernel

noncomputable def rawTupleEndpointLaw {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) : Measure (Fin k → Lattice d) :=
  Measure.pi (fun j => variableHitKernel ℓ H (ω,x j))

lemma rawTupleEndpointLaw_singleton {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x y : Fin k → Lattice d) :
    rawTupleEndpointLaw ℓ H ω x {y} = ∏ j, variableHitKernel ℓ H (ω,x j) {y j} := by
  exact Measure.pi_singleton _ _

lemma rawTupleEndpointLaw_le_one {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) :
    rawTupleEndpointLaw ℓ H ω x Set.univ ≤ 1 := by
  rw [rawTupleEndpointLaw,Measure.pi_univ]
  exact Finset.prod_le_one' fun j _ =>
    hitKernel_total_le_one (disjoint_strip_upper ℓ (x j) H) (ω,x j)

noncomputable def rawTupleMixture {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) : Measure (Fin k → Lattice d) :=
  π.bind (rawTupleEndpointLaw ℓ H ω)

lemma rawTupleMixture_apply {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) (A : Set (Fin k → Lattice d)) :
    rawTupleMixture ℓ H π ω A = ∫⁻ x, rawTupleEndpointLaw ℓ H ω x A ∂π := by
  exact Measure.bind_apply (Set.to_countable _).measurableSet (measurable_of_countable _).aemeasurable

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SuccessfulWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def hitWordEvent {d : ℕ} (x : Lattice d) (S T : Set (Lattice d))
    (E : Set (HitWord x S T)) : Set (Path d) :=
  ⋃ w : E, wordCylinder x w.val.val

lemma hitWordEvent_mass {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) (E : Set (HitWord x S T)) :
    quenchedKernel (ω,x) (hitWordEvent x S T E) =
      ∑' w : E, ENNReal.ofReal (wordWeight ω x w.val.val) := by
  rw [hitWordEvent,measure_iUnion]
  · congr 1; funext w; exact quenched_wordCylinder ω x w.val.val
  · intro u v huv
    exact hitWord_cylinders_disjoint x S T hST (fun h => huv (Subtype.ext h))
  · exact fun w => measurableSet_wordCylinder x w.val.val

noncomputable def successfulWordLaw {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) : Measure (HitWord x S T) :=
  Measure.sum (fun w => ENNReal.ofReal (wordWeight ω x w.val) • Measure.dirac w)

lemma successfulWordLaw_apply {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (E : Set (HitWord x S T)) :
    successfulWordLaw ω x S T E = ∑' w : E, ENNReal.ofReal (wordWeight ω x w.val.val) := by
  rw [successfulWordLaw,Measure.sum_apply_of_countable]
  simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ (Set.to_countable E).measurableSet]
  calc
    _ = ∑' w, E.indicator (fun w => ENNReal.ofReal (wordWeight ω x w.val)) w := by
      congr 1
      funext w
      by_cases hw : w ∈ E <;> simp [hw]
    _ = _ := (tsum_subtype E (fun w => ENNReal.ofReal (wordWeight ω x w.val))).symm

lemma successfulWordLaw_event {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) (E : Set (HitWord x S T)) :
    successfulWordLaw ω x S T E = quenchedKernel (ω,x) (hitWordEvent x S T E) := by
  rw [successfulWordLaw_apply,hitWordEvent_mass ω x S T hST]

lemma successfulWordLaw_endpoint {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) :
    (successfulWordLaw ω x S T).map (fun w => wordPath x w.val w.val.length) =
      hitKernel S T (ω,x) := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_of_countable _) hA,
    successfulWordLaw_event ω x S T hST,hitKernel_apply_eq_hit hST]
  apply measure_congr
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  apply propext
  constructor
  · intro hx
    obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hx
    have hp := hitWord_prefix x S T w.val hw
    exact Set.mem_iUnion.mpr ⟨w.val.val.length,⟨⟨hp.1,by
      rw [hw _ le_rfl]
      exact w.property⟩,hp.2⟩⟩
  · intro hx
    have hhit : X ∈ Hit S T := by
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨n,hn.1.1,hn.2⟩
    obtain ⟨w,hw⟩ := (hitWord_cover x S T X h0 hnn).mp hhit
    have hp := hitWord_prefix x S T w hw
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
    have hn' : X ∈ HitAt S T n := ⟨hn.1.1,hn.2⟩
    have he : n = w.val.length := by
      by_contra hne
      exact Set.disjoint_left.mp (hitAt_pairwise_disjoint hST hne) hn' hp
    have hwA : wordPath x w.val w.val.length ∈ A := by
      simpa only [he,hw _ le_rfl] using hn.1.2
    exact Set.mem_iUnion.mpr ⟨⟨w,hwA⟩,hw⟩

lemma successfulWordLaw_singleton {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (w : HitWord x S T) :
    successfulWordLaw ω x S T {w} = ENNReal.ofReal (wordWeight ω x w.val) := by
  rw [successfulWordLaw_apply,tsum_subtype {w} (fun v => ENNReal.ofReal (wordWeight ω x v.val))]
  simp

noncomputable def rawWordLaw {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d) : Measure (List (Direction d)) :=
  (successfulWordLaw ω x (Strip ℓ x H) (Upper ℓ x H)).map Subtype.val

lemma rawWordLaw_singleton {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d) (w : List (Direction d)) :
    rawWordLaw ℓ H ω x {w} =
      if wordPath x w ∈ HitAt (Strip ℓ x H) (Upper ℓ x H) w.length
      then ENNReal.ofReal (wordWeight ω x w) else 0 := by
  rw [rawWordLaw,Measure.map_apply measurable_subtype_coe (measurableSet_singleton _)]
  split_ifs with hw
  · have he : Subtype.val ⁻¹' {w} = ({⟨w,hw⟩} : Set (HitWord x (Strip ℓ x H) (Upper ℓ x H))) := by
      ext v
      simp only [Set.mem_preimage,Set.mem_singleton_iff,Subtype.ext_iff]
    rw [he,successfulWordLaw_singleton]
  · have he : Subtype.val ⁻¹' {w} = (∅ : Set (HitWord x (Strip ℓ x H) (Upper ℓ x H))) := by
      ext v
      simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
      intro hv
      exact hw (hv ▸ v.property)
    rw [he,measure_empty]

lemma rawWordLaw_endpoint {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d) :
    (rawWordLaw ℓ H ω x).map (fun w => wordPath x w w.length) = variableHitKernel ℓ H (ω,x) := by
  rw [rawWordLaw,Measure.map_map (measurable_of_countable _) measurable_subtype_coe]
  exact successfulWordLaw_endpoint ω x _ _ (disjoint_strip_upper _ _ _)

lemma measurable_rawWordLaw_rows {d : ℕ} (ℓ : Vector d) (H : ℕ) (x : Lattice d) :
    @Measurable _ _ (rowSigma (Strip ℓ x H)) _ (rawWordLaw ℓ H · x) := by
  let : MeasurableSpace (Environment d) := rowSigma (Strip ℓ x H)
  apply TupleKernel.measurable_countable_measure
  intro w
  simp_rw [rawWordLaw_singleton]
  by_cases hw : wordPath x w ∈ HitAt (Strip ℓ x H) (Upper ℓ x H) w.length
  · simp only [ite_eq_left hw]
    apply Measurable.ennreal_ofReal
    exact measurable_wordWeight_on x w fun y hy => by
      obtain ⟨n,hn,he⟩ := (wordDepartures_mem_iff x y w).mp hy
      rw [he]
      exact hw.2 n hn
  · simp only [ite_eq_right hw]
    exact measurable_const

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_FiniteWordGeometry
attribute [-instance] _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def wordFirstHitTime {d : ℕ} (e : Direction d) (x : Lattice d)
    (s : ℕ) (w : List (Direction d)) : ℕ :=
  if h : ∃ n, signedHeight e x+s ≤ signedHeight e (wordPath x w n) then Nat.find h else 0

noncomputable def wordFirstHitPosition {d : ℕ} (e : Direction d) (x : Lattice d)
    (s : ℕ) (w : List (Direction d)) : Lattice d :=
  wordPath x w (wordFirstHitTime e x s w)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordConcatenation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

abbrev CoordinateWord {d : ℕ} (e : Direction d) (x : Lattice d) (H : ℕ) :=
  HitWord x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H)

def ValidWordSplit {d : ℕ} (e : Direction d) (x : Lattice d) (h m : ℕ)
    (p : List (Direction d) × List (Direction d)) : Prop :=
  wordPath x p.1 ∈ HitAt (Strip (realPosition (step e)) x h)
    (Upper (realPosition (step e)) x h) p.1.length ∧
  wordPath (wordPath x p.1 p.1.length) p.2 ∈ HitAt
    (Strip (realPosition (step e)) (wordPath x p.1 p.1.length) m)
    (Upper (realPosition (step e)) (wordPath x p.1 p.1.length) m) p.2.length

abbrev CoordinateSplit {d : ℕ} (e : Direction d) (x : Lattice d) (h m : ℕ) :=
  {p : List (Direction d) × List (Direction d) // ValidWordSplit e x h m p}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RelativeBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def relativeWordDisplacement {d : ℕ} (e f : Direction d) (x : Lattice d)
    (s : ℕ) (w : List (Direction d)) : ℝ :=
  signedCoordinate f (wordFirstHitPosition e x s w - x)

def TupleSeparated {d k : ℕ} (f : Direction d) (G : ℝ) (x : Fin k → Lattice d) : Prop :=
  ∀ i j, i ≠ j → G ≤ |signedCoordinate f (x i) - signedCoordinate f (x j)|

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetClipping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

def CentralWordBudget {d : ℕ} (e f : Direction d) (x : Lattice d)
    (H : ℕ) (θ z : ℝ) (w : List (Direction d)) : Prop :=
  ∀ s ≤ H, |relativeWordDisplacement e f x s w-(s:ℝ)*θ| ≤ z

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferFirstFailure
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

def BelowHeight {d : ℕ} (ℓ : Vector d) (a : ℝ) : Set (Lattice d) :=
  {y | dot (realPosition y) ℓ < a}

def PairAtHeight {d : ℕ} (ℓ : Vector d) (a : ℝ) : Set (Lattice d × Lattice d) :=
  {x | dot (realPosition x.1) ℓ = a ∧ dot (realPosition x.2) ℓ = a}

noncomputable def rowHeightFiltration {d : ℕ} (ℓ : Vector d) (a : ℝ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Environment d)) where
  seq n := rowSigma (BelowHeight ℓ (a+n))
  mono' := by
    intro n m hnm
    apply rowSigma_mono
    intro y hy
    have hnmR : (n:ℝ) ≤ m := by exact_mod_cast hnm
    dsimp [BelowHeight] at hy ⊢
    linarith
  le' n := rowSigma_le _

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetAdapted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

abbrev SupportedTupleMeasures {d k : ℕ} (C : Set (Fin k → Lattice d)) :=
  {π : Measure (Fin k → Lattice d) // π Cᶜ = 0}

lemma supportedTupleMeasures_singleton {d k : ℕ} (C : Set (Fin k → Lattice d))
    (π : SupportedTupleMeasures C) {x : Fin k → Lattice d} (hx : x ∉ C) : π.val {x} = 0 := by
  apply le_antisymm _ bot_le
  calc
    π.val {x} ≤ π.val Cᶜ := measure_mono (Set.singleton_subset_iff.mpr hx)
    _ = 0 := π.property

def TupleAtHeight {d k : ℕ} (ℓ : Vector d) (a : ℝ) : Set (Fin k → Lattice d) :=
  {x | ∀ j, dot (realPosition (x j)) ℓ = a}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma TupleKernel.countable_bind_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (K : A → Measure B) (P : B → Prop)
    (hP : ∀ᵐ a ∂μ, ∀ᵐ b ∂K a, P b) : ∀ᵐ b ∂μ.bind K, P b := by
  rw [ae_iff,Measure.bind_apply (Set.to_countable _).measurableSet (measurable_of_countable _).aemeasurable]
  have he : (fun a => K a {b | ¬ P b}) =ᵐ[μ] fun _ => 0 := hP.mono fun a ha => ae_iff.mp ha
  rw [lintegral_congr_ae he,lintegral_zero]

lemma tupleSeparated_mono {d k : ℕ} (f : Direction d) {G g : ℝ} (h : g ≤ G)
    (x : Fin k → Lattice d) (hx : TupleSeparated f G x) : TupleSeparated f g x :=
  fun i j hij => h.trans (hx i j hij)

lemma tupleSeparated_coordinate {d k : ℕ} (f : Direction d) (G : ℕ) (x : Fin k → Lattice d) :
    TupleSeparated f (G:ℝ) x ↔ Pairwise fun i j => (G:ℤ) ≤ |x i f.1-x j f.1| := by
  have he (i j) : |signedCoordinate f (x i)-signedCoordinate f (x j)| = (|x i f.1-x j f.1|:ℤ) := by
    rw [Int.cast_abs,Int.cast_sub]
    simp only [signedCoordinate]
    split
    · rfl
    · rw [show -(x i f.1:ℝ)- -(x j f.1:ℝ) = -((x i f.1:ℝ)-(x j f.1:ℝ)) by ring, abs_neg]
  simp only [TupleSeparated,Pairwise,he]
  norm_cast

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def normalizeOr {α : Type*} [MeasurableSpace α] (μ ρ : Measure α) : Measure α :=
  if μ Set.univ = 0 then ρ else normalizedMeasure μ

lemma normalizeOr_probability {α : Type*} [MeasurableSpace α] (μ ρ : Measure α)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ρ] : IsProbabilityMeasure (normalizeOr μ ρ) := by
  by_cases h : μ Set.univ=0
  · simpa only [normalizeOr,ite_eq_left h] using (inferInstance : IsProbabilityMeasure ρ)
  · simpa only [normalizeOr,ite_eq_right h] using normalizedMeasure_probability μ h

lemma normalizeOr_ae {α : Type*} [MeasurableSpace α] (μ ρ : Measure α) (P : α → Prop)
    (hμ : ∀ᵐ x ∂μ, P x) (hρ : ∀ᵐ x ∂ρ, P x) : ∀ᵐ x ∂normalizeOr μ ρ, P x := by
  unfold normalizeOr
  split
  · exact hρ
  · exact Measure.ae_smul_measure hμ _

lemma measurable_normalizeOr {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ ρ : Ω → Measure α) (hμ : Measurable μ) (hρ : Measurable ρ) :
    Measurable (fun ω => normalizeOr (μ ω) (ρ ω)) := by
  unfold normalizeOr normalizedMeasure
  apply Measurable.ite (measurableSet_eq_fun ((Measure.measurable_coe MeasurableSet.univ).comp hμ) measurable_const) hρ
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [Measure.smul_apply,smul_eq_mul]
  exact (((Measure.measurable_coe MeasurableSet.univ).comp hμ).inv).mul
    ((Measure.measurable_coe hU).comp hμ)

abbrev BudgetProfile {d k : ℕ} (e f : Direction d) (a G : ℝ) :=
  {π : Measure (Fin k → Lattice d) // IsProbabilityMeasure π ∧
    ∀ᵐ x ∂π, x ∈ TupleAtHeight (realPosition (step e)) a ∧ TupleSeparated f G x}

def BudgetProfile.toSupported {d k : ℕ} {e f : Direction d} {a G : ℝ}
    (π : BudgetProfile (k:=k) e f a G) : SupportedTupleMeasures (TupleAtHeight (k:=k) (realPosition (step e)) a) :=
  ⟨π.val,ae_iff.mp (π.property.2.mono fun _ h => h.1)⟩

def tupleShiftUp {d k : ℕ} (e : Direction d) (H : ℕ) (x : Fin k → Lattice d) : Fin k → Lattice d :=
  fun j => x j + H • step e

lemma tupleShiftUp_support {d k : ℕ} (e f : Direction d) (H : ℕ) (a G : ℝ)
    (x : Fin k → Lattice d) (hx : x ∈ TupleAtHeight (realPosition (step e)) a ∧ TupleSeparated f G x) :
    tupleShiftUp e H x ∈ TupleAtHeight (realPosition (step e)) (a+H) ∧
      TupleSeparated f G (tupleShiftUp e H x) := by
  have hs (g : Direction d) (y : Lattice d) : signedCoordinate g (y+H • step e) =
      signedCoordinate g y + (H:ℝ)*signedCoordinate g (step e) := by
    simp only [signedCoordinate,Pi.add_apply,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply,Int.cast_add,Int.cast_mul,Int.cast_natCast]
    split <;> ring
  constructor
  · intro j
    change dot (realPosition (x j+H • step e)) (realPosition (step e))=a+H
    rw [dot_signed_direction,hs,signedCoordinate_step_self,mul_one,← dot_signed_direction,hx.1 j]
  · intro i j hij
    change G ≤ |signedCoordinate f (x i+H • step e)-signedCoordinate f (x j+H • step e)|
    rw [hs,hs,add_sub_add_right_eq_sub]
    exact hx.2 i j hij

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma rawTupleEndpointLaw_rows {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (x : Fin k → Lattice d) (S : Set (Lattice d)) (hS : ∀ j, Strip ℓ (x j) H⊆S) :
    @Measurable _ _ (rowSigma S) _ (fun ω => rawTupleEndpointLaw ℓ H ω x) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  apply TupleKernel.measurable_countable_measure
  intro y
  simp only [rawTupleEndpointLaw_singleton]
  apply Finset.measurable_prod
  intro j _
  have he : (fun ω => variableHitKernel ℓ H (ω,x j)) = fun ω =>
      (rawWordLaw ℓ H ω (x j)).map (fun w => wordPath (x j) w w.length) := by
    funext ω; exact (rawWordLaw_endpoint ℓ H ω (x j)).symm
  have hm : Measurable (fun ω => variableHitKernel ℓ H (ω,x j)) := by
    rw [he]
    exact (Measure.measurable_map _ (measurable_of_countable _)).comp
      ((measurable_rawWordLaw_rows ℓ H (x j)).mono (rowSigma_mono (hS j)) le_rfl)
  exact (Measure.measurable_coe (measurableSet_singleton _)).comp hm

lemma rawTupleMixture_joint_rows {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (C : Set (Fin k → Lattice d)) (S : Set (Lattice d))
    (hS : ∀ x∈C, ∀ j, Strip ℓ (x j) H⊆S) :
    @Measurable (SupportedTupleMeasures C×Environment d) (Measure (Fin k → Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => rawTupleMixture ℓ H p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  apply Measure.measurable_of_measurable_coe
  intro U _
  simp only [rawTupleMixture_apply,lintegral_countable']
  apply Measurable.tsum
  intro x
  by_cases hx : x∈C
  · exact (((Measure.measurable_coe (Set.to_countable _).measurableSet).comp
      (rawTupleEndpointLaw_rows ℓ H x S (hS x hx))).comp measurable_snd).mul
        ((Measure.measurable_coe (measurableSet_singleton x)).comp (measurable_subtype_coe.comp measurable_fst))
  · simp only [supportedTupleMeasures_singleton C _ hx,mul_zero]
    exact measurable_const

lemma rawTupleEndpointLaw_support {d k : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) (a : ℝ)
    (hx : x∈TupleAtHeight (realPosition (step e)) a) :
    ∀ᵐ y ∂rawTupleEndpointLaw (realPosition (step e)) H ω x,
      y∈TupleAtHeight (realPosition (step e)) (a+H) := by
  apply ae_all_iff.mpr
  intro j
  have hs := (Measure.tendsto_eval_ae_ae (μ:=fun j : Fin k => variableHitKernel (realPosition (step e)) H (ω,x j)) (i:=j)).eventually (coordinate_hitKernel_supported e (x j) H ω)
  apply hs.mono
  intro y hy
  rw [signedHeight_projection,hy,Int.cast_add,Int.cast_natCast,← signedHeight_projection,hx j]

lemma rawTupleMixture_support {d k : ℕ} (e : Direction d) (H : ℕ) (a : ℝ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d)
    (hπ : ∀ᵐ x ∂π, x∈TupleAtHeight (realPosition (step e)) a) :
    ∀ᵐ y ∂rawTupleMixture (realPosition (step e)) H π ω,
      y∈TupleAtHeight (realPosition (step e)) (a+H) := by
  apply TupleKernel.countable_bind_ae
  exact hπ.mono fun x hx => rawTupleEndpointLaw_support e H ω x a hx

lemma rawTupleMixture_univ_le {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    rawTupleMixture ℓ H π ω Set.univ≤π Set.univ := by
  rw [rawTupleMixture_apply]
  exact (lintegral_mono fun x => rawTupleEndpointLaw_le_one ℓ H ω x).trans_eq (by simp)

instance rawTupleMixture_finite {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (π : Measure (Fin k → Lattice d)) [IsFiniteMeasure π] (ω : Environment d) :
    IsFiniteMeasure (rawTupleMixture ℓ H π ω) :=
  ⟨lt_of_le_of_lt (rawTupleMixture_univ_le ℓ H π ω) (measure_lt_top _ _)⟩

abbrev LayerTupleProfile {d k : ℕ} (e : Direction d) (a : ℝ) :=
  {π : Measure (Fin k → Lattice d) // IsProbabilityMeasure π ∧
    ∀ᵐ x ∂π, x∈TupleAtHeight (realPosition (step e)) a}

instance layerTupleProfile_probability {d k : ℕ} (e : Direction d) (a : ℝ)
    (π : LayerTupleProfile (k:=k) e a) : IsProbabilityMeasure π.val := π.property.1

def LayerTupleProfile.toSupported {d k : ℕ} {e : Direction d} {a : ℝ}
    (π : LayerTupleProfile (k:=k) e a) : SupportedTupleMeasures (TupleAtHeight (k:=k) (realPosition (step e)) a) :=
  ⟨π.val,ae_iff.mp π.property.2⟩

lemma LayerTupleProfile.measurable_toSupported {d k : ℕ} (e : Direction d) (a : ℝ) :
    Measurable (LayerTupleProfile.toSupported (k:=k) (e:=e) (a:=a)) := measurable_subtype_coe.subtype_mk

def BudgetProfile.toLayerProfile {d k : ℕ} {e f : Direction d} {a G : ℝ}
    (π : BudgetProfile (k:=k) e f a G) : LayerTupleProfile (k:=k) e a :=
  ⟨π.val,π.property.1,π.property.2.mono fun _ h => h.1⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_StageSeedProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

def separateTuple {d k : ℕ} (f : Direction d) (M : ℕ) (x : Fin k → Lattice d) : Fin k → Lattice d :=
  fun j => Function.update (x j) f.1 ((j:ℕ)*M)

lemma separateTuple_separated {d k : ℕ} (f : Direction d) (M : ℕ) (x : Fin k → Lattice d) :
    TupleSeparated f (M:ℝ) (separateTuple f M x) := by
  rw [tupleSeparated_coordinate]
  intro i j hij
  simp only [separateTuple,Function.update_self]
  have hn : (i:ℤ)≠(j:ℤ) := by exact_mod_cast (Fin.val_ne_of_ne hij)
  have hh : (1:ℤ)≤|(i:ℤ)-(j:ℤ)| := Int.one_le_abs (sub_ne_zero.mpr hn)
  rw [← sub_mul,abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
  nlinarith [Int.natCast_nonneg M]

lemma separateTuple_height {d k : ℕ} (e f : Direction d) (hef : e.1≠f.1)
    (M : ℕ) (a : ℝ) (x : Fin k → Lattice d) (hx : x∈TupleAtHeight (realPosition (step e)) a) :
    separateTuple f M x∈TupleAtHeight (realPosition (step e)) a := by
  intro j
  rw [dot_signed_direction]
  simpa only [signedCoordinate,separateTuple,Function.update_of_ne hef] using
    (show signedCoordinate e (x j)=a by simpa only [dot_signed_direction] using hx j)

noncomputable def seedSeparatedRaw {d k : ℕ} (e f : Direction d) (H : ℕ) (G : ℝ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) : Measure (Fin k → Lattice d) :=
  (rawTupleMixture (realPosition (step e)) H π ω).restrict {y | TupleSeparated f G y}

instance seedSeparatedRaw_finite {d k : ℕ} (e f : Direction d) (H : ℕ) (G : ℝ)
    (π : Measure (Fin k → Lattice d)) [IsFiniteMeasure π] (ω : Environment d) :
    IsFiniteMeasure (seedSeparatedRaw e f H G π ω) := by unfold seedSeparatedRaw; infer_instance

lemma seedSeparatedRaw_support {d k : ℕ} (e f : Direction d) (H : ℕ) (G a : ℝ)
    (π : LayerTupleProfile (k:=k) e a) (ω : Environment d) :
    ∀ᵐ y ∂seedSeparatedRaw e f H G π.val ω,
      y∈TupleAtHeight (realPosition (step e)) (a+H) ∧ TupleSeparated f G y := by
  exact (ae_restrict_of_ae (rawTupleMixture_support e H a π.val ω π.property.2)).and
    (ae_restrict_mem ((Set.to_countable _).measurableSet))

noncomputable def seedSeparatedProfile {d k : ℕ} (e f : Direction d) (hef : e.1≠f.1)
    (a G : ℝ) (H : ℕ) (π : LayerTupleProfile (k:=k) e a) (ω : Environment d) :
    BudgetProfile (k:=k) e f (a+H) G := by
  let M : ℕ := Nat.ceil (max G 0)+1
  let μ := seedSeparatedRaw e f H G π.val ω
  let ρ := π.val.map (fun x => separateTuple f M (tupleShiftUp e H x))
  have : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).2 inferInstance
  refine ⟨normalizeOr μ ρ,normalizeOr_probability μ ρ,?_⟩
  apply normalizeOr_ae
  · exact seedSeparatedRaw_support e f H G a π ω
  · rw [ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
    apply π.property.2.mono
    intro x hx
    have hg : TupleSeparated e 0 x := fun _ _ _ => abs_nonneg _
    have hM : G≤(M:ℝ) := by
      have hh := Nat.le_ceil (max G 0)
      dsimp [M]; push_cast <;> linarith [le_max_left G 0]
    exact ⟨separateTuple_height e f hef M _ _ (tupleShiftUp_support e e H a 0 x ⟨hx,hg⟩).1,
      tupleSeparated_mono f hM _ (separateTuple_separated f M _)⟩

lemma seedSeparatedRaw_joint_rows {d k : ℕ} (e f : Direction d) (H : ℕ) (G a : ℝ)
    (S : Set (Lattice d)) (hS : ∀ x∈TupleAtHeight (k:=k) (realPosition (step e)) a,
      ∀ j, Strip (realPosition (step e)) (x j) H⊆S) :
    @Measurable (LayerTupleProfile (k:=k) e a×Environment d) (Measure (Fin k → Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => seedSeparatedRaw e f H G p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  have hm := (rawTupleMixture_joint_rows _ H _ S hS).comp
    (((LayerTupleProfile.measurable_toSupported e a).comp measurable_fst).prodMk measurable_snd)
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [seedSeparatedRaw,Measure.restrict_apply hU]
  exact (Measure.measurable_coe ((Set.to_countable _).measurableSet)).comp hm

lemma seedSeparatedProfile_measurable {d k : ℕ} (e f : Direction d) (hef : e.1≠f.1)
    (a G : ℝ) (H : ℕ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+H))) _
      (fun ω => seedSeparatedProfile e f hef a G H (π ω) ω) := by
  have hle : rowSigma (BelowHeight (realPosition (step e)) a) ≤ rowSigma (BelowHeight (realPosition (step e)) (a+H)) :=
    rowSigma_mono (by
      intro x hx
      change dot (realPosition x) (realPosition (step e)) < a+H
      exact lt_of_lt_of_le hx (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  let : MeasurableSpace (Environment d) := rowSigma (BelowHeight (realPosition (step e)) (a+H))
  apply Measurable.subtype_mk
  apply measurable_normalizeOr
  · apply (seedSeparatedRaw_joint_rows e f H G a _ ?_).comp ((hπ.mono hle le_rfl).prodMk measurable_id)
    intro x hx j y hy
    change dot (realPosition y) (realPosition (step e))<a+H
    simpa only [hx j] using hy.2
  · exact (Measure.measurable_map _ (measurable_of_countable _)).comp (measurable_subtype_coe.comp (hπ.mono hle le_rfl))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_EntropyVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience.Entropy

variable {X : Type*} [MeasurableSpace X]

theorem entropy_test_le (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hkl : klDiv μ ν ≠ ∞)
    (F : X → ℝ) (hFμ : Integrable F μ)
    (he : Integrable (fun x => Real.exp (F x)) ν) :
    (∫ x, F x ∂μ) - Real.log (∫ x, Real.exp (F x) ∂ν) ≤
      (klDiv μ ν).toReal := by
  obtain ⟨hac,hllr⟩ := klDiv_ne_top_iff.mp hkl
  have hac' : μ ≪ ν.tilted F := hac.trans (absolutelyContinuous_tilted he)
  have hh := integrable_llr_tilted_right hac hFμ hllr he
  have hnon := integral_llr_add_sub_measure_univ_nonneg hac' hh
  have : IsProbabilityMeasure (ν.tilted F) := isProbabilityMeasure_tilted he
  rw [probReal_univ,probReal_univ,add_sub_cancel_right] at hnon
  rw [integral_llr_tilted_right hac hFμ he hllr] at hnon
  rw [toReal_klDiv_of_measure_eq hac (by simp)]
  linarith

theorem entropy_exp_test_le (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hkl : klDiv μ ν ≠ ∞)
    (F : X → ℝ) (hFμ : Integrable F μ)
    (he : Integrable (fun x => Real.exp (F x)) ν) :
    (∫ x, F x ∂μ) - (∫ x, Real.exp (F x) ∂ν) + 1 ≤
      (klDiv μ ν).toReal := by
  have h := entropy_test_le μ ν hkl F hFμ he
  have hp : 0 < ∫ x, Real.exp (F x) ∂ν := integral_exp_pos he
  have hl := Real.log_le_sub_one_of_pos hp
  linarith

def ExpBudget (μ ν : Measure X) (C : ℝ) : Prop :=
  ∀ F : X → ℝ, Measurable F → (∃ B : ℝ, ∀ x, |F x| ≤ B) →
    (∫ x, F x ∂μ) - (∫ x, Real.exp (F x) ∂ν) + 1 ≤ C

lemma integrable_of_bounded {μ : Measure X} [IsFiniteMeasure μ] {F : X → ℝ}
    (hF : Measurable F) (hB : ∃ B : ℝ, ∀ x, |F x| ≤ B) : Integrable F μ := by
  obtain ⟨B,hB⟩ := hB
  exact (integrable_const B).mono' hF.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hB x)

lemma exp_integrable_of_bounded {μ : Measure X} [IsFiniteMeasure μ] {F : X → ℝ}
    (hF : Measurable F) (hB : ∃ B : ℝ, ∀ x, |F x| ≤ B) :
    Integrable (fun x => Real.exp (F x)) μ := by
  obtain ⟨B,hB⟩ := hB
  exact (integrable_const (Real.exp B)).mono' hF.exp.aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB x)))

lemma expBudget_of_kl_le (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ} (hC : 0 ≤ C) (hkl : klDiv μ ν ≤ ENNReal.ofReal C) :
    ExpBudget μ ν C := by
  intro F hF hB
  have hf : klDiv μ ν ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  exact (entropy_exp_test_le μ ν hf F (integrable_of_bounded hF hB)
    (exp_integrable_of_bounded hF hB)).trans (ENNReal.toReal_le_of_le_ofReal hC hkl)

lemma integrable_of_bounded_truncated_integrals (μ : Measure X) [IsFiniteMeasure μ]
    (F : X → ℝ) (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (C : ℝ) (hbound : ∀ n : ℕ, (∫ x, min (n:ℝ) (F x) ∂μ) ≤ C) :
    Integrable F μ := by
  have hi (n : ℕ) : Integrable (fun x => min (n:ℝ) (F x)) μ := by
    apply integrable_of_bounded (measurable_const.min hF)
    exact ⟨n,fun x => by
      rw [abs_of_nonneg (le_min (Nat.cast_nonneg _) (hF0 x))]
      exact min_le_left _ _⟩
  have heq (x : X) : ENNReal.ofReal (F x) =
      ⨆ n : ℕ, ENNReal.ofReal (min (n:ℝ) (F x)) := by
    apply le_antisymm
    · obtain ⟨n,hn⟩ := exists_nat_ge (F x)
      exact (by rw [min_eq_right hn] : ENNReal.ofReal (F x) ≤
        ENNReal.ofReal (min (n:ℝ) (F x))).trans (le_iSup (fun n : ℕ => ENNReal.ofReal (min (n:ℝ) (F x))) n)
    · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_right _ _)
  have hl : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal C := by
    simp_rw [heq]
    rw [lintegral_iSup (fun n => (measurable_const.min hF).ennreal_ofReal)
      (fun n m hnm x => ENNReal.ofReal_le_ofReal
        (min_le_min_right _ (Nat.cast_le.mpr hnm)))]
    apply iSup_le
    intro n
    rw [←ofReal_integral_eq_lintegral_ofReal (hi n)
      (ae_of_all _ fun x => le_min (Nat.cast_nonneg _) (hF0 x))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  exact (lintegral_ofReal_ne_top_iff_integrable hF.aestronglyMeasurable
    (ae_of_all _ hF0)).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hl)

noncomputable def logClip (n : ℕ) (x : ℝ) : ℝ := max (-(n:ℝ)) (min (n:ℝ) x)

end DirectionalTransience.Entropy

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_DescendingTrials
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def BoxStrip {d : ℕ} (e : Direction d) (N : ℕ) (B : Set (Lattice d)) : Set (Lattice d) :=
  {y | y ∈ B ∧ 0 ≤ signedHeight e y ∧ signedHeight e y ≤ (N:ℤ)}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CrossingGap
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def CrossingGap {d : ℕ} (e : Direction d) (N : ℕ) : Set (Path d) :=
  Cross (realPosition (step e)) 0 N \ Cross (realPosition (step e)) 0 (N+1)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FiniteBoxExit
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def ConfinedUntil {d : ℕ} (x : Lattice d) (S : Set (Lattice d)) (T : ℕ) : Set (Path d) :=
  {X | X 0=x ∧ ∀ j ≤ T, X j∈S}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace DirectionalTransience.StationaryCompact

abbrev Label := ℤ × ℕ
abbrev MarkSpace := ℕ∞ × ℕ∞ × ℝ≥0∞
abbrev EpisodeArray (H R : Type*) :=
  (ℤ → MarkSpace) × ((Label × Label) → OnePoint H) ×
    ((ℤ × Label × H) → Set.Icc (0:ℝ) 1) ×
    ((ℤ × ℕ × ℕ × ℕ × H) → R)

variable {H R : Type*}
  [TopologicalSpace H] [DiscreteTopology H] [Countable H]
  [TopologicalSpace R] [CompactSpace R] [T2Space R] [SecondCountableTopology R]

def shift (a : EpisodeArray H R) : EpisodeArray H R :=
  ⟨fun i => a.1 (i+1),
   (fun p => a.2.1 ((p.1.1+1,p.1.2),(p.2.1+1,p.2.2))),
   (fun p => a.2.2.1 (p.1+1,(p.2.1.1+1,p.2.1.2),p.2.2)),
   (fun p => a.2.2.2 (p.1+1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2))⟩

end DirectionalTransience.StationaryCompact

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_Array
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.quenchedKernel_markov _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.stateTrajectory_markov _root_.OAI.DirectionalTransience.state_measurableSingleton _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped NNReal ENNReal BigOperators Classical
namespace DirectionalTransience

def horizontalSubgroup {d : ℕ} (e : Direction d) : AddSubgroup (Lattice d) where
  carrier := {x | x e.1=0}
  zero_mem' := rfl
  add_mem' {x y} hx hy := by
    change x e.1=0 at hx
    change y e.1=0 at hy
    change x e.1+y e.1=0
    simp only [hx,hy,add_zero]
  neg_mem' {x} hx := by
    change x e.1=0 at hx
    change -x e.1=0
    simp only [hx,neg_zero]

abbrev HorizontalSpace {d : ℕ} (e : Direction d) := horizontalSubgroup e

abbrev ActualEpisodeArray {d : ℕ} (e : Direction d) :=
  StationaryCompact.EpisodeArray (HorizontalSpace e) (Row d)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GlobalProfile
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

def horizontalProjection {d : ℕ} (e : Direction d) (x : Lattice d) : HorizontalSpace e :=
  ⟨Function.update x e.1 0, by simp [horizontalSubgroup]⟩

def horizontalLift {d : ℕ} (e : Direction d) (h : ℤ) (z : HorizontalSpace e) : Lattice d :=
  z.val+h • step e

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience.AnchorSampling

variable {D I : Type*} {X : I → Type*}
  [MeasurableSpace D] [∀ i, MeasurableSpace (X i)]

lemma measurable_infinitePi (μ : D → (i : I) → Measure (X i))
    (hm : ∀ i, Measurable fun d => μ d i)
    [∀ d i, IsProbabilityMeasure (μ d i)] :
    Measurable (fun d => Measure.infinitePi (μ d)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => isPiSystem_measurableSet) (by simp))
  rintro _ ⟨s,t,ht,rfl⟩
  have htm : ∀ i, MeasurableSet (t i) := by simpa only [Set.mem_univ_pi,Set.mem_ofPred_eq] using ht
  simp_rw [Measure.infinitePi_pi _ (fun i _ => htm i)]
  exact Finset.measurable_fun_prod s (fun i _ => (Measure.measurable_coe (htm i)).comp (hm i))

noncomputable def anchorKernel {H : Type*} [MeasurableSpace H]
    (μ : D → ℤ → Measure H) (hm : ∀ i, Measurable fun d => μ d i)
    [∀ d i, IsProbabilityMeasure (μ d i)] : Kernel D ((ℤ×ℕ) → H) where
  toFun d := Measure.infinitePi (fun p : ℤ×ℕ => μ d p.1)
  measurable' := measurable_infinitePi _ fun p => hm p.1

instance anchorKernel_markov {H : Type*} [MeasurableSpace H]
    (μ : D → ℤ → Measure H) (hm : ∀ i, Measurable fun d => μ d i)
    [∀ d i, IsProbabilityMeasure (μ d i)] : IsMarkovKernel (anchorKernel μ hm) where
  isProbabilityMeasure d := by
    change IsProbabilityMeasure (Measure.infinitePi (fun p : ℤ×ℕ => μ d p.1))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end DirectionalTransience.AnchorSampling

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_DominatedEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal
namespace DirectionalTransience.Entropy
variable {X : Type*} [MeasurableSpace X]

lemma finite_kl_of_integrable_poslog (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hac : μ≪ν)
    (hF : Integrable (fun x => Real.log (max 1 ((μ.rnDeriv ν x).toReal))) μ) :
    klDiv μ ν≠∞ := by
  let g : X → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hg0 (x : X) : 0≤g x := ENNReal.toReal_nonneg
  let F : X → ℝ := fun x => Real.log (max 1 (g x))
  have hF0 (x : X) : 0≤F x := Real.log_nonneg (le_max_left _ _)
  have hp : Integrable (fun x => g x*F x) ν := (integrable_toReal_rnDeriv_mul_iff hac).mpr hF
  have hl : Integrable (fun x => g x*Real.log (g x)) ν := by
    apply (hp.add (integrable_const 1)).mono' (hg.mul hg.log).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      change |g x*Real.log (g x)|≤g x*F x+1
      apply abs_le.mpr
      constructor
      · have hlow : -1≤g x*Real.log (g x) := by
          by_cases hx : g x=0
          · simp [hx]
          have h := mul_le_mul_of_nonneg_left (Real.neg_inv_le_log (hg0 x)) (hg0 x)
          rw [mul_neg,mul_inv_cancel₀ hx] at h
          exact h
        have hn := mul_nonneg (hg0 x) (hF0 x)
        linarith
      · by_cases hx : g x=0
        · simp [hx]
        have h := mul_le_mul_of_nonneg_left
          (Real.log_le_log (lt_of_le_of_ne (hg0 x) (Ne.symm hx)) (le_max_right 1 (g x))) (hg0 x)
        change g x*Real.log (g x)≤g x*F x at h
        linarith
  exact klDiv_ne_top hac ((integrable_rnDeriv_mul_log_iff hac).mp hl)

lemma finite_kl_of_domination (Q μ ν : Measure X) [IsProbabilityMeasure Q]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hkl : klDiv μ ν≠∞)
    (K : ℝ) (hK : 0≤K) (hdom : Q≤ENNReal.ofReal K • μ) : klDiv Q ν≠∞ := by
  have hac : Q≪ν := (Measure.absolutelyContinuous_of_le hdom).trans
    (Measure.smul_absolutelyContinuous.trans (klDiv_ne_top_iff.mp hkl).1)
  let g : X → ℝ := fun x => (Q.rnDeriv ν x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv Q ν).ennreal_toReal
  have hg0 (x : X) : 0≤g x := ENNReal.toReal_nonneg
  have hgi : Integrable g ν := by
    simpa only [mul_one] using
      (integrable_toReal_rnDeriv_mul_iff hac (f := fun _ => (1:ℝ))).mpr (integrable_const 1)
  have hg1 : (∫ x, g x ∂ν)=1 := by
    simpa only [mul_one,integral_const,probReal_univ,one_smul] using
      (integral_toReal_rnDeriv_mul hac (f := fun _ => (1:ℝ)))
  apply finite_kl_of_integrable_poslog Q ν hac
  let F := fun x => Real.log (max 1 (g x))
  have hF : Measurable F := (measurable_const.max hg).log
  have hF0 (x : X) : 0≤F x := Real.log_nonneg (le_max_left _ _)
  apply integrable_of_bounded_truncated_integrals Q F hF hF0 (K*((klDiv μ ν).toReal+1))
  intro n
  let Fn : X → ℝ := fun x => min (n:ℝ) (F x)
  have hFn : Measurable Fn := measurable_const.min hF
  have hBn : ∃ B : ℝ, ∀ x, |Fn x|≤B := ⟨n,fun x => by
    rw [abs_of_nonneg (le_min (Nat.cast_nonneg _) (hF0 x))]
    exact min_le_left _ _⟩
  have hi : Integrable Fn μ := integrable_of_bounded hFn hBn
  have he : Integrable (fun x => Real.exp (Fn x)) ν := exp_integrable_of_bounded hFn hBn
  have htest := entropy_exp_test_le μ ν hkl Fn hi he
  have he₂ : (∫ x, Real.exp (Fn x) ∂ν)≤2 := by
    have hb := integral_mono he ((integrable_const 1).add hgi) (fun x => by
      calc Real.exp (Fn x)≤Real.exp (F x) := Real.exp_le_exp.mpr (min_le_right _ _)
        _ = max 1 (g x) := Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
        _ ≤ 1+g x := max_le (by linarith [hg0 x]) (by linarith))
    simpa only [Pi.add_apply,integral_add (integrable_const 1) hgi,integral_const,
      probReal_univ,one_smul,hg1,one_add_one_eq_two] using hb
  have hd := integral_mono_measure hdom
    (ae_of_all _ fun x => le_min (Nat.cast_nonneg n) (hF0 x))
    (hi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure,ENNReal.toReal_ofReal hK,smul_eq_mul] at hd
  exact hd.trans (mul_le_mul_of_nonneg_left (by linarith) hK)

end DirectionalTransience.Entropy

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_EntropyPlus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailDecorrelation

noncomputable def entropyPlus (u : ℝ) : ℝ := u * Real.log (max 1 u)

end TailDecorrelation

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_EntropyDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace DirectionalTransience.Entropy

lemma density_of_finite_kl {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hkl : klDiv μ ν≠∞) :
    ∃ g : X → ℝ, Measurable g ∧ (∀ x, 0≤g x) ∧ Integrable g ν ∧
      (∫ x, g x ∂ν)=1 ∧ Integrable (fun x => TailDecorrelation.entropyPlus (g x)) ν ∧
      μ=ν.withDensity (fun x => ENNReal.ofReal (g x)) := by
  obtain ⟨hac,hint⟩ := klDiv_ne_top_iff.mp hkl
  let g : X → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hgi : Integrable g ν := by
    simpa only [mul_one] using
      (integrable_toReal_rnDeriv_mul_iff hac (f := fun _ => (1:ℝ))).mpr (integrable_const 1)
  have hg1 : (∫ x, g x ∂ν)=1 := by
    simpa only [mul_one,integral_const,probReal_univ,one_smul] using
      (integral_toReal_rnDeriv_mul hac (f := fun _ => (1:ℝ)))
  have hpos : Integrable (fun x => Real.log (max 1 (g x))) μ := by
    apply hint.abs.mono' (measurable_const.max hg).log.aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (le_max_left _ _))]
    change Real.log (max 1 (g x))≤|Real.log (g x)|
    by_cases h : g x≤1
    · simp only [max_eq_left h,Real.log_one,abs_nonneg]
    · rw [max_eq_right (le_of_not_ge h)]
      exact le_abs_self _
  have hH := (integrable_toReal_rnDeriv_mul_iff hac).mpr hpos
  refine ⟨g,hg,fun _ => ENNReal.toReal_nonneg,hgi,hg1,hH,?_⟩
  rw [←Measure.withDensity_rnDeriv_eq μ ν hac]
  apply withDensity_congr_ae
  filter_upwards [Measure.rnDeriv_ne_top μ ν] with x hx
  exact (ENNReal.ofReal_toReal hx).symm

end DirectionalTransience.Entropy

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_EntropyEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience.Entropy
variable {X : Type*} [MeasurableSpace X]

lemma event_budget (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {C M t : ℝ} (hC : 0≤C) (hkl : klDiv μ ν≤ENNReal.ofReal C)
    (S : Set X) (hS : MeasurableSet S) (he : Real.exp t * ν.real S≤M) :
    μ.real S*t≤C+M := by
  let f : X → ℝ := S.indicator (fun _ => t)
  have hf : Measurable f := measurable_const.indicator hS
  have hb : ∃ B : ℝ, ∀ x, |f x|≤B := ⟨|t|,fun x => by
    by_cases hx : x∈S <;> simp [f,hx]⟩
  have hi : (∫ x, f x ∂μ)=μ.real S*t := by
    simp only [f,integral_indicator_const t hS,smul_eq_mul]
  have heq : (fun x => Real.exp (f x))=fun x => S.indicator (fun _ => Real.exp t-1) x+1 := by
    funext x
    by_cases hx : x∈S <;> simp [f,hx]
  have hh := expBudget_of_kl_le μ ν hC hkl f hf hb
  rw [hi,heq,integral_add ((integrable_const _).indicator hS) (integrable_const _),
    integral_indicator_const _ hS,integral_const,probReal_univ,one_smul,smul_eq_mul] at hh
  have hn : 0≤ν.real S := measureReal_nonneg
  nlinarith

lemma event_moment_budget (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0≤C) (hkl : klDiv μ ν≤ENNReal.ofReal C)
    (F : X → ℝ≥0∞) (hF : Measurable F) {M : ℝ≥0∞} (hM : M≠⊤)
    (hmean : (∫⁻ x, F x ∂ν)≤M) (t : ℝ) :
    μ.real {x | ENNReal.ofReal (Real.exp t)≤F x}*t ≤ C+M.toReal := by
  have hm := (mul_meas_ge_le_lintegral hF (ENNReal.ofReal (Real.exp t))).trans hmean
  have hr := ENNReal.toReal_mono hM hm
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hr
  exact event_budget μ ν hC hkl _ (measurableSet_le measurable_const hF) hr

end DirectionalTransience.Entropy

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_OccupationEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience.Entropy
variable {X I : Type*} [MeasurableSpace X]

noncomputable def activeSum (s : Finset I) (μ : I → Measure X) (E : I → Set X) : Measure X :=
  ∑ i ∈ s, (μ i).restrict (E i)

instance activeSum_finite (s : Finset I) (μ : I → Measure X)
    [∀ i, IsFiniteMeasure (μ i)] (E : I → Set X) : IsFiniteMeasure (activeSum s μ E) := by
  unfold activeSum
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end DirectionalTransience.Entropy

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AnchorMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience.AnchorSampling

variable {I H : Type*} [Countable H] [MeasurableSpace H] [MeasurableSingletonClass H]

noncomputable def atomError (ν : Measure H) (F : H → H) (u v : H) : ℝ :=
  (if v=F u then 1 else 0)-ν.real {F u}

end DirectionalTransience.AnchorSampling

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMap
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

instance horizontalOnePoint_measurable {d : ℕ} (e : Direction d) :
    MeasurableSpace (OnePoint (HorizontalSpace e)) := borel _

abbrev EpisodeAnchors {d : ℕ} (e : Direction d) := (ℤ×ℕ) → HorizontalSpace e

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_LocalStoppedSplice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal Topology
namespace DirectionalTransience.ReferenceClasses

variable {H : Type*} [AddCommGroup H]

abbrev Offsets (H : Type*) := (ℕ × ℕ) → OnePoint H

structure Consistent (O : Offsets H) : Prop where
  self : ∀ a, O (a,a) = (0 : H)
  symm : ∀ (a b : ℕ) (z : H), O (a,b) = (z : OnePoint H) → O (b,a) = ((-z : H) : OnePoint H)
  add : ∀ (a b c : ℕ) (z w : H), O (a,b) = (z : OnePoint H) → O (b,c) = (w : OnePoint H) →
    O (a,c) = ((z+w : H) : OnePoint H)

abbrev Data (H : Type*) [AddCommGroup H] := {O : Offsets H // Consistent O}

def related (O : Data H) (a b : ℕ) : Prop := ∃ z : H, O.1 (a,b) = (z : OnePoint H)

lemma related_self (O : Data H) (a : ℕ) : related O a a := ⟨0,O.2.self a⟩

noncomputable def representative (O : Data H) (a : ℕ) : ℕ :=
  @Nat.find (fun b => related O b a) (Classical.decPred _) ⟨a, related_self O a⟩

section Measurable
variable [Countable H] [TopologicalSpace H] [DiscreteTopology H]
  [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)]

variable {R : Type*} [MeasurableSpace R]

abbrev Site (H : Type*) := ℕ × ℕ × H
abbrev AllFields (H R : Type*) := Site H → R

end Measurable
end DirectionalTransience.ReferenceClasses

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_WindowProjection
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

abbrev CurrentProfiles {d : ℕ} (e : Direction d) :=
  (ℕ × HorizontalSpace e) → Set.Icc (0 : ℝ) 1

abbrev CurrentWindow {d : ℕ} (e : Direction d) :=
  (ReferenceClasses.Data (HorizontalSpace e) × CurrentProfiles e) ×
    ReferenceClasses.AllFields (HorizontalSpace e) (Row d)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayClosed
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal Classical
namespace DirectionalTransience

abbrev AmbientCurrentWindow {d : ℕ} (e : Direction d) :=
  (ReferenceClasses.Offsets (HorizontalSpace e) × CurrentProfiles e) ×
    ReferenceClasses.AllFields (HorizontalSpace e) (Row d)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AllOffsetConsistency
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

noncomputable def selectedOffsets {d : ℕ} (e : Direction d)
    (u : ℕ → StationaryCompact.Label) (Y : ActualEpisodeArray e) :
    ReferenceClasses.Offsets (HorizontalSpace e) := fun p => Y.2.1 (u p.1,u p.2)

def ArrayOffsetsConsistent {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e) : Prop :=
  ∀ u : ℕ → StationaryCompact.Label, ReferenceClasses.Consistent (selectedOffsets e u Y)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferStageSuccess
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

def BufferStageSuccess {d : ℕ} (ℓ : Vector d) (f : Direction d) (H : ℕ)
    (z₀ r ε a g : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) : Prop :=
  (∀ h : ℕ, 0 < h → h ≤ H → g ≤ rawPairEndpointMass ℓ f h (z₀+(1-ε)*r) π ω) ∧
    g ≤ rawPairEndpointMass ℓ f H (z₀+(1+a)*r) π ω

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RawPairRetention
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

def BufferStageEvent {d : ℕ} (ℓ : Vector d) (f : Direction d) (H : ℕ)
    (z₀ r ε a g : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) : Prop :=
  (∀ h : ℕ, 0 < h → h ≤ H → ENNReal.ofReal g ≤ pairKernelMass ℓ f h (z₀+(1-ε)*r) π ω) ∧
    ENNReal.ofReal g ≤ pairKernelMass ℓ f H (z₀+(1+a)*r) π ω

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferRestorationScript
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma signedHeight_add_nsmul_other {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (x : Lattice d) (m : ℕ) : signedHeight e (x+m • step f)=signedHeight e x := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul,←add_assoc,signedHeight_add_step_other e f hef,ih]

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferChildNode
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

structure AdaptedBufferNode {d : ℕ} (e : Direction d) where
  level : ℝ
  radius : ℝ
  law : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) level)
  law_rows : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) level)) _ law
  active : Set (Environment d)
  active_rows : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) level)] active

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def BufferNodeValid {d : ℕ} (e f : Direction d) (z₀ : ℝ) (κ : ℝ≥0) (N : AdaptedBufferNode e) : Prop :=
  ∀ ω : Environment d, (∀ y u, κ ≤ (ω y).1 u) → ω ∈ N.active →
    IsProbabilityMeasure (N.law ω).val ∧
      ∀ᵐ x ∂(N.law ω).val, z₀+N.radius ≤ signedCoordinate f (x.2-x.1)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

abbrev BufferWords (n : ℕ) := {l : List (ℕ × Bool) // l.length=n}

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferChanceData
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def positiveBufferPlan {d : ℕ} (ν : Measure (Row d)) (e f : Direction d) (r : ℝ) : ℕ :=
  max 1 ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊

def BufferChanceData {d : ℕ} (ν : Measure (Row d)) (e f : Direction d)
    (α c ε g R : ℝ) : Prop :=
  ∀ r : ℝ, R ≤ r →
    positiveBufferPlan ν e f r = ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊ ∧
    ∀ z₀ : ℝ, ∀ π : Measure (Lattice d × Lattice d), IsProbabilityMeasure π →
      (∀ᵐ x ∂π, z₀+r ≤ signedCoordinate f (x.2-x.1)) →
      ENNReal.ofReal c ≤ environmentLaw ν {ω | BufferStageEvent (realPosition (step e)) f
        (positiveBufferPlan ν e f r) z₀ r ε α g π ω}

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_UpperKernel
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

abbrev UpperRows {d : ℕ} (e : Direction d) := (ℕ×HorizontalSpace e) → Row d

noncomputable def upperEnvironment {d : ℕ} (e : Direction d) (ξ : UpperRows e) : Environment d :=
  fun x => ξ ((signedHeight e x).toNat,horizontalProjection e x)

noncomputable def upperHorizontalKernel {d : ℕ} (e : Direction d) (H : ℕ) (ξ : UpperRows e) :
    Kernel (HorizontalSpace e) (HorizontalSpace e) :=
  Kernel.mk (fun z => (variableHitKernel (realPosition (step e)) H (upperEnvironment e ξ,horizontalLift e 0 z)).map
    (horizontalProjection e)) (measurable_of_countable _)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_Dust
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

abbrev CurrentData {d : ℕ} (e : Direction d) := ReferenceClasses.Data (HorizontalSpace e) × CurrentProfiles e

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ClassSelection
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def CurrentClassSelection {d : ℕ} (e : Direction d) (n : ℕ) (r : ℝ)
    (A : CurrentData e) (a : Fin n → ℕ) : Prop :=
  (∀ j, r≤(A.2 (a j,0):ℝ)) ∧
    ∀ j k, j≠k → ¬ReferenceClasses.related A.1 (a j) (a k)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FiniteClasses
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def CurrentFiniteClasses {d : ℕ} (e : Direction d) (A : CurrentData e) : Prop :=
  (Set.range (ReferenceClasses.representative A.1)).Finite

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GlobalTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators Classical
namespace DirectionalTransience

lemma injection_candidate_unique (x y R M : ℝ) (hR : 0 ≤ R) (hM : 2*R < M)
    (a b : ℕ) (ha : |x+M*(a+1)-y| < R) (hb : |x+M*(b+1)-y| < R) : a=b := by
  by_contra hab
  have hd : (1:ℝ) ≤ |(a:ℝ)-b| := by
    have hh0 : (0:ℤ) < |(a:ℤ)-b| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hab))
    have hh : (1:ℤ) ≤ |(a:ℤ)-b| := by omega
    exact_mod_cast hh
  have hn : |M*((a:ℝ)-b)| < 2*R := by
    calc
      _ = |(x+M*(a+1)-y)-(x+M*(b+1)-y)| := by congr 1; ring
      _ ≤ |x+M*(a+1)-y|+|x+M*(b+1)-y| := abs_sub _ _
      _ < 2*R := by linarith
  rw [abs_mul,abs_of_pos (lt_of_le_of_lt (by positivity) hM)] at hn
  nlinarith

lemma finite_injection_choice (k : ℕ) (R M : ℝ) (hR : 0 ≤ R) (hM : 2*R < M)
    (x : Fin k → ℝ) : ∃ m : Fin k → Fin k,
      ∀ i j, i ≠ j → R ≤ |(x i+M*((m i:ℕ)+1))-(x j+M*((m j:ℕ)+1))| := by
  induction k with
  | zero => exact ⟨Fin.elim0,fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨m,hm⟩ := ih (fun i => x i.castSucc)
    let bad : Fin k → Finset (Fin (k+1)) := fun j => Finset.univ.filter fun l =>
      |x (Fin.last k)+M*((l:ℕ)+1)-(x j.castSucc+M*((m j:ℕ)+1))| < R
    have hbad (j : Fin k) : (bad j).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      apply Fin.ext
      exact injection_candidate_unique _ _ R M hR hM _ _
        (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    let B := Finset.univ.biUnion bad
    have hB : B.card ≤ k := by
      calc
        B.card ≤ ∑ j, (bad j).card := Finset.card_biUnion_le
        _ ≤ ∑ _j : Fin k, 1 := Finset.sum_le_sum (fun j _ => hbad j)
        _ = k := by simp
    have hex : ∃ l : Fin (k+1), l ∉ B := by
      by_contra no
      have hu : B=Finset.univ := Finset.eq_univ_of_forall fun l => by simpa using not_exists.mp no l
      rw [hu] at hB
      simp only [Finset.card_univ,Fintype.card_fin] at hB
      omega
    obtain ⟨l,hl⟩ := hex
    have hlm (j : Fin k) : R ≤ |x (Fin.last k)+M*((l:ℕ)+1)-(x j.castSucc+M*((m j:ℕ)+1))| := by
      apply le_of_not_gt
      intro hh
      exact hl (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩⟩)
    refine ⟨Fin.lastCases l (fun j => (m j).castSucc),?_⟩
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact (hij rfl).elim
      | cast j => simpa using hlm j
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa only [Fin.lastCases_last,Fin.lastCases_castSucc,Fin.val_castSucc,abs_sub_comm] using hlm i
      | cast j =>
        simpa using hm i j (fun h => hij (congrArg Fin.castSucc h))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GridTrials
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def DropBetween {d : ℕ} (ℓ : Vector d) (n m : ℕ) : Set (Path d) :=
  {X | ∃ r, n ≤ r ∧ r < m ∧ dot (realPosition (X r)) ℓ < dot (realPosition (X n)) ℓ}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_FiniteCoordinateApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter UniformSpace
open scoped Uniformity Topology
namespace DirectionalTransience.Entropy

noncomputable def finiteFiller {I R : Type*} (r : I → R) (S : Finset I) (x : S → R) : I → R := by
  classical
  exact fun i => if h : i∈S then x ⟨i,h⟩ else r i

end DirectionalTransience.Entropy

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ReferenceFeller
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology BoundedContinuousFunction
namespace DirectionalTransience.Entropy

variable {X Y I : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

variable [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [SecondCountableTopology X] [SecondCountableTopology Y]

noncomputable def compProdProb (μ : ProbabilityMeasure X) (K : Kernel X Y) [IsMarkovKernel K] :
    ProbabilityMeasure (X×Y) := ⟨(μ : Measure X).compProd K,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

noncomputable def kernelProb (K : Kernel X Y) [IsMarkovKernel K] (x : X) :
    ProbabilityMeasure Y := ⟨K x,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

end DirectionalTransience.Entropy

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StageStopping
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def stageEndpointMass {d k : ℕ} (e f : Direction d) (a G : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (h : ℕ) (ω : Environment d) : ℝ≥0∞ :=
  rawTupleMixture (realPosition (step e)) h (π ω).val ω {y | TupleSeparated f G y}

lemma stageEndpointMass_adapted {d k : ℕ} (e f : Direction d) (a G : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) :
    Adapted (rowHeightFiltration (realPosition (step e)) a) (stageEndpointMass e f a G π) := by
  intro h
  have hle : rowSigma (BelowHeight (realPosition (step e)) a) ≤
      rowSigma (BelowHeight (realPosition (step e)) (a+h)) := by
    apply rowSigma_mono
    intro y hy
    change dot (realPosition y) (realPosition (step e)) < a+h
    change dot (realPosition y) (realPosition (step e)) < a at hy
    linarith [Nat.cast_nonneg (α:=ℝ) h]
  have hp := ((LayerTupleProfile.measurable_toSupported e a).comp hπ).mono hle le_rfl
  have hm := (rawTupleMixture_joint_rows (realPosition (step e)) h
    (TupleAtHeight (k:=k) (realPosition (step e)) a)
    (BelowHeight (realPosition (step e)) (a+h)) (by
      intro x hx j y hy
      change dot (realPosition y) (realPosition (step e))<a+h
      simpa only [hx j] using hy.2)).comp (hp.prodMk measurable_id)
  exact (Measure.measurable_coe (Set.to_countable _).measurableSet).comp hm

noncomputable def stageTestMass {d k : ℕ} (e f : Direction d) (a Gminus Gplus : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H h : ℕ) (ω : Environment d) : ℝ≥0∞ :=
  if h=0 then 1 else if h=H then
    min (stageEndpointMass e f a Gminus π h ω) (stageEndpointMass e f a Gplus π h ω)
  else stageEndpointMass e f a Gminus π h ω

lemma stageTestMass_adapted {d k : ℕ} (e f : Direction d) (a Gminus Gplus : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) (H : ℕ) :
    Adapted (rowHeightFiltration (realPosition (step e)) a) (stageTestMass e f a Gminus Gplus π H) := by
  intro h
  change @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+h))) _
    (fun ω => stageTestMass e f a Gminus Gplus π H h ω)
  by_cases hh : h=0
  · simp only [stageTestMass,hh]; exact measurable_const
  · simp only [stageTestMass,ite_eq_right hh]
    by_cases hH : h=H
    · simp only [ite_eq_left hH]
      exact (stageEndpointMass_adapted e f a Gminus π hπ h).min
        (stageEndpointMass_adapted e f a Gplus π hπ h)
    · simp only [ite_eq_right hH]
      exact stageEndpointMass_adapted e f a Gminus π hπ h

noncomputable def stageStop {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ) : Environment d → ℕ :=
  hittingBtwn (stageTestMass e f a Gminus Gplus π H)
    (Set.Iio (ENNReal.ofReal (Real.exp (-B)))) 1 (min H R)

lemma stageStop_stopping {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) (H R : ℕ) :
    IsStoppingTime (rowHeightFiltration (realPosition (step e)) a)
      (fun ω => (stageStop e f a Gminus Gplus B π H R ω : WithTop ℕ)) :=
  (stageTestMass_adapted e f a Gminus Gplus π hπ H).isStoppingTime_hittingBtwn measurableSet_Iio

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StageRetention
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma stageStop_event {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (H R h : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+h))]
      {ω | stageStop e f a Gminus Gplus B π H R ω=h} := by
  have ht := (stageStop_stopping e f a Gminus Gplus B π hπ H R).measurableSet_eq_of_countable h
  change MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+h))] _ at ht
  simpa only [WithTop.coe_inj, Nat.cast_withTop] using ht

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_OperationalEpisode
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

structure EpisodeState {d k : ℕ} (e f : Direction d) (r : ℝ  →  ℝ) where
  height : ℕ
  scale : ℝ
  profile : BudgetProfile (k:=k) e f height (r scale)

noncomputable def episodeStageH (χ b s : ℝ) : ℕ := ⌊s*Real.exp (χ*b)⌋₊

noncomputable def episodeStageLength {d k : ℕ} (e f : Direction d) (r : ℝ  →  ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) : ℕ :=
  stageStop e f q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (N-q.height) ω

noncomputable def episodeStageGrows {d k : ℕ} (e f : Direction d) (r : ℝ  →  ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) : Prop :=
  episodeStageLength e f r fexp g χ b N q ω=episodeStageH χ b q.scale ∧
    ENNReal.ofReal (Real.exp (-(k:ℝ)*b))  ≤
      stageTestMass e f q.height (r (q.scale*Real.exp (-fexp*b)))
        (r (q.scale*Real.exp (g*b))) (fun _ => q.profile.toLayerProfile)
        (episodeStageH χ b q.scale) (episodeStageLength e f r fexp g χ b N q ω) ω

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StageClassification
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def episodeStageFails {d k : ℕ} (e f : Direction d)
    (r : ℝ → ℝ) (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) : Prop :=
  stageTestMass e f q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (episodeStageLength e f r fexp g χ b N q ω) ω <
    ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayWindowMarks
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal Classical BigOperators
namespace DirectionalTransience

noncomputable def arrayWindowHeight {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ)
    (Y : ActualEpisodeArray e) : ℕ∞ := ∑ r∈Finset.range m, (Y.1 (i+r)).1
noncomputable def arrayWindowCost {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ)
    (Y : ActualEpisodeArray e) : ℝ≥0∞ := ∑ r∈Finset.range m, (Y.1 (i+r)).2.2

noncomputable def expNeg (C : ℝ≥0∞) : ℝ≥0∞ := EReal.exp (-(C:EReal))

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def arrayProfileMass {d : ℕ} (e : Direction d) (j : ℤ)
    (p : StationaryCompact.Label) (z : HorizontalSpace e) (Y : ActualEpisodeArray e) : ℝ≥0∞ :=
  ENNReal.ofReal (Y.2.2.1 (j,p,z):ℝ)

noncomputable def arrayUpperRows {d : ℕ} (e : Direction d) (i : ℤ) (m a : ℕ)
    (Y : ActualEpisodeArray e) : UpperRows e := fun p => Y.2.2.2 (i,m,a,p.1,p.2)

noncomputable def arrayKernelImage {d : ℕ} (e : Direction d) (i : ℤ) (m a H : ℕ)
    (A : Set (HorizontalSpace e)) (Y : ActualEpisodeArray e) : ℝ≥0∞ :=
  ∑' z, arrayProfileMass e i (i,a) z Y * upperHorizontalKernel e H (arrayUpperRows e i m a Y) z A

noncomputable def arrayDiscountedProfile {d : ℕ} (e : Direction d) (i : ℤ) (m a : ℕ)
    (z : HorizontalSpace e) (Y : ActualEpisodeArray e) : ℝ≥0∞ :=
  expNeg (arrayWindowCost e i m Y)*arrayProfileMass e (i+m) (i,a) z Y

def ArrayContinuation {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e) : Prop :=
  ∀ (i : ℤ) (m a H : ℕ) (z : HorizontalSpace e), arrayWindowHeight e i m Y=H →
    arrayKernelImage e i m a H {z} Y ≤ arrayDiscountedProfile e i m a z Y

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArraySurvival
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def arraySurvivalSum {d : ℕ} (e : Direction d) (i : ℤ) (m H n : ℕ)
    (Y : ActualEpisodeArray e) : ℝ≥0∞ :=
  ∑ a∈Finset.range n, upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeInjection
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience.BoundedInjection

noncomputable def injectionMultiplier (R : ℝ) : ℕ := ⌈2*R⌉₊+1

lemma injectionMultiplier_lt (R : ℝ) : 2*R < (injectionMultiplier R : ℝ) := by
  have h := Nat.le_ceil (2*R)
  dsimp [injectionMultiplier]
  push_cast
  linarith

noncomputable def injectionChoice {d k : ℕ} (f : Direction d) (R : ℝ) (hR : 0 ≤ R)
    (x : Fin k → Lattice d) : Fin k → Fin k :=
  (finite_injection_choice k R (injectionMultiplier R) hR (injectionMultiplier_lt R)
    (fun j => signedCoordinate f (x j))).choose

noncomputable def injectionOffset {d k : ℕ} (f : Direction d) (R : ℝ) (hR : 0 ≤ R)
    (x : Fin k → Lattice d) (j : Fin k) : ℕ :=
  injectionMultiplier R * ((injectionChoice f R hR x j : ℕ)+1)

noncomputable def injectTuple {d k : ℕ} (e f : Direction d) (R : ℝ) (hR : 0 ≤ R)
    (x : Fin k → Lattice d) : Fin k → Lattice d :=
  fun j => x j+injectionOffset f R hR x j • step f+step e

lemma injectTuple_separated {d k : ℕ} (e f : Direction d) (R : ℝ) (hR : 0 ≤ R)
    (x : Fin k → Lattice d) : TupleSeparated f R (injectTuple e f R hR x) := by
  intro i j hij
  have h := (finite_injection_choice k R (injectionMultiplier R) hR (injectionMultiplier_lt R)
    (fun j => signedCoordinate f (x j))).choose_spec i j hij
  simpa only [injectTuple,injectionOffset,signedCoordinate_add,signedCoordinate_nsmul,
    signedCoordinate_step_self,mul_one,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    add_sub_add_right_eq_sub,injectionChoice] using h

lemma injectTuple_height {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R : ℝ) (hR : 0 ≤ R) (a : ℝ) (x : Fin k → Lattice d)
    (hx : x ∈ TupleAtHeight (realPosition (step e)) a) :
    injectTuple e f R hR x ∈ TupleAtHeight (realPosition (step e)) (a+1) := by
  intro j
  have hh := hx j
  simp only [signedHeight_projection] at hh
  change dot (realPosition (x j+injectionOffset f R hR x j • step f+step e)) (realPosition (step e))=a+1
  simp only [signedHeight_projection,signedHeight_add_step_self,
    signedHeight_add_nsmul_other e f hef,Int.cast_add,Int.cast_one,hh]

noncomputable def injectionProfile {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R : ℝ) (hR : 0 ≤ R) (a : ℝ) (π : LayerTupleProfile (k:=k) e a) :
    BudgetProfile (k:=k) e f (a+1) R := by
  let ρ := π.val.map (injectTuple e f R hR)
  refine ⟨ρ,Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable,?_⟩
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
  exact π.property.2.mono fun x hx => ⟨injectTuple_height e f hef R hR a x hx,
    injectTuple_separated e f R hR x⟩

lemma injectionProfile_measurable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R : ℝ) (hR : 0 ≤ R) (a : ℝ) : Measurable (injectionProfile (k:=k) e f hef R hR a) := by
  exact ((Measure.measurable_map _ (measurable_of_countable _)).comp measurable_subtype_coe).subtype_mk

end DirectionalTransience.BoundedInjection

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeCharts
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

structure EpisodeChart {d k : ℕ} (e f : Direction d) (r : ℝ → ℝ) where
  height : ℕ
  scale : ℝ
  profile : Environment d → BudgetProfile (k:=k) e f height (r scale)
  measurable_profile : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) height)) _ profile
  event : Set (Environment d)
  measurable_event : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) height)] event

namespace EpisodeChart
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}

noncomputable def state (c : EpisodeChart (k:=k) e f r) (ω : Environment d) : EpisodeState (k:=k) e f r :=
  ⟨c.height,c.scale,c.profile ω⟩

noncomputable def layerProfile (c : EpisodeChart (k:=k) e f r) : Environment d → LayerTupleProfile (k:=k) e c.height :=
  fun ω => (c.profile ω).toLayerProfile

lemma measurable_layerProfile (c : EpisodeChart (k:=k) e f r) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) c.height)) _ c.layerProfile :=
  (measurable_subtype_coe.comp c.measurable_profile).subtype_mk

noncomputable def stop (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (N : ℕ) : Environment d → ℕ :=
  stageStop e f c.height (r (c.scale*Real.exp (-fexp*b))) (r (c.scale*Real.exp (g*b)))
    ((k:ℝ)*b) c.layerProfile (episodeStageH χ b c.scale) (N-c.height)

noncomputable def growsAt (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (j : ℕ) (ω : Environment d) : Prop :=
  j=episodeStageH χ b c.scale ∧ ENNReal.ofReal (Real.exp (-((k:ℝ)*b))) ≤
    stageTestMass e f c.height (r (c.scale*Real.exp (-fexp*b))) (r (c.scale*Real.exp (g*b)))
      c.layerProfile (episodeStageH χ b c.scale) j ω

lemma measurableSet_growsAt (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (j : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) ((c.height+j:ℕ):ℝ))]
      {ω | c.growsAt fexp g χ b j ω} := by
  have hm := (MeasurableSet.const (j=episodeStageH χ b c.scale)).inter
    (measurableSet_le (f:=fun _ : Environment d => ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))) measurable_const
      (stageTestMass_adapted e f c.height (r (c.scale*Real.exp (-fexp*b)))
        (r (c.scale*Real.exp (g*b))) c.layerProfile c.measurable_layerProfile
        (episodeStageH χ b c.scale) j))
  convert hm using 1 <;> first | rfl | (rw [Nat.cast_add]; rfl)

noncomputable def nextScale (c : EpisodeChart (k:=k) e f r) (fexp g b : ℝ) (grow : Bool) : ℝ :=
  if grow then c.scale*Real.exp (g*b) else c.scale*Real.exp (-fexp*b)

noncomputable def nextProfile (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g b : ℝ) (j : ℕ) (grow : Bool) (ω : Environment d) :
    BudgetProfile (k:=k) e f ((c.height+j:ℕ):ℝ) (r (c.nextScale fexp g b grow)) := by
  let p := seedSeparatedProfile e f hef c.height (r (c.nextScale fexp g b grow)) j (c.layerProfile ω) ω
  refine ⟨p.val,p.property.1,?_⟩
  simpa only [Nat.cast_add] using p.property.2

lemma measurable_nextProfile (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g b : ℝ) (j : ℕ) (grow : Bool) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) ((c.height+j:ℕ):ℝ))) _
      (c.nextProfile hef fexp g b j grow) := by
  apply Measurable.subtype_mk
  have hm := measurable_subtype_coe.comp
    (seedSeparatedProfile_measurable e f hef c.height (r (c.nextScale fexp g b grow)) j
      c.layerProfile c.measurable_layerProfile)
  convert hm using 1 <;> first | rfl | rw [Nat.cast_add]

noncomputable def nextEvent (c : EpisodeChart (k:=k) e f r)
    (fexp g χ b sfloor : ℝ) (N j : ℕ) (grow : Bool) : Set (Environment d) :=
  {ω | ω∈c.event ∧ c.height<N ∧ sfloor ≤ c.scale ∧ c.stop fexp g χ b N ω=j ∧
    (c.growsAt fexp g χ b j ω ↔ grow=true)}

lemma measurable_nextEvent (c : EpisodeChart (k:=k) e f r)
    (fexp g χ b sfloor : ℝ) (N j : ℕ) (grow : Bool) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) ((c.height+j:ℕ):ℝ))]
      (c.nextEvent fexp g χ b sfloor N j grow) := by
  have hle : rowSigma (BelowHeight (realPosition (step e)) (c.height:ℝ)) ≤
      rowSigma (BelowHeight (realPosition (step e)) ((c.height+j:ℕ):ℝ)) :=
    rowSigma_mono (by
      intro x hx
      change dot (realPosition x) (realPosition (step e)) < ((c.height+j:ℕ):ℝ)
      exact hx.trans_le (by exact_mod_cast Nat.le_add_right c.height j))
  have hstop := stageStop_event e f c.height (r (c.scale*Real.exp (-fexp*b)))
    (r (c.scale*Real.exp (g*b))) ((k:ℝ)*b) c.layerProfile c.measurable_layerProfile
    (episodeStageH χ b c.scale) (N-c.height) j
  have hg := c.measurableSet_growsAt fexp g χ b j
  have hlast : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) ((c.height+j:ℕ):ℝ))]
      {ω | c.growsAt fexp g χ b j ω ↔ grow=true} := by
    cases grow
    · simpa only [Bool.false_eq_true,iff_false,Set.compl_ofPred,Nat.cast_add] using hg.compl
    · simpa only [iff_true,Nat.cast_add] using hg
  have hc := hle _ c.measurable_event
  have hcast : ((c.height+j:ℕ):ℝ) = (c.height:ℝ)+(j:ℝ) := Nat.cast_add _ _
  rw [hcast] at hc hlast
  rw [hcast]
  exact hc.inter
    ((MeasurableSet.const (c.height<N)).inter ((MeasurableSet.const (sfloor ≤ c.scale)).inter
      (hstop.inter hlast)))

noncomputable def next (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N j : ℕ) (grow : Bool) : EpisodeChart (k:=k) e f r where
  height := c.height+j
  scale := c.nextScale fexp g b grow
  profile := c.nextProfile hef fexp g b j grow
  measurable_profile := c.measurable_nextProfile hef fexp g b j grow
  event := c.nextEvent fexp g χ b sfloor N j grow
  measurable_event := c.measurable_nextEvent fexp g χ b sfloor N j grow

end EpisodeChart
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

namespace EpisodeChart
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}

noncomputable def frozen (c : EpisodeChart (k:=k) e f r) (sfloor : ℝ) (N : ℕ) : EpisodeChart (k:=k) e f r where
  height := c.height
  scale := c.scale
  profile := c.profile
  measurable_profile := c.measurable_profile
  event := c.event ∩ {_ω | ¬(c.height<N ∧ sfloor ≤ c.scale)}
  measurable_event := c.measurable_event.inter (MeasurableSet.const _)

noncomputable def branch (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) : Option (ℕ×Bool) → EpisodeChart (k:=k) e f r
  | none => c.frozen sfloor N
  | some (j,grow) => c.next hef fexp g χ b sfloor N j grow

lemma branch_covers (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (ω : Environment d) (hω : ω∈c.event) :
    ∃ l, ω∈(c.branch hef fexp g χ b sfloor N l).event := by
  by_cases hr : c.height<N ∧ sfloor ≤ c.scale
  · let j := c.stop fexp g χ b N ω
    by_cases hg : c.growsAt fexp g χ b j ω
    · exact ⟨some (j,true),hω,hr.1,hr.2,rfl,by simpa only [iff_true] using hg⟩
    · exact ⟨some (j,false),hω,hr.1,hr.2,rfl,by simpa only [Bool.false_eq_true,iff_false] using hg⟩
  · exact ⟨none,hω,hr⟩

end EpisodeChart

structure EpisodeAtlas {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
    (q : Environment d → EpisodeState (k:=k) e f r) where
  Label : Type
  countable : Countable Label
  chart : Label → EpisodeChart (k:=k) e f r
  cover : ∀ ω, ∃ l, ω∈(chart l).event
  correct : ∀ l ω, ω∈(chart l).event → q ω=(chart l).state ω

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeAdapted
attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r}

def IsPartition (A : EpisodeAtlas q) : Prop :=
  ∀ l m ω, ω∈(A.chart l).event → ω∈(A.chart m).event → l=m

end EpisodeAtlas

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryWindowEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

def ArrayElliptic {d : ℕ} (e : Direction d) (κ : ℝ≥0) (Y : ActualEpisodeArray e) : Prop :=
  ∀ i m a l z u, κ ≤ (Y.2.2.2 (i,m,a,l,z)).1 u

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SurvivalLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def arraySurvivalAverage {d : ℕ} (e : Direction d) (i : ℤ) (m H n : ℕ)
    (Y : ActualEpisodeArray e) : ℝ := (n:ℝ)⁻¹*(arraySurvivalSum e i m H n Y).toReal

def ArrayAveragedSurvival {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e) : Prop :=
  ∀ (i : ℤ) (m H : ℕ), arrayWindowHeight e i m Y=H →
    limsup (fun r : ℕ => arraySurvivalAverage e i m H (2^r) Y) atTop ≤
      (expNeg (arrayWindowCost e i m Y)).toReal

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayPermutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter BoundedContinuousFunction
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def labelPerm (σ : Equiv.Perm ℕ) : Equiv.Perm StationaryCompact.Label :=
  Equiv.prodCongr (Equiv.refl ℤ) σ

def arrayPerm {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (Y : ActualEpisodeArray e) : ActualEpisodeArray e :=
  (Y.1,(fun p => Y.2.1 (labelPerm σ p.1,labelPerm σ p.2)),
    (fun p => Y.2.2.1 (p.1,labelPerm σ p.2.1,p.2.2)),
    (fun p => Y.2.2.2 (p.1,p.2.1,σ p.2.2.1,p.2.2.2)))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayProfileConsistency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def ArrayProfilesConsistent {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e) : Prop :=
  (∀ (j : ℤ) (p q : StationaryCompact.Label) (z w : HorizontalSpace e),
    Y.2.1 (p,q)=(z:OnePoint (HorizontalSpace e)) →
      Y.2.2.1 (j,p,z+w)=Y.2.2.1 (j,q,w)) ∧
  (∀ (j : ℤ) (p : StationaryCompact.Label) (s : Finset (HorizontalSpace e)),
    ∑ z∈s, (Y.2.2.1 (j,p,z):ℝ) ≤ 1)

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

def arrayDust {d : ℕ} (e : Direction d) (i : ℤ) (a : ℕ) (Y : ActualEpisodeArray e) : Prop :=
  (Y.2.2.1 (i,(i,a),0):ℝ)=0

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_ArrayGrowthEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

structure ArrayGrowthSector {d : ℕ} (e : Direction d)
    (μ : Measure (ActualEpisodeArray e)) where
  event : Set (ActualEpisodeArray e)
  measurable_event : MeasurableSet event
  positive_event : 0<μ event
  invariant : ∀ᵐ Y ∂μ, StationaryCompact.shift Y∈event ↔ Y∈event
  symmetric : ∀ σ, ∀ᵐ Y ∂μ, arrayPerm e σ Y∈event ↔ Y∈event
  ζ : ℝ
  positive_ζ : 0<ζ
  sequence : ℕ → ℕ
  strictMono : StrictMono sequence
  growth : ∀ᵐ Y ∂μ, Y∈event → ∀ᶠ k in atTop,
    ζ*(sequence k:ℝ)<(arrayWindowCost e 0 (sequence k) Y).toReal
  no_dust : ∀ᵐ Y ∂μ, Y∈event → ∀ i a, ¬arrayDust e i a Y

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

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical BigOperators Topology
namespace DirectionalTransience

def ArrayRelated {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (p q : StationaryCompact.Label) : Prop := ∃ z : HorizontalSpace e,
      Y.2.1 (p,q)=(z:OnePoint (HorizontalSpace e))

end DirectionalTransience

end

end OAI
end


