-- Prove2me | solution 1 for AgrawalGoyalTS.TwoArmed.thompson_sampling_two_armed_regret
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-19T06:44:48.865634+00:00
-- url     : https://prove2.me/submissions/4c2973c6-82c1-4423-8aeb-e5f56481a0c8

-- Licensed under Apache 2.0. Complete two-armed Thompson Sampling logarithmic regret.
import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_AgrawalGoyalTS_TwoArmed_ThompsonSampling

open MeasureTheory BanditAlgorithm


namespace ThompsonSamplingProof

open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

noncomputable def posteriorOdds (j s : ℕ) (y : ℝ) : ℝ :=
  (binomCDF (j + 1) y s)⁻¹ - 1

noncomputable def binomExpectation (j : ℕ) (μ : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ s ∈ Finset.range (j + 1), binomPMF j μ s * f s

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

 theorem argmaxMin_two (θ : Fin 2 → ℝ) :
    argmaxMin θ = if θ 1 ≤ θ 0 then 0 else 1 := by
  classical
  by_cases h : θ 1 ≤ θ 0
  · have hn : (Finset.univ.filter (fun i : Fin 2 => ∀ j, θ j ≤ θ i)).Nonempty := by
      refine ⟨0, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro j; fin_cases j <;> simp [h]
    rw [argmaxMin, dif_pos hn, if_pos h]
    apply le_antisymm
    · apply Finset.min'_le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro j; fin_cases j <;> simp [h]
    · exact Fin.zero_le _
  · have he : Finset.univ.filter (fun i : Fin 2 => ∀ j, θ j ≤ θ i) = {1} := by
      ext i; fin_cases i <;> simp [Fin.forall_fin_two, h, (lt_of_not_ge h).le]
    unfold argmaxMin
    rw [he]
    simp [h]

 theorem counts_succ (ω : TSOmega 2) (t : ℕ) :
    tsCounts ω (t+1) =
      if tsCoin ω t then
        (Function.update (tsCounts ω t).1 (tsArm ω t)
          ((tsCounts ω t).1 (tsArm ω t)+1), (tsCounts ω t).2)
      else
        ((tsCounts ω t).1, Function.update (tsCounts ω t).2 (tsArm ω t)
          ((tsCounts ω t).2 (tsArm ω t)+1)) := by
  classical
  unfold tsCoin tsReward tsArm tsTheta tsSuccesses tsFailures
  simp only [decide_eq_true_eq]
  rfl

 theorem plays_succ (ω : TSOmega 2) (t : ℕ) (i : Fin 2) :
    tsPlays ω (t+1) i = tsPlays ω t i + if tsArm ω t = i then 1 else 0 := by
  classical
  by_cases h : tsArm ω t = i <;>
    simp [tsPlays, Finset.range_add_one, Finset.filter_insert, h]

 theorem counts_eq_plays (ω : TSOmega 2) (t : ℕ) (i : Fin 2) :
    tsSuccesses ω t i + tsFailures ω t i = tsPlays ω t i := by
  classical
  induction t with
  | zero => simp [tsSuccesses, tsFailures, tsCounts, tsPlays]
  | succ t ih =>
    rw [plays_succ]
    simp only [tsSuccesses, tsFailures] at *
    rw [counts_succ]
    split <;> by_cases ha : tsArm ω t = i
    all_goals first | (subst i; simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]) |
      simp [ha, Ne.symm ha, ih]

 theorem plays_le_time (ω : TSOmega 2) (t : ℕ) (i : Fin 2) : tsPlays ω t i ≤ t := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range t)

 theorem counts_le_time (ω : TSOmega 2) (t : ℕ) (i : Fin 2) :
    tsSuccesses ω t i ≤ t ∧ tsFailures ω t i ≤ t := by
  have h := plays_le_time ω t i
  rw [← counts_eq_plays] at h
  omega

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

abbrev History := ℕ → Fin 2 × Bool
abbrev CountState := (Fin 2 → ℕ) × (Fin 2 → ℕ)

 def updateCounts (c : CountState) (a : Fin 2) (b : Bool) : CountState :=
  if b then (Function.update c.1 a (c.1 a+1), c.2)
  else (c.1, Function.update c.2 a (c.2 a+1))

 def historyCounts (h : History) : ℕ → CountState
  | 0 => (0,0)
  | t+1 => updateCounts (historyCounts h t) (h t).1 (h t).2

 noncomputable def nativeHistory (ω : TSOmega 2) : History :=
  fun t => (tsArm ω t, tsCoin ω t)

 theorem native_counts_history (ω : TSOmega 2) (t : ℕ) :
    tsCounts ω t = historyCounts (nativeHistory ω) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [counts_succ, historyCounts]; simp only [nativeHistory, updateCounts, ih]; rfl

 theorem historyCounts_congr {h g : History} {t : ℕ} (he : ∀ u < t, h u = g u) :
    historyCounts h t = historyCounts g t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [historyCounts, historyCounts, ih (fun u hu => he u (by omega)), he t (by omega)]

 def historyPlays (h : History) (t : ℕ) (i : Fin 2) : ℕ :=
  ((Finset.range t).filter (fun u => (h u).1 = i)).card

 theorem historyPlays_succ (h : History) (t : ℕ) (i : Fin 2) :
    historyPlays h (t+1) i = historyPlays h t i + if (h t).1 = i then 1 else 0 := by
  classical
  by_cases he : (h t).1 = i <;>
    simp [historyPlays, Finset.range_add_one, Finset.filter_insert, he]

 theorem historyCounts_total (h : History) (t : ℕ) (i : Fin 2) :
    (historyCounts h t).1 i + (historyCounts h t).2 i = historyPlays h t i := by
  induction t with
  | zero => simp [historyCounts, historyPlays]
  | succ t ih =>
    rw [historyPlays_succ, historyCounts]
    unfold updateCounts
    split <;> by_cases ha : (h t).1 = i
    all_goals first | (subst i; simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]) |
      simp [ha, Ne.symm ha, ih]

 theorem historyPlays_mono (h : History) (i : Fin 2) : Monotone (fun t => historyPlays h t i) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [historyPlays_succ]
  omega

 theorem history_pull_index_injective (h : History) :
    Function.Injective (fun t => ((h t).1, historyPlays h t (h t).1)) := by
  intro s t he
  have ha := congrArg Prod.fst he
  have hn := congrArg Prod.snd he
  dsimp at ha hn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · have hh := historyPlays_mono h (h s).1 (Nat.succ_le_of_lt hst)
    change historyPlays h (s+1) (h s).1 ≤ historyPlays h t (h s).1 at hh
    rw [historyPlays_succ, if_pos rfl] at hh
    rw [ha] at hn hh
    omega
  · have hh := historyPlays_mono h (h t).1 (Nat.succ_le_of_lt hts)
    change historyPlays h (t+1) (h t).1 ≤ historyPlays h s (h t).1 at hh
    rw [historyPlays_succ, if_pos rfl] at hh
    rw [← ha] at hn hh
    omega

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory

 theorem measurable_countable_selection {Ω ι E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Countable ι] [MeasurableSpace E]
    {f : ι → Ω → E} {k : Ω → ι}
    (hf : ∀ i, Measurable (f i)) (hk : Measurable k) :
    Measurable (fun ω => f (k ω) ω) := by
  intro s hs
  have he : (fun ω => f (k ω) ω) ⁻¹' s =
      ⋃ i, (k ⁻¹' {i}) ∩ (f i ⁻¹' s) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨k ω, rfl, h⟩, fun ⟨i, hi, h⟩ => hi ▸ h⟩
  rw [he]
  exact MeasurableSet.iUnion fun i => (hk (measurableSet_singleton i)).inter (hf i hs)

 theorem measurable_selected_table {Ω ι E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Countable ι] [MeasurableSpace E]
    {f : Ω → (ι → E)} {k : Ω → ι}
    (hf : Measurable f) (hk : Measurable k) : Measurable (fun ω => f ω (k ω)) :=
  measurable_countable_selection (fun i => (measurable_pi_apply i).comp hf) hk

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

 theorem argmaxMin_two_measurable : Measurable (argmaxMin : (Fin 2 → ℝ) → Fin 2) := by
  classical
  have he : (argmaxMin : (Fin 2 → ℝ) → Fin 2) =
      fun θ => if θ 1 ≤ θ 0 then 0 else 1 := funext argmaxMin_two
  rw [he]
  exact Measurable.ite (measurableSet_le (measurable_pi_apply 1) (measurable_pi_apply 0))
    measurable_const measurable_const

 theorem counts_measurable (t : ℕ) : Measurable (fun ω : TSOmega 2 => tsCounts ω t) := by
  classical
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have htheta : Measurable (fun ω : TSOmega 2 => tsTheta ω t) := by
      apply measurable_pi_lambda
      intro i
      change Measurable (fun ω : TSOmega 2 => ω.1 (i,t,(tsCounts ω t).1 i,(tsCounts ω t).2 i))
      exact measurable_selected_table measurable_fst
        (measurable_const.prodMk (measurable_const.prodMk
          ((ih.fst.eval).prodMk (ih.snd.eval))))
    have ha : Measurable (fun ω : TSOmega 2 => tsArm ω t) :=
      argmaxMin_two_measurable.comp htheta
    have hr : Measurable (fun ω : TSOmega 2 => tsReward ω t) := by
      change Measurable (fun ω : TSOmega 2 => ω.2.1 (tsArm ω t,t))
      exact measurable_selected_table measurable_snd.fst (ha.prodMk measurable_const)
    have hv : Measurable (fun ω : TSOmega 2 => (ω.2.2 (tsArm ω t,t) : ℝ)) :=
      (measurable_selected_table measurable_snd.snd (ha.prodMk measurable_const)).subtype_val
    have hc : MeasurableSet {ω : TSOmega 2 | tsCoin ω t = true} := by
      simpa only [tsCoin, decide_eq_true_eq] using measurableSet_lt hv hr
    have hs : Measurable (fun ω : TSOmega 2 => Function.update (tsCounts ω t).1
        (tsArm ω t) ((tsCounts ω t).1 (tsArm ω t)+1)) := by
      apply measurable_countable_selection (f := fun i ω => Function.update (tsCounts ω t).1 i ((tsCounts ω t).1 i+1)) (k := fun ω => tsArm ω t) _ ha
      intro i
      exact measurable_update'.comp ((ih.fst).prodMk ((ih.fst.eval).add_const 1))
    have hf : Measurable (fun ω : TSOmega 2 => Function.update (tsCounts ω t).2
        (tsArm ω t) ((tsCounts ω t).2 (tsArm ω t)+1)) := by
      apply measurable_countable_selection (f := fun i ω => Function.update (tsCounts ω t).2 i ((tsCounts ω t).2 i+1)) (k := fun ω => tsArm ω t) _ ha
      intro i
      exact measurable_update'.comp ((ih.snd).prodMk ((ih.snd.eval).add_const 1))
    simpa only [counts_succ] using Measurable.ite hc (hs.prodMk ih.snd) (ih.fst.prodMk hf)

 theorem theta_measurable (t : ℕ) : Measurable (fun ω : TSOmega 2 => tsTheta ω t) := by
  apply measurable_pi_lambda
  intro i
  change Measurable (fun ω : TSOmega 2 => ω.1 (i,t,(tsCounts ω t).1 i,(tsCounts ω t).2 i))
  exact measurable_selected_table measurable_fst
    (measurable_const.prodMk (measurable_const.prodMk
      (((counts_measurable t).fst.eval).prodMk ((counts_measurable t).snd.eval))))

 theorem arm_measurable (t : ℕ) : Measurable (fun ω : TSOmega 2 => tsArm ω t) :=
  argmaxMin_two_measurable.comp (theta_measurable t)

 theorem plays_measurable (t : ℕ) (i : Fin 2) :
    Measurable (fun ω : TSOmega 2 => tsPlays ω t i) := by
  have h := ((counts_measurable t).fst.eval (a := i)).add
    ((counts_measurable t).snd.eval (a := i))
  change Measurable (fun ω => tsSuccesses ω t i + tsFailures ω t i) at h
  simpa only [counts_eq_plays] using h

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

 noncomputable def historyChoice (W : Fin 2 × ℕ × ℕ × ℕ → ℝ) (h : History) (t : ℕ) : Fin 2 :=
  argmaxMin (fun i => W (i,t,(historyCounts h t).1 i,(historyCounts h t).2 i))

 def historyEvent (h : History) (T : ℕ) : Set (TSOmega 2) :=
  {ω | ∀ t < T, nativeHistory ω t = h t}

 theorem counts_on_history {h : History} {ω : TSOmega 2} {T : ℕ}
    (he : ω ∈ historyEvent h T) {t : ℕ} (ht : t ≤ T) :
    tsCounts ω t = historyCounts h t := by
  rw [native_counts_history]
  exact historyCounts_congr (fun u hu => he u (lt_of_lt_of_le hu ht))

 theorem arm_on_history {h : History} {ω : TSOmega 2} {T : ℕ}
    (he : ω ∈ historyEvent h T) : tsArm ω T = historyChoice ω.1 h T := by
  unfold tsArm tsTheta tsSuccesses tsFailures historyChoice
  rw [counts_on_history he le_rfl]

 theorem historyEvent_measurable (h : History) (T : ℕ) : MeasurableSet (historyEvent h T) := by
  simp only [historyEvent, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro t
  apply MeasurableSet.iInter
  intro _ht
  have ha := arm_measurable t
  have hr : Measurable (fun ω : TSOmega 2 => ω.2.1 (tsArm ω t,t)) :=
    measurable_selected_table measurable_snd.fst (ha.prodMk measurable_const)
  have hv : Measurable (fun ω : TSOmega 2 => (ω.2.2 (tsArm ω t,t) : ℝ)) :=
    (measurable_selected_table measurable_snd.snd (ha.prodMk measurable_const)).subtype_val
  have hb : Measurable (fun ω : TSOmega 2 => tsCoin ω t) := by
    apply measurable_to_bool
    change MeasurableSet {ω : TSOmega 2 | decide ((ω.2.2 (tsArm ω t,t) : ℝ) < ω.2.1 (tsArm ω t,t)) = true}
    simpa only [decide_eq_true_eq] using measurableSet_lt hv hr
  exact (ha.prodMk hb) (measurableSet_singleton (h t))

 theorem historyEvent_local (h : History) (T : ℕ) (ω : TSOmega 2) :
    ω ∈ historyEvent h T ↔ ∀ t < T,
      historyChoice ω.1 h t = (h t).1 ∧
      decide ((ω.2.2 ((h t).1,t) : ℝ) < ω.2.1 ((h t).1,t)) = (h t).2 := by
  constructor
  · intro he t ht
    have hp : ω ∈ historyEvent h t := fun u hu => he u (hu.trans ht)
    have hc := arm_on_history hp
    have hs := he t ht
    have ha : tsArm ω t = (h t).1 := congrArg Prod.fst hs
    have hb : tsCoin ω t = (h t).2 := congrArg Prod.snd hs
    refine ⟨hc.symm.trans ha, ?_⟩
    simpa only [tsCoin, tsReward, ha] using hb
  · intro he
    have hh : ∀ t, t ≤ T → ω ∈ historyEvent h t := by
      intro t
      induction t with
      | zero => intro _ u hu; omega
      | succ t ih =>
        intro ht
        have hp := ih (by omega)
        have hd := he t (by omega)
        have ha : tsArm ω t = (h t).1 := (arm_on_history hp).trans hd.1
        intro u hu
        rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
        · exact hp u hu
        · apply Prod.ext
          · exact ha
          · simpa only [nativeHistory, tsCoin, tsReward, ha] using hd.2
    exact hh T le_rfl

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory Set

 theorem product_disjoint_blocks {ι E : Type*} [DecidableEq ι] [MeasurableSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)]
    (S T : Finset ι) (hST : Disjoint S T) :
    IndepFun (fun ω : ι → E => fun i : S => ω i)
      (fun ω : ι → E => fun i : T => ω i) (Measure.infinitePi P) := by
  exact (iIndepFun_infinitePi (P := P) (X := fun _ x => x)
    (fun _ => measurable_id)).indepFun_finset S T hST (fun _ => measurable_pi_apply _)

 theorem product_fresh_event {ι E : Type*} [DecidableEq ι] [MeasurableSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)]
    (S T : Finset ι) (hST : Disjoint S T)
    (A : Set (S → E)) (B : Set (T → E))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (Measure.infinitePi P) {ω | (fun i : S => ω i) ∈ A ∧ (fun i : T => ω i) ∈ B} =
      (Measure.infinitePi P) {ω | (fun i : S => ω i) ∈ A} *
      (Measure.infinitePi P) {ω | (fun i : T => ω i) ∈ B} := by
  exact (product_disjoint_blocks P S T hST).measure_inter_preimage_eq_mul A B hA hB

 theorem product_injective_coordinates {ι κ E : Type*} [MeasurableSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)]
    (f : κ → ι) (hf : Function.Injective f) :
    (Measure.infinitePi P).map (fun ω i => ω (f i)) = Measure.infinitePi (fun i => P (f i)) :=
  Measure.map_infinitePi_infinitePi_of_inj hf

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory

 theorem finite_pair_law {ι X Y : Type*} [Fintype ι] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ι → Measure X) (ν : ι → Measure Y) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.pi μ).prod (Measure.pi ν)).map (fun z i => (z.1 i,z.2 i)) =
      Measure.pi (fun i => (μ i).prod (ν i)) := by
  exact (MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow X Y ι)
    (measurePreserving_arrowProdEquivProdArrow X Y ι μ ν)).map_eq

 theorem selected_pair_law {ι κ X Y : Type*} [Fintype κ]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ι → Measure X) (ν : ι → Measure Y) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] (f : κ → ι) (hf : Function.Injective f) :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun z i => (z.1 (f i), z.2 (f i))) =
        Measure.pi (fun i => (μ (f i)).prod (ν (f i))) := by
  have hμ := product_injective_coordinates μ f hf
  have hν := product_injective_coordinates ν f hf
  rw [Measure.infinitePi_eq_pi (fun i : κ => μ (f i))] at hμ
  rw [Measure.infinitePi_eq_pi (fun i : κ => ν (f i))] at hν
  have hm : Measurable (fun z : ι → X => fun i => z (f i)) := by fun_prop
  have hn : Measurable (fun z : ι → Y => fun i => z (f i)) := by fun_prop
  have hprod := Measure.map_prod_map (Measure.infinitePi μ) (Measure.infinitePi ν) hm hn
  rw [hμ,hν] at hprod
  have hz := finite_pair_law (fun i => μ (f i)) (fun i => ν (f i))
  rw [hprod, Measure.map_map (by fun_prop) (hm.prodMap hn)] at hz
  exact hz

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm Set

 theorem reward_ae_bounds (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : P (Icc 0 1) = 1) : ∀ᵐ x ∂P, 0 ≤ x ∧ x ≤ 1 := by
  exact (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hP

 theorem reward_integrable (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : P (Icc 0 1) = 1) : Integrable (fun x : ℝ => x) P := by
  apply (integrable_const (1 : ℝ)).mono' measurable_id.aestronglyMeasurable
  filter_upwards [reward_ae_bounds P hP] with x hx
  simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

 theorem reward_mean_bounds (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : P (Icc 0 1) = 1) : 0 ≤ ∫ x, x ∂P ∧ (∫ x, x ∂P) ≤ 1 := by
  have hi := reward_integrable P hP
  constructor
  · exact integral_nonneg_of_ae ((reward_ae_bounds P hP).mono fun _ h => h.1)
  · simpa using integral_mono_ae hi (integrable_const (1 : ℝ))
      ((reward_ae_bounds P hP).mono fun _ h => h.2)

 theorem reward_coin_probability (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : P (Icc 0 1) = 1) :
    (P.prod (volume : Measure unitInterval)) {z | (z.2 : ℝ) < z.1} =
      ENNReal.ofReal (∫ x, x ∂P) := by
  rw [Measure.prod_apply (measurableSet_lt (by fun_prop) (by fun_prop))]
  calc
    _ = ∫⁻ x : ℝ, ENNReal.ofReal x ∂P := by
      apply lintegral_congr_ae
      filter_upwards [reward_ae_bounds P hP] with x hx
      exact unitInterval.volume_Iio (⟨x,hx⟩ : unitInterval)
    _ = _ := (ofReal_integral_eq_lintegral_ofReal (reward_integrable P hP)
      ((reward_ae_bounds P hP).mono fun _ h => h.1)).symm

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory Set

 theorem bool_measure_ext {μ ν : Measure Bool} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : μ {true} = ν {true}) : μ = ν := by
  apply Measure.ext_of_singleton
  intro b
  cases b
  · have he : ({false} : Set Bool) = {true}ᶜ := by ext b; cases b <;> simp
    rw [he, prob_compl_eq_one_sub (measurableSet_singleton _),
      prob_compl_eq_one_sub (measurableSet_singleton _), h]
  · exact h

 noncomputable def rewardCoin (z : ℝ × unitInterval) : Bool := decide ((z.2 : ℝ) < z.1)

 theorem rewardCoin_measurable : Measurable rewardCoin := by
  apply measurable_to_bool
  simpa only [rewardCoin, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
    (measurableSet_lt (by fun_prop) (by fun_prop) :
      MeasurableSet {z : ℝ × unitInterval | (z.2 : ℝ) < z.1})

 theorem rewardCoin_map (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : P (Icc 0 1) = 1) :
    (P.prod (volume : Measure unitInterval)).map rewardCoin =
      bernoulliMeasure true false ⟨∫ x, x ∂P, reward_mean_bounds P hP⟩ := by
  let : IsProbabilityMeasure ((P.prod (volume : Measure unitInterval)).map rewardCoin) :=
    Measure.isProbabilityMeasure_map rewardCoin_measurable.aemeasurable
  apply bool_measure_ext
  rw [Measure.map_apply rewardCoin_measurable (measurableSet_singleton _)]
  have he : rewardCoin ⁻¹' {true} = {z : ℝ × unitInterval | (z.2 : ℝ) < z.1} := by
    ext z; simp [rewardCoin]
  rw [he, reward_coin_probability P hP]
  rw [bernoulliMeasure_apply_of_mem_of_notMem (x := true) (y := false)
    (s := {true}) _ (measurableSet_singleton _) (by simp) (by simp)]
  exact ENNReal.ofReal_eq_coe_nnreal (reward_mean_bounds P hP).1

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory Set

 noncomputable def meanParameter (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : P (Icc 0 1) = 1) : unitInterval := ⟨∫ x, x ∂P, reward_mean_bounds P hP⟩

 theorem selected_coin_law {ι κ : Type*} [Fintype κ]
    (P : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (P i)]
    (hP : ∀ i, P i (Icc 0 1) = 1) (f : κ → ι) (hf : Function.Injective f) :
    ((Measure.infinitePi P).prod
      (Measure.infinitePi (fun _ : ι => (volume : Measure unitInterval)))).map
      (fun z i => rewardCoin (z.1 (f i),z.2 (f i))) =
      Measure.pi (fun i => bernoulliMeasure true false (meanParameter (P (f i)) (hP (f i)))) := by
  have hp := selected_pair_law P (fun _ : ι => (volume : Measure unitInterval)) f hf
  have hm : Measurable (fun z : (ι → ℝ) × (ι → unitInterval) =>
      fun i : κ => (z.1 (f i),z.2 (f i))) := by fun_prop
  have hc : Measurable (fun z : κ → ℝ × unitInterval => fun i => rewardCoin (z i)) :=
    measurable_pi_lambda _ (fun i => rewardCoin_measurable.comp (measurable_pi_apply i))
  calc
    _ = ((Measure.pi (fun i => (P (f i)).prod (volume : Measure unitInterval)))).map
        (fun z i => rewardCoin (z i)) := by
      rw [← hp, Measure.map_map hc hm]
      rfl
    _ = _ := by
      let (i : κ) : IsProbabilityMeasure (((P (f i)).prod
          (volume : Measure unitInterval)).map rewardCoin) :=
        Measure.isProbabilityMeasure_map rewardCoin_measurable.aemeasurable
      rw [Measure.pi_map_pi (fun _ => rewardCoin_measurable.aemeasurable)]
      congr 1
      funext i
      exact rewardCoin_map (P (f i)) (hP (f i))

 theorem selected_coin_pattern {ι κ : Type*} [Fintype κ]
    (P : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (P i)]
    (hP : ∀ i, P i (Icc 0 1) = 1) (f : κ → ι) (hf : Function.Injective f)
    (b : κ → Bool) :
    ((Measure.infinitePi P).prod
      (Measure.infinitePi (fun _ : ι => (volume : Measure unitInterval))))
      {z | ∀ i, rewardCoin (z.1 (f i),z.2 (f i)) = b i} =
      ∏ i, bernoulliMeasure true false (meanParameter (P (f i)) (hP (f i))) {b i} := by
  have hm : Measurable (fun z : (ι → ℝ) × (ι → unitInterval) =>
      fun i : κ => rewardCoin (z.1 (f i),z.2 (f i))) := by
    apply measurable_pi_lambda
    intro i
    exact rewardCoin_measurable.comp (by fun_prop)
  have hh := congrArg (fun μ : Measure (κ → Bool) => μ (Set.univ.pi (fun i => {b i})))
    (selected_coin_law P hP f hf)
  rw [Measure.map_apply hm (MeasurableSet.univ_pi (fun _ => measurableSet_singleton _)),
    Measure.pi_pi] at hh
  simpa only [Set.preimage, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_singleton_iff] using hh

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 noncomputable def posteriorLaw : Measure (Fin 2 × ℕ × ℕ × ℕ → ℝ) :=
  Measure.infinitePi (fun k => betaMeasure ((k.2.2.1 : ℝ)+1) ((k.2.2.2 : ℝ)+1))

 instance posteriorLaw_probability : IsProbabilityMeasure posteriorLaw := by
  unfold posteriorLaw
  infer_instance

 def posteriorHistoryEvent (h : History) (T : ℕ) : Set (Fin 2 × ℕ × ℕ × ℕ → ℝ) :=
  {W | ∀ t < T, historyChoice W h t = (h t).1}

 theorem posteriorHistoryEvent_measurable (h : History) (T : ℕ) :
    MeasurableSet (posteriorHistoryEvent h T) := by
  simp only [posteriorHistoryEvent, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro t
  apply MeasurableSet.iInter
  intro _ht
  exact (argmaxMin_two_measurable.comp (by fun_prop)) (measurableSet_singleton _)

 theorem native_history_probability (ν : StochasticBandit 2)
    (hν : ∀ i, ν.P i (Icc 0 1) = 1) (h : History) (T : ℕ) :
    tsLaw ν (historyEvent h T) = posteriorLaw (posteriorHistoryEvent h T) *
      ∏ t : Fin T, bernoulliMeasure true false
        (meanParameter (ν.P (h t).1) (hν (h t).1)) {(h t).2} := by
  let E : Set ((Fin 2 × ℕ → ℝ) × (Fin 2 × ℕ → unitInterval)) :=
    {z | ∀ t : Fin T, rewardCoin (z.1 ((h t).1,t),z.2 ((h t).1,t)) = (h t).2}
  have he : historyEvent h T = (posteriorHistoryEvent h T) ×ˢ E := by
    ext ω
    rw [historyEvent_local]
    simp only [Set.mem_prod, posteriorHistoryEvent, E, Set.mem_ofPred_eq, rewardCoin]
    constructor
    · intro hh
      exact ⟨fun t ht => (hh t ht).1, fun t => (hh t t.isLt).2⟩
    · rintro ⟨ha,hb⟩ t ht
      exact ⟨ha t ht,hb ⟨t,ht⟩⟩
  rw [he]
  change (posteriorLaw.prod ((Measure.infinitePi (fun k : Fin 2 × ℕ => ν.P k.1)).prod
    (Measure.infinitePi (fun _ : Fin 2 × ℕ => (volume : Measure unitInterval)))))
      ((posteriorHistoryEvent h T) ×ˢ E) = _
  rw [Measure.prod_prod]
  congr 1
  exact selected_coin_pattern (fun k : Fin 2 × ℕ => ν.P k.1) (fun k => hν k.1)
    (fun t : Fin T => ((h t).1,(t : ℕ)))
    (fun s t he => Fin.ext (congrArg Prod.snd he)) (fun t : Fin T => (h t).2)

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

abbrev SliceIndex := Fin 2 × ℕ × ℕ
abbrev PosteriorSlice := SliceIndex → ℝ
abbrev Calendar := ℕ → PosteriorSlice

 noncomputable def sliceLaw : Measure PosteriorSlice :=
  Measure.infinitePi (fun k : SliceIndex => betaMeasure ((k.2.1 : ℝ)+1) ((k.2.2 : ℝ)+1))

 instance sliceLaw_probability : IsProbabilityMeasure sliceLaw := by
  unfold sliceLaw
  infer_instance

 def toCalendar (W : Fin 2 × ℕ × ℕ × ℕ → ℝ) : Calendar :=
  fun t k => W (k.1,t,k.2.1,k.2.2)

 def fromCalendar (W : Calendar) : Fin 2 × ℕ × ℕ × ℕ → ℝ :=
  fun k => W k.2.1 (k.1,k.2.2.1,k.2.2.2)

 theorem from_toCalendar (W : Fin 2 × ℕ × ℕ × ℕ → ℝ) :
    fromCalendar (toCalendar W) = W := rfl

 theorem calendar_law : posteriorLaw.map toCalendar =
    Measure.infinitePi (fun _ : ℕ => sliceLaw) := by
  let f : ℕ × SliceIndex → Fin 2 × ℕ × ℕ × ℕ :=
    fun z => (z.2.1,z.1,z.2.2.1,z.2.2.2)
  have hf : Function.Injective f := by
    rintro ⟨t,i,a,b⟩ ⟨u,j,c,d⟩ he
    simp only [f, Prod.mk.injEq] at he ⊢
    tauto
  have hm := product_injective_coordinates
    (fun k : Fin 2 × ℕ × ℕ × ℕ => betaMeasure ((k.2.2.1 : ℝ)+1) ((k.2.2.2 : ℝ)+1)) f hf
  have hc := Measure.infinitePi_map_curry (fun _ : ℕ =>
    fun k : SliceIndex => betaMeasure ((k.2.1 : ℝ)+1) ((k.2.2 : ℝ)+1))
  rw [← hm, Measure.map_map (by fun_prop) (by fun_prop)] at hc
  exact hc

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

abbrev PosteriorTable := Fin 2 × ℕ × ℕ × ℕ → ℝ
abbrev CoinStack := Fin 2 × ℕ → Bool
abbrev StackOmega := PosteriorTable × CoinStack

 noncomputable def stackCounts (ω : StackOmega) : ℕ → CountState
  | 0 => (0,0)
  | t+1 =>
    let c := stackCounts ω t
    let a := argmaxMin (fun i => ω.1 (i,t,c.1 i,c.2 i))
    updateCounts c a (ω.2 (a,c.1 a+c.2 a))

 noncomputable def stackArm (ω : StackOmega) (t : ℕ) : Fin 2 :=
  argmaxMin (fun i => ω.1 (i,t,(stackCounts ω t).1 i,(stackCounts ω t).2 i))

 noncomputable def stackCoin (ω : StackOmega) (t : ℕ) : Bool :=
  ω.2 (stackArm ω t,(stackCounts ω t).1 (stackArm ω t)+(stackCounts ω t).2 (stackArm ω t))

 noncomputable def stackHistory (ω : StackOmega) : History :=
  fun t => (stackArm ω t,stackCoin ω t)

 theorem stackCounts_succ (ω : StackOmega) (t : ℕ) :
    stackCounts ω (t+1) = updateCounts (stackCounts ω t) (stackArm ω t) (stackCoin ω t) := rfl

 theorem stackCounts_history (ω : StackOmega) (t : ℕ) :
    stackCounts ω t = historyCounts (stackHistory ω) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [stackCounts_succ,historyCounts]; simp only [stackHistory,ih]

 def stackEvent (h : History) (T : ℕ) : Set StackOmega :=
  {ω | ∀ t < T, stackHistory ω t = h t}

 theorem stackCounts_on_event {h : History} {ω : StackOmega} {T : ℕ}
    (he : ω ∈ stackEvent h T) {t : ℕ} (ht : t ≤ T) :
    stackCounts ω t = historyCounts h t := by
  rw [stackCounts_history]
  exact historyCounts_congr (fun u hu => he u (lt_of_lt_of_le hu ht))

 theorem stackCounts_measurable (t : ℕ) : Measurable (fun ω : StackOmega => stackCounts ω t) := by
  classical
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have ha : Measurable (fun ω : StackOmega => stackArm ω t) := by
      apply argmaxMin_two_measurable.comp
      apply measurable_pi_lambda
      intro i
      exact measurable_selected_table measurable_fst
        (measurable_const.prodMk (measurable_const.prodMk
          ((ih.fst.eval).prodMk (ih.snd.eval))))
    have hS := measurable_selected_table ih.fst ha
    have hF := measurable_selected_table ih.snd ha
    have hb : Measurable (fun ω : StackOmega => stackCoin ω t) := by
      change Measurable (fun ω : StackOmega => ω.2 (stackArm ω t,
        (stackCounts ω t).1 (stackArm ω t)+(stackCounts ω t).2 (stackArm ω t)))
      exact measurable_selected_table measurable_snd (ha.prodMk (hS.add hF))
    have hu : Measurable (fun z : CountState × (Fin 2 × Bool) =>
        updateCounts z.1 z.2.1 z.2.2) := measurable_of_countable _
    exact hu.comp (ih.prodMk (ha.prodMk hb))

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

 theorem stackArm_measurable (t : ℕ) : Measurable (fun ω : StackOmega => stackArm ω t) := by
  apply argmaxMin_two_measurable.comp
  apply measurable_pi_lambda
  intro i
  exact measurable_selected_table measurable_fst
    (measurable_const.prodMk (measurable_const.prodMk
      (((stackCounts_measurable t).fst.eval).prodMk ((stackCounts_measurable t).snd.eval))))

 theorem stackCoin_measurable (t : ℕ) : Measurable (fun ω : StackOmega => stackCoin ω t) := by
  have hs := measurable_selected_table (stackCounts_measurable t).fst (stackArm_measurable t)
  have hf := measurable_selected_table (stackCounts_measurable t).snd (stackArm_measurable t)
  exact measurable_selected_table (f := Prod.snd) measurable_snd
    ((stackArm_measurable t).prodMk (hs.add hf))

 theorem stackHistory_measurable (t : ℕ) : Measurable (fun ω : StackOmega => stackHistory ω t) :=
  (stackArm_measurable t).prodMk (stackCoin_measurable t)

 theorem nativeHistory_measurable (t : ℕ) : Measurable (fun ω : TSOmega 2 => nativeHistory ω t) := by
  have ha := arm_measurable t
  have hr : Measurable (fun ω : TSOmega 2 => ω.2.1 (tsArm ω t,t)) :=
    measurable_selected_table measurable_snd.fst (ha.prodMk measurable_const)
  have hv : Measurable (fun ω : TSOmega 2 => (ω.2.2 (tsArm ω t,t) : ℝ)) :=
    (measurable_selected_table measurable_snd.snd (ha.prodMk measurable_const)).subtype_val
  have hb : Measurable (fun ω : TSOmega 2 => tsCoin ω t) := by
    apply measurable_to_bool
    change MeasurableSet {ω : TSOmega 2 | decide ((ω.2.2 (tsArm ω t,t) : ℝ) < ω.2.1 (tsArm ω t,t)) = true}
    simpa only [decide_eq_true_eq] using measurableSet_lt hv hr
  exact ha.prodMk hb

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

 theorem calendar_counts_congr (W V : Calendar) (z : CoinStack) (t : ℕ)
    (h : ∀ u < t, W u = V u) :
    stackCounts (fromCalendar W,z) t = stackCounts (fromCalendar V,z) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hc := ih (fun u hu => h u (Nat.lt_succ_of_lt hu))
    have hw := h t (Nat.lt_succ_self t)
    simp only [stackCounts, fromCalendar, hc, hw]

 def prefixCalendar (t : ℕ) (W : (Finset.range t) → PosteriorSlice) : Calendar :=
  fun u => if h : u < t then W ⟨u,Finset.mem_range.mpr h⟩ else 0

 theorem prefixCalendar_measurable (t : ℕ) : Measurable (prefixCalendar t) := by
  apply measurable_pi_lambda
  intro u
  by_cases h : u < t
  · simpa only [prefixCalendar, dif_pos h] using
      (measurable_pi_apply (⟨u,Finset.mem_range.mpr h⟩ : Finset.range t))
  · simpa only [prefixCalendar, dif_neg h] using
      (measurable_const : Measurable (fun _ : (Finset.range t) → PosteriorSlice => (0 : PosteriorSlice)))

 theorem prefix_counts (W : Calendar) (z : CoinStack) (t : ℕ) :
    stackCounts (fromCalendar (prefixCalendar t (fun u => W u)),z) t =
      stackCounts (fromCalendar W,z) t := by
  apply calendar_counts_congr
  intro u hu
  simp only [prefixCalendar, dif_pos hu]

 theorem prefix_counts_measurable (z : CoinStack) (t : ℕ) :
    Measurable (fun W : (Finset.range t) → PosteriorSlice =>
      stackCounts (fromCalendar (prefixCalendar t W),z) t) := by
  apply (stackCounts_measurable t).comp
  apply Measurable.prodMk _ measurable_const
  apply measurable_pi_lambda
  intro k
  change Measurable (fun W : (Finset.range t) → PosteriorSlice =>
    prefixCalendar t W k.2.1 (k.1,k.2.2.1,k.2.2.2))
  exact (measurable_pi_apply (k.1,k.2.2.1,k.2.2.2)).comp
    ((measurable_pi_apply k.2.1).comp (prefixCalendar_measurable t))

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 noncomputable def stageCondition (z : CoinStack) (j L t : ℕ) (W : Calendar) : Prop :=
  let c := stackCounts (fromCalendar W,z) t
  c.1 0 + c.2 0 = j ∧ L ≤ c.1 1 + c.2 1

 noncomputable def stageEvent (z : CoinStack) (j L t : ℕ) : Set Calendar :=
  {W | stageCondition z j L t W ∧ ∀ u < t, ¬ stageCondition z j L u W}

 theorem stageCondition_congr (z : CoinStack) (j L t : ℕ) {W V : Calendar}
    (h : ∀ u < t, W u = V u) :
    stageCondition z j L t W ↔ stageCondition z j L t V := by
  unfold stageCondition
  rw [calendar_counts_congr W V z t h]

 theorem stageEvent_congr (z : CoinStack) (j L t : ℕ) {W V : Calendar}
    (h : ∀ u < t, W u = V u) :
    W ∈ stageEvent z j L t ↔ V ∈ stageEvent z j L t := by
  change (stageCondition z j L t W ∧ _) ↔ (stageCondition z j L t V ∧ _)
  rw [stageCondition_congr z j L t h]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  rw [stageCondition_congr z j L u (fun v hv => h v (lt_trans hv hu))]

 theorem stageEvent_disjoint (z : CoinStack) (j L : ℕ) {s t : ℕ} (hst : s ≠ t) :
    Disjoint (stageEvent z j L s) (stageEvent z j L t) := by
  rw [Set.disjoint_left]
  intro W hs ht
  rcases lt_or_gt_of_ne hst with h | h
  · exact ht.2 s h hs.1
  · exact hs.2 t h ht.1

 theorem stageCondition_measurable (z : CoinStack) (j L t : ℕ) :
    MeasurableSet {W | stageCondition z j L t W} := by
  have hc : Measurable (fun W : Calendar => stackCounts (fromCalendar W,z) t) := by
    apply (stackCounts_measurable t).comp
    apply Measurable.prodMk _ measurable_const
    apply measurable_pi_lambda
    intro k
    change Measurable (fun W : Calendar => W k.2.1 (k.1,k.2.2.1,k.2.2.2))
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  exact (measurableSet_eq_fun (hc.fst.eval.add hc.snd.eval) measurable_const).inter
    (measurableSet_le measurable_const (hc.fst.eval.add hc.snd.eval))

 theorem stageEvent_measurable (z : CoinStack) (j L t : ℕ) :
    MeasurableSet (stageEvent z j L t) := by
  unfold stageEvent
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (stageCondition_measurable z j L t).inter
    (MeasurableSet.iInter (fun u => MeasurableSet.iInter (fun (_ : u < t) =>
      (stageCondition_measurable z j L u).compl)))

 theorem stageEvent_prefix (z : CoinStack) (j L t : ℕ) (W : Calendar) :
    W ∈ stageEvent z j L t ↔
      prefixCalendar t (fun u => W u) ∈ stageEvent z j L t := by
  apply stageEvent_congr
  intro u hu
  simp only [prefixCalendar, dif_pos hu]

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

 def stackSuccessSum (z : CoinStack) (i : Fin 2) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, if z (i,k) then 1 else 0

 theorem stackSuccessSum_succ (z : CoinStack) (i : Fin 2) (n : ℕ) :
    stackSuccessSum z i (n+1) = stackSuccessSum z i n + if z (i,n) then 1 else 0 := by
  exact Finset.sum_range_succ _ _

 theorem stack_successes_sum (ω : StackOmega) (t : ℕ) (i : Fin 2) :
    (stackCounts ω t).1 i = stackSuccessSum ω.2 i
      ((stackCounts ω t).1 i + (stackCounts ω t).2 i) := by
  induction t with
  | zero => simp [stackCounts, stackSuccessSum]
  | succ t ih =>
    rw [stackCounts_succ]
    unfold updateCounts
    by_cases ha : stackArm ω t = i
    · subst i
      cases hb : stackCoin ω t
      · simp only [Bool.false_eq_true, ↓reduceIte, Function.update_self]
        rw [← Nat.add_assoc, stackSuccessSum_succ]
        change ω.2 (stackArm ω t, (stackCounts ω t).1 (stackArm ω t) + (stackCounts ω t).2 (stackArm ω t)) = false at hb
        simpa only [hb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using ih
      · simp only [↓reduceIte, Function.update_self]
        rw [Nat.add_right_comm _ 1, stackSuccessSum_succ]
        change ω.2 (stackArm ω t, (stackCounts ω t).1 (stackArm ω t) + (stackCounts ω t).2 (stackArm ω t)) = true at hb
        simp only [hb, ↓reduceIte]
        omega
    · cases hb : stackCoin ω t <;>
        simpa [hb, Function.update_of_ne (Ne.symm ha)] using ih

 theorem stack_successes_at_count (ω : StackOmega) (t j : ℕ) (i : Fin 2)
    (hj : (stackCounts ω t).1 i + (stackCounts ω t).2 i = j) :
    (stackCounts ω t).1 i = stackSuccessSum ω.2 i j := by
  rw [← hj]
  exact stack_successes_sum ω t i

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

 theorem stack_total (ω : StackOmega) (t : ℕ) (i : Fin 2) :
    (stackCounts ω t).1 i + (stackCounts ω t).2 i = historyPlays (stackHistory ω) t i := by
  rw [stackCounts_history, historyCounts_total]

 theorem historyPlays_two (h : History) (t : ℕ) :
    historyPlays h t 0 + historyPlays h t 1 = t := by
  induction t with
  | zero => simp [historyPlays]
  | succ t ih =>
    rw [historyPlays_succ,historyPlays_succ]
    have he : (h t).1 = 0 ∨ (h t).1 = 1 := by omega
    rcases he with he | he <;> simp [he] <;> omega

 theorem stack_counts_at_total (ω : StackOmega) (t j : ℕ) (i : Fin 2)
    (hj : historyPlays (stackHistory ω) t i = j) :
    (stackCounts ω t).1 i = stackSuccessSum ω.2 i j ∧
    (stackCounts ω t).2 i = j - stackSuccessSum ω.2 i j := by
  have ht := stack_total ω t i
  rw [hj] at ht
  have hs := stack_successes_at_count ω t j i ht
  exact ⟨hs, by omega⟩

 theorem stack_bad_implies_best_failure (W : Calendar) (z : CoinStack) (t j : ℕ)
    (hj : historyPlays (stackHistory (fromCalendar W,z)) t 0 = j)
    {y : ℝ}
    (ha : stackArm (fromCalendar W,z) t = 1)
    (hb : W t (1,(stackCounts (fromCalendar W,z) t).1 1,
      (stackCounts (fromCalendar W,z) t).2 1) ≤ y) :
    W t (0,stackSuccessSum z 0 j,j-stackSuccessSum z 0 j) ≤ y := by
  have hc := stack_counts_at_total (fromCalendar W,z) t j 0 hj
  have ht : W t (0,(stackCounts (fromCalendar W,z) t).1 0,
      (stackCounts (fromCalendar W,z) t).2 0) <
      W t (1,(stackCounts (fromCalendar W,z) t).1 1,
      (stackCounts (fromCalendar W,z) t).2 1) := by
    unfold stackArm at ha
    rw [argmaxMin_two] at ha
    split at ha
    · norm_num at ha
    · exact lt_of_not_ge ‹_›
  simpa only [hc.1,hc.2] using ht.le.trans hb

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

 theorem stageEvent_exists (z : CoinStack) (j L u : ℕ) (W : Calendar)
    (hu : stageCondition z j L u W) :
    ∃ t ≤ u, W ∈ stageEvent z j L t := by
  classical
  have hex : ∃ t, stageCondition z j L t W := ⟨u,hu⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hu, Nat.find_spec hex, ?_⟩
  intro v hv
  exact Nat.find_min hex hv

 theorem same_count_interval (h : History) {s u : ℕ} (_hsu : s ≤ u)
    (he : historyPlays h s 0 = historyPlays h u 0) :
    ∀ v ∈ Finset.Ico s u, (h v).1 = 1 := by
  intro v hv
  have hvb := Finset.mem_Ico.mp hv
  have h1 := historyPlays_mono h 0 hvb.1
  have h2 := historyPlays_mono h 0 (Nat.succ_le_of_lt hvb.2)
  change historyPlays h (v+1) 0 ≤ historyPlays h u 0 at h2
  dsimp only at h1
  rw [historyPlays_succ] at h2
  have ha : (h v).1 = 0 ∨ (h v).1 = 1 := by omega
  rcases ha with ha | ha
  · simp only [ha, ↓reduceIte] at h2
    omega
  · exact ha

 theorem same_count_between (h : History) {s u v : ℕ}
    (hsv : s ≤ v) (hvu : v ≤ u)
    (he : historyPlays h s 0 = historyPlays h u 0) :
    historyPlays h v 0 = historyPlays h u 0 := by
  have h1 := historyPlays_mono h 0 hsv
  have h2 := historyPlays_mono h 0 hvu
  dsimp only at h1 h2
  omega

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

 theorem stage_interval_failures (W : Calendar) (z : CoinStack) (j L t u : ℕ)
    (hte : W ∈ stageEvent z j L t) (htu : t ≤ u)
    (hju : historyPlays (stackHistory (fromCalendar W,z)) u 0 = j)
    (hau : stackArm (fromCalendar W,z) u = 1) {y : ℝ}
    (hgood : ∀ v ∈ Finset.Ico t (u+1),
      W v (1,(stackCounts (fromCalendar W,z) v).1 1,
        (stackCounts (fromCalendar W,z) v).2 1) ≤ y) :
    ∀ v ∈ Finset.Ico t (u+1),
      W v (0,stackSuccessSum z 0 j,j-stackSuccessSum z 0 j) ≤ y := by
  have hjt : historyPlays (stackHistory (fromCalendar W,z)) t 0 = j := by
    have he := hte.1.1
    change (stackCounts (fromCalendar W,z) t).1 0 +
      (stackCounts (fromCalendar W,z) t).2 0 = j at he
    rwa [stack_total] at he
  intro v hv
  have hvb := Finset.mem_Ico.mp hv
  have hvu : v ≤ u := by omega
  have hjv : historyPlays (stackHistory (fromCalendar W,z)) v 0 = j := by
    rw [← hju]
    exact same_count_between _ hvb.1 hvu (hjt.trans hju.symm)
  have hav : stackArm (fromCalendar W,z) v = 1 := by
    by_cases he : v = u
    · simpa only [he] using hau
    · exact same_count_interval _ htu (hjt.trans hju.symm) v
        (Finset.mem_Ico.mpr ⟨hvb.1, by omega⟩)
  exact stack_bad_implies_best_failure W z v j hjv hav (hgood v hv)

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

 noncomputable def goodCalendar (W : Calendar) (z : CoinStack) (L T : ℕ) (y : ℝ) : Prop :=
  ∀ v < T, L ≤ historyPlays (stackHistory (fromCalendar W,z)) v 1 →
    W v (1,(stackCounts (fromCalendar W,z) v).1 1,
      (stackCounts (fromCalendar W,z) v).2 1) ≤ y

 theorem bad_after_saturation_has_charge (W : Calendar) (z : CoinStack)
    (L T u : ℕ) {y : ℝ} (hgood : goodCalendar W z L T y) (hu : u < T)
    (hL : L ≤ historyPlays (stackHistory (fromCalendar W,z)) u 1)
    (ha : stackArm (fromCalendar W,z) u = 1) :
    ∃ j ≤ T, ∃ t < T, ∃ n < T, u = t+n ∧ W ∈ stageEvent z j L t ∧
      ∀ v ∈ Finset.Ico t (t+(n+1)),
        W v (0,stackSuccessSum z 0 j,j-stackSuccessSum z 0 j) ≤ y := by
  let h := stackHistory (fromCalendar W,z)
  let j := historyPlays h u 0
  have hjT : j ≤ T := by
    have hh : historyPlays h u 0 ≤ u :=
      (Finset.card_filter_le _ _).trans_eq (Finset.card_range u)
    omega
  have hc : stageCondition z j L u W := by
    change (stackCounts (fromCalendar W,z) u).1 0 +
        (stackCounts (fromCalendar W,z) u).2 0 = j ∧
      L ≤ (stackCounts (fromCalendar W,z) u).1 1 + (stackCounts (fromCalendar W,z) u).2 1
    rw [stack_total, stack_total]
    exact ⟨rfl,hL⟩
  obtain ⟨t,htu,hte⟩ := stageEvent_exists z j L u W hc
  refine ⟨j,hjT,t,by omega,u-t,by omega,by omega,hte,?_⟩
  have hLt : L ≤ historyPlays h t 1 := by
    have hh := hte.1.2
    change L ≤ (stackCounts (fromCalendar W,z) t).1 1 +
      (stackCounts (fromCalendar W,z) t).2 1 at hh
    rwa [stack_total] at hh
  have hf := stage_interval_failures W z j L t u hte htu rfl ha
    (fun v hv => hgood v (by have := (Finset.mem_Ico.mp hv).2; omega)
      (hLt.trans (historyPlays_mono h 1 (Finset.mem_Ico.mp hv).1)))
  have he : t+(u-t+1)=u+1 := by omega
  simpa only [he] using hf

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed
open Finset

 noncomputable def chargeSet (W : Calendar) (z : CoinStack) (L T : ℕ) (y : ℝ) :
    Finset (ℕ × ℕ × ℕ) := by
  classical
  exact ((range (T+1)).product ((range T).product (range T))).filter (fun a =>
    W ∈ stageEvent z a.1 L a.2.1 ∧ ∀ v ∈ Ico a.2.1 (a.2.1+(a.2.2+1)),
      W v (0,stackSuccessSum z 0 a.1,a.1-stackSuccessSum z 0 a.1) ≤ y)

 theorem saturated_count_le_charges (W : Calendar) (z : CoinStack) (L T : ℕ)
    {y : ℝ} (hgood : goodCalendar W z L T y) :
    ((range T).filter (fun u =>
      L ≤ historyPlays (stackHistory (fromCalendar W,z)) u 1 ∧
      stackArm (fromCalendar W,z) u = 1)).card ≤ (chargeSet W z L T y).card := by
  classical
  have hs : (range T).filter (fun u =>
      L ≤ historyPlays (stackHistory (fromCalendar W,z)) u 1 ∧
      stackArm (fromCalendar W,z) u = 1) ⊆
      (chargeSet W z L T y).image (fun a => a.2.1+a.2.2) := by
    intro u hu
    obtain ⟨hur,hL,ha⟩ := mem_filter.mp hu
    obtain ⟨j,hj,t,ht,n,hn,he,hte,hf⟩ :=
      bad_after_saturation_has_charge W z L T u hgood (mem_range.mp hur) hL ha
    apply mem_image.mpr
    refine ⟨(j,t,n),?_,he.symm⟩
    simp only [chargeSet, product_eq_sprod, mem_filter, mem_product, mem_range]
    exact ⟨⟨by omega,ht,hn⟩,hte,hf⟩
  exact (card_le_card hs).trans (card_image_le)

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory Set

 theorem prefix_future_factor {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (t n : ℕ)
    (A : Set ((Finset.range t) → E)) (hA : MeasurableSet A)
    (B : Set E) (hB : MeasurableSet B) :
    (Measure.infinitePi (fun _ : ℕ => P))
      {W | (fun i : Finset.range t => W i) ∈ A ∧ ∀ k ∈ Finset.Ico t (t+n), W k ∈ B} =
      (Measure.infinitePi (fun _ : ℕ => P)) {W | (fun i : Finset.range t => W i) ∈ A} * (P B)^n := by
  have hd : Disjoint (Finset.range t) (Finset.Ico t (t+n)) := by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    simp only [Finset.mem_range, Finset.mem_Ico] at hk hl
    omega
  let C : Set ((Finset.Ico t (t+n)) → E) := Set.univ.pi (fun _ => B)
  have hC : MeasurableSet C := MeasurableSet.univ_pi (fun _ => hB)
  have hh := product_fresh_event (fun _ : ℕ => P) (Finset.range t)
    (Finset.Ico t (t+n)) hd A C hA hC
  have he : {W : ℕ → E | (fun i : Finset.Ico t (t+n) => W i) ∈ C} =
      {W : ℕ → E | ∀ k ∈ Finset.Ico t (t+n), W k ∈ B} := by
    ext W
    simp [C]
  have hm := Measure.infinitePi_map_restrict (fun _ : ℕ => P) (I := Finset.Ico t (t+n))
  have hv := congrArg (fun μ : Measure ((Finset.Ico t (t+n)) → E) => μ C) hm
  rw [Measure.map_apply (by fun_prop) hC, Measure.pi_pi] at hv
  simp only [C, Finset.prod_const] at hv
  have hs : {W : ℕ → E | (fun i : Finset.range t => W i) ∈ A ∧
      (fun i : Finset.Ico t (t+n) => W i) ∈ C} =
      {W : ℕ → E | (fun i : Finset.range t => W i) ∈ A ∧
      ∀ k ∈ Finset.Ico t (t+n), W k ∈ B} := by
    ext W; simp [C]
  have hv' : (Measure.infinitePi (fun _ : ℕ => P))
      {W | (fun i : Finset.Ico t (t+n) => W i) ∈ C} = (P B)^n := by
    change (Measure.infinitePi (fun _ : ℕ => P))
      {W | (fun i : Finset.Ico t (t+n) => W i) ∈ C} =
      (P B)^((Finset.univ : Finset (Finset.Ico t (t+n))).card) at hv
    simpa only [Finset.card_univ, Fintype.card_coe, Nat.card_Ico, Nat.add_sub_cancel_left] using hv
  rw [hs, hv'] at hh
  exact hh

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 theorem stage_future_factor (z : CoinStack) (j L t n : ℕ)
    (B : Set PosteriorSlice) (hB : MeasurableSet B) :
    (Measure.infinitePi (fun _ : ℕ => sliceLaw))
      {W | W ∈ stageEvent z j L t ∧ ∀ k ∈ Finset.Ico t (t+n), W k ∈ B} =
    (Measure.infinitePi (fun _ : ℕ => sliceLaw)) (stageEvent z j L t) * (sliceLaw B)^n := by
  let A : Set ((Finset.range t) → PosteriorSlice) :=
    (prefixCalendar t) ⁻¹' stageEvent z j L t
  have hA : MeasurableSet A :=
    (stageEvent_measurable z j L t).preimage (prefixCalendar_measurable t)
  have he := prefix_future_factor sliceLaw t n A hA B hB
  have hmem (W : Calendar) : (fun i : Finset.range t => W i) ∈ A ↔ W ∈ stageEvent z j L t :=
    (stageEvent_prefix z j L t W).symm
  simpa only [hmem, Set.ofPred_mem_eq] using he

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory Set

 theorem stage_mass_le_one (z : CoinStack) (j L T : ℕ) :
    ∑ t ∈ Finset.range T,
      (Measure.infinitePi (fun _ : ℕ => sliceLaw)).real (stageEvent z j L t) ≤ 1 := by
  have hd : (Finset.range T : Set ℕ).PairwiseDisjoint (stageEvent z j L) := by
    intro a ha b hb hab
    exact stageEvent_disjoint z j L hab
  have hm : ∀ t ∈ Finset.range T, MeasurableSet (stageEvent z j L t) :=
    fun t _ => stageEvent_measurable z j L t
  rw [← measureReal_biUnion_finset hd hm]
  exact measureReal_le_one

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open Finset

lemma exp_neg_gap {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    a / 2 ≤ 1 - Real.exp (-a) := by
  have he : 1 + a ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  have hinv : Real.exp (-a) ≤ 1 / (1 + a) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by positivity) he
  have hfrac : a / 2 ≤ 1 - 1 / (1 + a) := by
    have h : 1 / (1 + a) ≤ 1 - a / 2 :=
      (div_le_iff₀ (by positivity : 0 < 1 + a)).mpr (by nlinarith)
    linarith
  linarith

lemma geometric_prefix_bound {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (J : ℕ) :
    ∑ j ∈ range J, r ^ j ≤ 1 / (1 - r) := by
  have h := hasSum_geometric_of_lt_one hr hr1
  simpa only [one_div] using sum_le_hasSum (range J) (fun j _ => pow_nonneg hr j) h

lemma geometric_weighted_prefix_bound {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (J : ℕ) :
    ∑ j ∈ range J, (j + 1 : ℝ) * r ^ j ≤ 1 / (1 - r) ^ 2 := by
  have hnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hr1
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).add
    (hasSum_geometric_of_lt_one hr hr1)
  have he : r / (1 - r) ^ 2 + 1 / (1 - r) = 1 / (1 - r) ^ 2 := by
    field_simp [ne_of_gt (sub_pos.mpr hr1)]
    ring
  simp only [← one_div] at h
  rw [he] at h
  have hh := sum_le_hasSum (range J) (fun j _ => by positivity) h
  convert hh using 1 <;> try rfl
  apply sum_congr rfl
  intro j _
  ring

lemma exponential_prefix_bound {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (J : ℕ) :
    ∑ j ∈ range J, Real.exp (-a * j) ≤ 2 / a := by
  have hr0 := (Real.exp_pos (-a)).le
  have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgap := exp_neg_gap ha ha1
  have he : (fun j : ℕ => Real.exp (-a * j)) = (fun j => Real.exp (-a) ^ j) := by
    funext j
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  apply (geometric_prefix_bound hr0 hr1 J).trans
  have hh := one_div_le_one_div_of_le (by positivity : 0 < a / 2) hgap
  simpa using hh

lemma exponential_weighted_prefix_bound {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (J : ℕ) :
    ∑ j ∈ range J, (j + 1 : ℝ) * Real.exp (-a * j) ≤ 4 / a ^ 2 := by
  have hr0 := (Real.exp_pos (-a)).le
  have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgap := exp_neg_gap ha ha1
  have he (j : ℕ) : Real.exp (-a * j) = Real.exp (-a) ^ j := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [he]
  apply (geometric_weighted_prefix_bound hr0 hr1 J).trans
  have hs : (a / 2) ^ 2 ≤ (1 - Real.exp (-a)) ^ 2 := by
    nlinarith [sub_pos.mpr hr1]
  have hh := one_div_le_one_div_of_le (by positivity : 0 < (a / 2) ^ 2) hs
  convert hh using 1
  ring

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory Set Finset

 theorem stage_future_real (z : CoinStack) (j L t n : ℕ)
    (B : Set PosteriorSlice) (hB : MeasurableSet B) :
    (Measure.infinitePi (fun _ : ℕ => sliceLaw)).real
      {W | W ∈ stageEvent z j L t ∧ ∀ k ∈ Finset.Ico t (t+n), W k ∈ B} =
    (Measure.infinitePi (fun _ : ℕ => sliceLaw)).real (stageEvent z j L t) * (sliceLaw.real B)^n := by
  unfold Measure.real
  rw [stage_future_factor z j L t n B hB, ENNReal.toReal_mul, ENNReal.toReal_pow]

 theorem geometric_positive_prefix {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ n ∈ range N, r^(n+1) ≤ r/(1-r) := by
  simp only [pow_succ, ← sum_mul]
  calc
    (∑ n ∈ range N, r^n) * r ≤ (1/(1-r))*r :=
      mul_le_mul_of_nonneg_right (geometric_prefix_bound hr hr1 N) hr
    _ = r/(1-r) := by ring

 theorem stage_geometric_budget (z : CoinStack) (j L T N : ℕ)
    (B : Set PosteriorSlice) (hB : MeasurableSet B) (hr : sliceLaw.real B < 1) :
    (∑ t ∈ range T, ∑ n ∈ range N,
      (Measure.infinitePi (fun _ : ℕ => sliceLaw)).real
        {W | W ∈ stageEvent z j L t ∧ ∀ k ∈ Finset.Ico t (t+(n+1)), W k ∈ B}) ≤
      sliceLaw.real B / (1-sliceLaw.real B) := by
  simp_rw [stage_future_real z j L _ _ B hB, ← mul_sum]
  rw [← sum_mul]
  have hm := stage_mass_le_one z j L T
  have hg := geometric_positive_prefix (measureReal_nonneg) hr N
  have hs : 0 ≤ ∑ n ∈ range N, (sliceLaw.real B)^(n+1) :=
    sum_nonneg (fun n _ => pow_nonneg measureReal_nonneg _)
  calc
    _ ≤ 1 * (∑ n ∈ range N, (sliceLaw.real B)^(n+1)) := mul_le_mul_of_nonneg_right hm hs
    _ ≤ _ := by simpa only [one_mul] using hg

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open MeasureTheory ProbabilityTheory AgrawalGoyalTS.TwoArmed Finset

lemma binomPMF_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n k : ℕ) :
    0 ≤ binomPMF n p k := by
  unfold binomPMF
  positivity

lemma binomPMF_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {n k : ℕ}
    (hk : k ≤ n) : 0 < binomPMF n p k := by
  unfold binomPMF
  have hc : 0 < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  positivity

lemma binomPMF_sum (n : ℕ) (p : ℝ) :
    ∑ k ∈ range (n + 1), binomPMF n p k = 1 := by
  have h := add_pow p (1 - p) n
  have he : p + (1 - p) = 1 := by ring
  rw [he, one_pow] at h
  calc
    _ = ∑ k ∈ range (n + 1), p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ) := by
      apply sum_congr rfl
      intro k _
      unfold binomPMF
      ring
    _ = 1 := h.symm

lemma binomCDF_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) (x : ℝ) :
    0 ≤ binomCDF n p x := by
  unfold binomCDF
  exact sum_nonneg fun k _ => binomPMF_nonneg hp hp1 n k

lemma binomCDF_le_one {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) (x : ℝ) :
    binomCDF n p x ≤ 1 := by
  rw [← binomPMF_sum n p]
  unfold binomCDF
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  intro k _ _
  exact binomPMF_nonneg hp hp1 n k

lemma binomCDF_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (n : ℕ) {x : ℝ}
    (hx : 0 ≤ x) : 0 < binomCDF n p x := by
  unfold binomCDF
  apply sum_pos'
  · intro k _
    exact binomPMF_nonneg hp.le hp1.le n k
  · refine ⟨0, ?_, binomPMF_pos hp hp1 (Nat.zero_le n)⟩
    simp [hx]

lemma binomCDF_mono {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    Monotone (binomCDF n p) := by
  intro x y hxy
  unfold binomCDF
  apply sum_le_sum_of_subset_of_nonneg
  · intro k hk
    rcases mem_filter.mp hk with ⟨hk, hx⟩
    exact mem_filter.mpr ⟨hk, hx.trans hxy⟩
  · intro k _ _
    exact binomPMF_nonneg hp hp1 n k

lemma posteriorOdds_nonneg {y : ℝ} (hy : 0 < y) (hy1 : y < 1) (j s : ℕ) :
    0 ≤ posteriorOdds j s y := by
  have hq := binomCDF_pos hy hy1 (j + 1) (show 0 ≤ (s : ℝ) by positivity)
  have hq1 := binomCDF_le_one hy.le hy1.le (j + 1) s
  unfold posteriorOdds
  have : 1 ≤ (binomCDF (j + 1) y s)⁻¹ := (one_le_inv₀ hq).mpr hq1
  linarith

lemma binomExpectation_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) {f : ℕ → ℝ} (hf : ∀ k ≤ n, 0 ≤ f k) :
    0 ≤ binomExpectation n p f := by
  unfold binomExpectation
  apply sum_nonneg
  intro k hk
  exact mul_nonneg (binomPMF_nonneg hp hp1 n k) (hf k (Nat.le_of_lt_succ (mem_range.mp hk)))

lemma binomExpectation_integral (n : ℕ) (p : unitInterval) (f : ℕ → ℝ) :
    binomExpectation n p f = ∫ k, f k ∂(ProbabilityTheory.binomial n p) := by
  rw [ProbabilityTheory.integral_binomial]
  have hs : Finset.Iic n = range (n + 1) := by
    ext k
    simp
  rw [hs]
  rfl

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open AgrawalGoyalTS.TwoArmed Finset

lemma binomPMF_mul_succ (n k : ℕ) (p : ℝ) :
    (k + 1 : ℝ) * binomPMF (n + 1) p (k + 1) =
      (n + 1 : ℝ) * p * binomPMF n p k := by
  have hc : (n + 1 : ℝ) * (n.choose k : ℝ) =
      ((n + 1).choose (k + 1) : ℝ) * (k + 1 : ℝ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  unfold binomPMF
  rw [Nat.add_sub_add_right, pow_succ]
  calc
    _ = (((n + 1).choose (k + 1) : ℝ) * (k + 1 : ℝ)) *
        (p ^ k * p * (1 - p) ^ (n - k)) := by ring
    _ = _ := by rw [← hc]; ring

lemma binom_mean (n : ℕ) (p : ℝ) :
    binomExpectation n p (fun k => (k : ℝ)) = n * p := by
  cases n with
  | zero => simp [binomExpectation, binomPMF]
  | succ n =>
    unfold binomExpectation
    rw [sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, add_zero, Nat.cast_add, Nat.cast_one]
    have he : (∑ k ∈ range (n + 1), binomPMF (n + 1) p (k + 1) * (k + 1 : ℝ)) =
        (n + 1 : ℝ) * p * ∑ k ∈ range (n + 1), binomPMF n p k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      simpa only [mul_comm] using binomPMF_mul_succ n k p
    rw [he, binomPMF_sum, mul_one]

lemma binom_factorial_second (n : ℕ) (p : ℝ) :
    binomExpectation n p (fun k => (k : ℝ) * ((k : ℝ) - 1)) =
      (n : ℝ) * ((n : ℝ) - 1) * p ^ 2 := by
  cases n with
  | zero => simp [binomExpectation, binomPMF]
  | succ n =>
    unfold binomExpectation
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.cast_add, Nat.cast_one]
    have he : (∑ k ∈ range (n + 1),
        binomPMF (n + 1) p (k + 1) * ((k + 1 : ℝ) * ((k + 1 : ℝ) - 1))) =
        ((n + 1 : ℝ) * p) * binomExpectation n p (fun k => (k : ℝ)) := by
      unfold binomExpectation
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      calc
        _ = ((k + 1 : ℝ) * binomPMF (n + 1) p (k + 1)) * k := by ring
        _ = _ := by rw [binomPMF_mul_succ]; ring
    rw [he, binom_mean]
    ring

lemma binom_second_moment (n : ℕ) (p : ℝ) :
    binomExpectation n p (fun k => (k : ℝ) ^ 2) =
      (n : ℝ) * ((n : ℝ) - 1) * p ^ 2 + n * p := by
  have he : binomExpectation n p (fun k => (k : ℝ) ^ 2) =
      binomExpectation n p (fun k => (k : ℝ) * ((k : ℝ) - 1)) +
      binomExpectation n p (fun k => (k : ℝ)) := by
    unfold binomExpectation
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    ring
  rw [he, binom_factorial_second, binom_mean]

lemma binom_centered_second (n : ℕ) (p : ℝ) :
    binomExpectation n p (fun k => ((k : ℝ) - n * p) ^ 2) = n * p * (1 - p) := by
  have he : binomExpectation n p (fun k => ((k : ℝ) - n * p) ^ 2) =
      binomExpectation n p (fun k => (k : ℝ) ^ 2) -
      2 * n * p * binomExpectation n p (fun k => (k : ℝ)) +
      (n * p) ^ 2 * (∑ k ∈ range (n + 1), binomPMF n p k) := by
    unfold binomExpectation
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    ring
  rw [he, binom_second_moment, binom_mean, binomPMF_sum]
  ring

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open AgrawalGoyalTS.TwoArmed Finset

lemma binomPMF_deriv_zero (n : ℕ) (x : ℝ) :
    HasDerivAt (fun p => binomPMF (n + 1) p 0)
      (-(n + 1 : ℝ) * (1 - x) ^ n) x := by
  have hd := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).pow (n + 1)
  convert hd using 1 <;> try rfl
  · funext p
    simp [binomPMF]
  · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Pi.sub_apply, id_eq,
      zero_sub, mul_neg, mul_one]
    ring


lemma binomPMF_deriv_succ (n k : ℕ) (hk : k < n) (x : ℝ) :
    HasDerivAt (fun p => binomPMF (n + 1) p (k + 1))
      ((n + 1 : ℝ) * (binomPMF n x k - binomPMF n x (k + 1))) x := by
  have hd := (((hasDerivAt_id x).pow (k + 1)).mul
    (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).pow (n - k))).const_mul
      ((n + 1).choose (k + 1) : ℝ)
  have hc1 : ((n + 1).choose (k + 1) : ℝ) * (k + 1 : ℝ) =
      (n + 1 : ℝ) * (n.choose k : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq n k).symm
  have hc2 : ((n + 1).choose (k + 1) : ℝ) * ((n : ℝ) - k) =
      (n + 1 : ℝ) * (n.choose (k + 1) : ℝ) := by
    have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_mul_succ_eq n (k + 1))
    have he : n + 1 - (k + 1) = n - k := by omega
    rw [he] at h
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk.le, mul_comm] using h.symm
  convert hd using 1 <;> try rfl
  · funext p
    simp only [binomPMF, Nat.add_sub_add_right, mul_assoc, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
  · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Nat.cast_sub hk.le,
      zero_sub, mul_neg, mul_one, Nat.sub_sub,
      Pi.pow_apply, Pi.sub_apply, id_eq]
    unfold binomPMF
    rw [pow_succ]
    calc
      _ = ((n + 1 : ℝ) * (n.choose k : ℝ)) * x ^ k * (1 - x) ^ (n - k) -
          ((n + 1 : ℝ) * (n.choose (k + 1) : ℝ)) * (x ^ k * x) *
            (1 - x) ^ (n - (k + 1)) := by ring
      _ = _ := by rw [← hc1, ← hc2]; ring

lemma binom_partial_derivative (n s : ℕ) (hs : s ≤ n) (x : ℝ) :
    HasDerivAt (fun p => ∑ k ∈ range (s + 1), binomPMF (n + 1) p k)
      (-(n + 1 : ℝ) * binomPMF n x s) x := by
  induction s with
  | zero => simpa [binomPMF] using binomPMF_deriv_zero n x
  | succ s ih =>
    have h1 := ih (by omega)
    have h2 := binomPMF_deriv_succ n s (by omega) x
    have hd := h1.add h2
    convert hd using 1 <;> try rfl
    · funext p
      exact sum_range_succ _ _
    · ring

lemma binomCDF_eq_partial (n s : ℕ) (hs : s ≤ n) (p : ℝ) :
    binomCDF (n + 1) p s = ∑ k ∈ range (s + 1), binomPMF (n + 1) p k := by
  unfold binomCDF
  congr 1
  ext k
  simp only [mem_filter, mem_range, Nat.cast_le]
  omega

lemma binomCDF_derivative (n s : ℕ) (hs : s ≤ n) (x : ℝ) :
    HasDerivAt (fun p => binomCDF (n + 1) p s)
      (-(n + 1 : ℝ) * binomPMF n x s) x := by
  have he : (fun p => binomCDF (n + 1) p s) =
      (fun p => ∑ k ∈ range (s + 1), binomPMF (n + 1) p k) :=
    funext (binomCDF_eq_partial n s hs)
  rw [he]
  exact binom_partial_derivative n s hs x

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open MeasureTheory ProbabilityTheory AgrawalGoyalTS.TwoArmed

lemma beta_nat_normalizer (n s : ℕ) (hs : s ≤ n) :
    1 / beta ((s : ℝ) + 1) ((n - s : ℕ) + 1) =
      (n + 1 : ℝ) * (n.choose s : ℝ) := by
  have he : (s : ℝ) + 1 + ((n - s : ℕ) + 1) = ((n + 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hs]
    push_cast
    ring
  rw [beta, he, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    Real.Gamma_nat_eq_factorial]
  have hsf : (s.factorial : ℝ) ≠ 0 := by positivity
  have hnf : ((n - s).factorial : ℝ) ≠ 0 := by positivity
  have hc : (n.choose s : ℝ) * (s.factorial : ℝ) * ((n - s).factorial : ℝ) =
      (n.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hs
  rw [one_div_div]
  apply (div_eq_iff (mul_ne_zero hsf hnf)).mpr
  rw [Nat.factorial_succ]
  push_cast
  nlinarith [hc]

lemma beta_density_polynomial (n s : ℕ) (hs : s ≤ n) {x : ℝ}
    (hx : 0 < x) (hx1 : x < 1) :
    betaPDFReal ((s : ℝ) + 1) ((n - s : ℕ) + 1) x =
      (n + 1 : ℝ) * binomPMF n x s := by
  rw [betaPDFReal, if_pos ⟨hx, hx1⟩]
  simp only [add_sub_cancel_right, Real.rpow_natCast]
  rw [beta_nat_normalizer n s hs]
  unfold binomPMF
  ring

lemma beta_density_nonneg (a b : ℕ) (x : ℝ) :
    0 ≤ betaPDFReal ((a : ℝ) + 1) ((b : ℝ) + 1) x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact (betaPDFReal_pos hx.1 hx.2 (by positivity) (by positivity)).le
  · simp [betaPDFReal, hx]

lemma beta_measure_real_integral (a b : ℕ) (S : Set ℝ) (hS : MeasurableSet S) :
    (betaMeasure ((a : ℝ) + 1) ((b : ℝ) + 1)).real S =
      ∫ x in S, betaPDFReal ((a : ℝ) + 1) ((b : ℝ) + 1) x := by
  rw [measureReal_def, betaMeasure, withDensity_apply _ hS]
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (beta_density_nonneg a b))
    ((stronglyMeasurable_betaPDFReal _ _).aestronglyMeasurable)).symm

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open MeasureTheory ProbabilityTheory AgrawalGoyalTS.TwoArmed Set Finset

lemma binomCDF_one (n s : ℕ) (hs : s ≤ n) : binomCDF (n + 1) 1 s = 0 := by
  rw [binomCDF_eq_partial n s hs]
  apply sum_eq_zero
  intro k hk
  have hkn : k < n + 1 := by have := mem_range.mp hk; omega
  have hz : n + 1 - k ≠ 0 := by omega
  simp [binomPMF, zero_pow hz]

lemma beta_tail_polynomial_integral (n s : ℕ) (hs : s ≤ n) {y : ℝ}
    (hy : 0 < y) (hy1 : y < 1) :
    (betaMeasure ((s : ℝ) + 1) ((n - s : ℕ) + 1)).real (Ioi y) =
      ∫ x in y..1, (n + 1 : ℝ) * binomPMF n x s := by
  rw [beta_measure_real_integral _ _ _ measurableSet_Ioi,
    intervalIntegral.integral_of_le hy1.le, integral_Ioc_eq_integral_Ioo]
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hxy : y < x
  · by_cases hx1 : x < 1
    · rw [Set.indicator_of_mem (show x ∈ Ioi y from hxy),
        Set.indicator_of_mem (show x ∈ Ioo y 1 from ⟨hxy, hx1⟩)]
      exact beta_density_polynomial n s hs (hy.trans hxy) hx1
    · rw [Set.indicator_of_mem (show x ∈ Ioi y from hxy)]
      rw [Set.indicator_of_notMem (show x ∉ Ioo y 1 from fun h => hx1 h.2)]
      simp [betaPDFReal, hx1]
  · rw [Set.indicator_of_notMem (show x ∉ Ioi y from hxy),
      Set.indicator_of_notMem (show x ∉ Ioo y 1 from fun h => hxy h.1)]

lemma beta_binomial_tail (n s : ℕ) (hs : s ≤ n) {y : ℝ}
    (hy : 0 < y) (hy1 : y < 1) :
    (betaMeasure ((s : ℝ) + 1) ((n - s : ℕ) + 1)).real (Ioi y) =
      binomCDF (n + 1) y s := by
  rw [beta_tail_polynomial_integral n s hs hy hy1]
  have hd (x : ℝ) : HasDerivAt (fun p => -binomCDF (n + 1) p s)
      ((n + 1 : ℝ) * binomPMF n x s) x := by
    have hh := (binomCDF_derivative n s hs x).neg
    simp only [neg_mul, neg_neg] at hh
    convert hh using 1 <;> rfl
  have hc : Continuous (fun x : ℝ => (n + 1 : ℝ) * binomPMF n x s) := by
    unfold binomPMF
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x) (hc.intervalIntegrable y 1), binomCDF_one n s hs]
  ring

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 theorem slice_coordinate_law (i : Fin 2) (s f : ℕ) :
    sliceLaw.map (fun W => W (i,s,f)) = betaMeasure ((s : ℝ)+1) ((f : ℝ)+1) := by
  exact Measure.infinitePi_map_eval _ _

 theorem slice_failure_probability (i : Fin 2) (j s : ℕ) (hs : s ≤ j)
    {y : ℝ} (hy : 0 < y) (hy1 : y < 1) :
    sliceLaw.real {W | W (i,s,j-s) ≤ y} = 1 - binomCDF (j+1) y s := by
  have ht : sliceLaw.real {W | y < W (i,s,j-s)} = binomCDF (j+1) y s := by
    rw [← beta_binomial_tail j s hs hy hy1, ← slice_coordinate_law i s (j-s)]
    simp only [Measure.real]
    rw [Measure.map_apply (measurable_pi_apply _) measurableSet_Ioi]
    rfl
  have he : {W : PosteriorSlice | W (i,s,j-s) ≤ y} =
      {W : PosteriorSlice | y < W (i,s,j-s)}ᶜ := by
    ext W; simp
  rw [he, measureReal_compl (measurableSet_lt measurable_const (measurable_pi_apply _)), ht]
  simp

end ThompsonSamplingProof


namespace ThompsonSamplingProof

 theorem stackSuccessSum_le (z : CoinStack) (i : Fin 2) (j : ℕ) :
    stackSuccessSum z i j ≤ j := by
  induction j with
  | zero => simp [stackSuccessSum]
  | succ j ih =>
    rw [stackSuccessSum_succ]
    split <;> omega

 theorem stackSuccessSum_measurable (i : Fin 2) (j : ℕ) :
    Measurable (fun z : CoinStack => stackSuccessSum z i j) := by
  apply Finset.measurable_sum
  intro k _
  exact (measurable_of_countable (fun b : Bool => if b then (1 : ℕ) else 0)).comp
    (measurable_pi_apply (i,k))

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory Set Finset

 noncomputable def eventCount {Ω ι : Type*} (I : Finset ι) (A : ι → Set Ω) (ω : Ω) : ℝ := by
  classical
  exact ∑ i ∈ I, if ω ∈ A i then 1 else 0

 theorem eventCount_measurable {Ω ι : Type*} [MeasurableSpace Ω]
    (I : Finset ι) (A : ι → Set Ω) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    Measurable (eventCount I A) := by
  classical
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.ite (hA i hi) measurable_const

 theorem eventCount_integrable {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (I : Finset ι) (A : ι → Set Ω) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    Integrable (eventCount I A) μ := by
  classical
  apply integrable_finsetSum
  intro i hi
  exact (integrable_const (1 : ℝ)).indicator (hA i hi)

 theorem eventCount_integral {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (I : Finset ι) (A : ι → Set Ω) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    (∫ ω, eventCount I A ω ∂μ) = ∑ i ∈ I, μ.real (A i) := by
  classical
  unfold eventCount
  change (∫ ω, ∑ i ∈ I, (A i).indicator (fun _ => (1 : ℝ)) ω ∂μ) = _
  rw [integral_finsetSum I (fun i hi => (integrable_const (1 : ℝ)).indicator (hA i hi))]
  apply sum_congr rfl
  intro i hi
  change (∫ ω, (A i).indicator (fun _ => (1 : ℝ)) ω ∂μ) = _
  rw [integral_indicator (hA i hi)]
  simp

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set Finset

 noncomputable def chargeEvent (z : CoinStack) (j L t n : ℕ) (y : ℝ) : Set Calendar :=
  {W | W ∈ stageEvent z j L t ∧ ∀ v ∈ Finset.Ico t (t+(n+1)),
    W v (0,stackSuccessSum z 0 j,j-stackSuccessSum z 0 j) ≤ y}

 theorem chargeEvent_measurable (z : CoinStack) (j L t n : ℕ) (y : ℝ) :
    MeasurableSet (chargeEvent z j L t n y) := by
  unfold chargeEvent
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply (stageEvent_measurable z j L t).inter
  apply MeasurableSet.iInter
  intro v
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le ((measurable_pi_apply _).comp (measurable_pi_apply v)) measurable_const

 noncomputable def stageCost (z : CoinStack) (j L T : ℕ) (y : ℝ) : Calendar → ℝ :=
  eventCount ((range T).product (range T)) (fun a => chargeEvent z j L a.1 a.2 y)

 theorem stageCost_integrable (z : CoinStack) (j L T : ℕ) (y : ℝ) :
    Integrable (stageCost z j L T y) (Measure.infinitePi (fun _ : ℕ => sliceLaw)) :=
  eventCount_integrable _ _ _ (fun a _ => chargeEvent_measurable z j L a.1 a.2 y)

 theorem stageCost_expectation (z : CoinStack) (j L T : ℕ) {y : ℝ}
    (hy : 0 < y) (hy1 : y < 1) :
    (∫ W, stageCost z j L T y W ∂Measure.infinitePi (fun _ : ℕ => sliceLaw)) ≤
      posteriorOdds j (stackSuccessSum z 0 j) y := by
  let B : Set PosteriorSlice := {w | w (0,stackSuccessSum z 0 j,j-stackSuccessSum z 0 j) ≤ y}
  have hB : MeasurableSet B := measurableSet_le (measurable_pi_apply _) measurable_const
  have hp := slice_failure_probability 0 j (stackSuccessSum z 0 j)
    (stackSuccessSum_le z 0 j) hy hy1
  have hq := binomCDF_pos hy hy1 (j+1) (show 0 ≤ (stackSuccessSum z 0 j : ℝ) by positivity)
  have hr : sliceLaw.real B < 1 := by dsimp [B]; rw [hp]; linarith
  have hb := stage_geometric_budget z j L T T B hB hr
  rw [show stageCost z j L T y = eventCount ((range T).product (range T))
    (fun a => chargeEvent z j L a.1 a.2 y) from rfl,
    eventCount_integral _ _ _ (fun a _ => chargeEvent_measurable z j L a.1 a.2 y), product_eq_sprod, sum_product]
  change (∑ t ∈ range T, ∑ n ∈ range T,
    (Measure.infinitePi (fun _ : ℕ => sliceLaw)).real (chargeEvent z j L t n y)) ≤ _
  calc
    _ ≤ sliceLaw.real B / (1-sliceLaw.real B) := hb
    _ = posteriorOdds j (stackSuccessSum z 0 j) y := by
      change sliceLaw.real {w | w (0,stackSuccessSum z 0 j,j-stackSuccessSum z 0 j) ≤ y} /
        (1-sliceLaw.real {w | w (0,stackSuccessSum z 0 j,j-stackSuccessSum z 0 j) ≤ y}) = _
      rw [hp]
      unfold posteriorOdds
      field_simp [hq.ne']
      ring

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open Finset

 theorem initial_pull_count_le (h : History) (T L : ℕ) (i : Fin 2) :
    ((range T).filter (fun u => (h u).1 = i ∧ historyPlays h u i < L)).card ≤ L := by
  classical
  let A := (range T).filter (fun u => (h u).1 = i ∧ historyPlays h u i < L)
  have hi : Set.InjOn (fun u => historyPlays h u i) A := by
    intro u hu v hv he
    have hau := (mem_filter.mp hu).2.1
    have hav := (mem_filter.mp hv).2.1
    apply history_pull_index_injective h
    simp only [hau,hav,Prod.mk.injEq,true_and]
    exact he
  have hs : A.image (fun u => historyPlays h u i) ⊆ range L := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hv
    exact mem_range.mpr (mem_filter.mp hu).2.2
  calc
    _ = (A.image (fun u => historyPlays h u i)).card := (card_image_of_injOn hi).symm
    _ ≤ (range L).card := card_le_card hs
    _ = L := card_range L

 theorem historyPlays_split (h : History) (T L : ℕ) (i : Fin 2) :
    historyPlays h T i =
    ((range T).filter (fun u => (h u).1 = i ∧ historyPlays h u i < L)).card +
    ((range T).filter (fun u => L ≤ historyPlays h u i ∧ (h u).1 = i)).card := by
  classical
  have he := card_filter_add_card_filter_not (s := (range T).filter (fun u => (h u).1 = i))
    (fun u => historyPlays h u i < L)
  have h1 : ((range T).filter (fun u => (h u).1 = i)).filter
      (fun u => historyPlays h u i < L) =
      (range T).filter (fun u => (h u).1 = i ∧ historyPlays h u i < L) := by
    ext u; simp only [mem_filter]; tauto
  have h2 : ((range T).filter (fun u => (h u).1 = i)).filter
      (fun u => ¬ historyPlays h u i < L) =
      (range T).filter (fun u => L ≤ historyPlays h u i ∧ (h u).1 = i) := by
    ext u; simp only [mem_filter, not_lt]; tauto
  rw [h1,h2] at he
  exact he.symm

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open scoped Classical
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Finset

 theorem chargeSet_card (W : Calendar) (z : CoinStack) (L T : ℕ) (y : ℝ) :
    ((chargeSet W z L T y).card : ℝ) = ∑ j ∈ range (T+1), stageCost z j L T y W := by
  classical
  unfold chargeSet stageCost eventCount chargeEvent
  rw [card_eq_sum_ones]
  simp only [sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    product_eq_sprod, sum_product, Set.mem_ofPred_eq]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro n _
  split_ifs <;> rfl

 theorem stageCost_nonneg (W : Calendar) (z : CoinStack) (j L T : ℕ) (y : ℝ) :
    0 ≤ stageCost z j L T y W := by
  classical
  unfold stageCost eventCount
  exact sum_nonneg (fun _ _ => by split <;> norm_num)

 theorem pathwise_pull_budget (W : Calendar) (z : CoinStack) (L T : ℕ) (y : ℝ) :
    (historyPlays (stackHistory (fromCalendar W,z)) T 1 : ℝ) ≤
      (L : ℝ) + (∑ j ∈ range (T+1), stageCost z j L T y W) +
      (T : ℝ) * (if goodCalendar W z L T y then 0 else 1) := by
  classical
  by_cases hg : goodCalendar W z L T y
  · rw [if_pos hg, mul_zero, add_zero, ← chargeSet_card]
    have hs := saturated_count_le_charges W z L T hg
    have hi := initial_pull_count_le (stackHistory (fromCalendar W,z)) T L 1
    have he := historyPlays_split (stackHistory (fromCalendar W,z)) T L 1
    have hn : historyPlays (stackHistory (fromCalendar W,z)) T 1 ≤ L + (chargeSet W z L T y).card := by
      rw [he]
      exact Nat.add_le_add hi hs
    exact_mod_cast hn
  · rw [if_neg hg, mul_one]
    have ht : historyPlays (stackHistory (fromCalendar W,z)) T 1 ≤ T :=
      (card_filter_le _ _).trans_eq (card_range T)
    have hc : 0 ≤ ∑ j ∈ range (T+1), stageCost z j L T y W :=
      sum_nonneg (fun j _ => stageCost_nonneg W z j L T y)
    have hl : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    exact (Nat.cast_le.mpr ht).trans (by linarith)

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 theorem stackArm_on_event {h : History} {ω : StackOmega} {T : ℕ}
    (he : ω ∈ stackEvent h T) : stackArm ω T = historyChoice ω.1 h T := by
  unfold stackArm historyChoice
  rw [stackCounts_on_event he le_rfl]

 theorem stackEvent_local (h : History) (T : ℕ) (ω : StackOmega) :
    ω ∈ stackEvent h T ↔ ∀ t < T,
      historyChoice ω.1 h t = (h t).1 ∧
      ω.2 ((h t).1,historyPlays h t (h t).1) = (h t).2 := by
  constructor
  · intro he t ht
    have hp : ω ∈ stackEvent h t := fun u hu => he u (hu.trans ht)
    have hs := he t ht
    have ha : stackArm ω t = (h t).1 := congrArg Prod.fst hs
    have hb : stackCoin ω t = (h t).2 := congrArg Prod.snd hs
    refine ⟨(stackArm_on_event hp).symm.trans ha, ?_⟩
    simpa only [stackCoin, stackCounts_on_event hp le_rfl, ha, historyCounts_total] using hb
  · intro he
    have hh : ∀ t, t ≤ T → ω ∈ stackEvent h t := by
      intro t
      induction t with
      | zero => intro _ u hu; omega
      | succ t ih =>
        intro ht
        have hp := ih (by omega)
        have hd := he t (by omega)
        have ha : stackArm ω t = (h t).1 := (stackArm_on_event hp).trans hd.1
        intro u hu
        rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
        · exact hp u hu
        · apply Prod.ext
          · exact ha
          · simpa only [stackHistory, stackCoin, ha, stackCounts_on_event hp le_rfl,
              historyCounts_total] using hd.2
    exact hh T le_rfl

 noncomputable def stackLaw (p : Fin 2 → unitInterval) : Measure StackOmega :=
  posteriorLaw.prod (Measure.infinitePi (fun k : Fin 2 × ℕ => bernoulliMeasure true false (p k.1)))

 instance stackLaw_probability (p : Fin 2 → unitInterval) : IsProbabilityMeasure (stackLaw p) := by
  unfold stackLaw
  infer_instance

 theorem stack_history_probability (p : Fin 2 → unitInterval) (h : History) (T : ℕ) :
    stackLaw p (stackEvent h T) = posteriorLaw (posteriorHistoryEvent h T) *
      ∏ t : Fin T, bernoulliMeasure true false (p (h t).1) {(h t).2} := by
  let E : Set CoinStack := {z | ∀ t : Fin T,
    z ((h t).1,historyPlays h t (h t).1) = (h t).2}
  have he : stackEvent h T = (posteriorHistoryEvent h T) ×ˢ E := by
    ext ω
    rw [stackEvent_local]
    simp only [Set.mem_prod, posteriorHistoryEvent, E, Set.mem_ofPred_eq]
    constructor
    · intro hh
      exact ⟨fun t ht => (hh t ht).1, fun t => (hh t t.isLt).2⟩
    · rintro ⟨ha,hb⟩ t ht
      exact ⟨ha t ht,hb ⟨t,ht⟩⟩
  rw [he]
  unfold stackLaw
  rw [Measure.prod_prod]
  congr 1
  let f : Fin T → Fin 2 × ℕ := fun t => ((h t).1,historyPlays h t (h t).1)
  have hf : Function.Injective f := (history_pull_index_injective h).comp Fin.val_injective
  have hl := product_injective_coordinates
    (fun k : Fin 2 × ℕ => bernoulliMeasure true false (p k.1)) f hf
  rw [Measure.infinitePi_eq_pi (fun t : Fin T => bernoulliMeasure true false (p (f t).1))] at hl
  have hm : Measurable (fun z : CoinStack => fun t => z (f t)) := by fun_prop
  have hh := congrArg (fun μ : Measure (Fin T → Bool) => μ (Set.univ.pi (fun t => {(h t).2}))) hl
  rw [Measure.map_apply hm (MeasurableSet.univ_pi (fun _ => measurableSet_singleton _)),
    Measure.pi_pi] at hh
  simpa only [E, f, Set.preimage, Set.mem_pi, Set.mem_univ, forall_const,
    Set.mem_singleton_iff] using hh

 theorem native_stack_history_equal (ν : StochasticBandit 2)
    (hν : ∀ i, ν.P i (Icc 0 1) = 1) (h : History) (T : ℕ) :
    tsLaw ν (historyEvent h T) =
      stackLaw (fun i => meanParameter (ν.P i) (hν i)) (stackEvent h T) := by
  rw [native_history_probability ν hν, stack_history_probability]

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

 theorem fromCalendar_measurable : Measurable fromCalendar := by
  apply measurable_pi_lambda
  intro k
  exact (measurable_pi_apply _).comp (measurable_pi_apply _)

 theorem toCalendar_measurable : Measurable toCalendar := by
  apply measurable_pi_lambda
  intro t
  apply measurable_pi_lambda
  intro k
  exact measurable_pi_apply _

 theorem fromCalendar_law :
    (Measure.infinitePi (fun _ : ℕ => sliceLaw)).map fromCalendar = posteriorLaw := by
  rw [← calendar_law, Measure.map_map fromCalendar_measurable toCalendar_measurable]
  change posteriorLaw.map id = posteriorLaw
  exact Measure.map_id

 theorem calendar_stack_law (p : Fin 2 → unitInterval) :
    ((Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod
      (Measure.infinitePi (fun k : Fin 2 × ℕ => bernoulliMeasure true false (p k.1)))).map
      (Prod.map fromCalendar id) = stackLaw p := by
  rw [← Measure.map_prod_map _ _ fromCalendar_measurable measurable_id, fromCalendar_law,
    Measure.map_id]
  rfl

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 theorem calendar_counts_joint_measurable (t : ℕ) :
    Measurable (fun a : Calendar × CoinStack => stackCounts (fromCalendar a.1,a.2) t) :=
  (stackCounts_measurable t).comp ((fromCalendar_measurable.comp measurable_fst).prodMk measurable_snd)

 theorem stageCondition_joint_measurable (j L t : ℕ) :
    MeasurableSet {a : Calendar × CoinStack | stageCondition a.2 j L t a.1} := by
  have hc := calendar_counts_joint_measurable t
  exact (measurableSet_eq_fun (hc.fst.eval.add hc.snd.eval) measurable_const).inter
    (measurableSet_le measurable_const (hc.fst.eval.add hc.snd.eval))

 theorem stageEvent_joint_measurable (j L t : ℕ) :
    MeasurableSet {a : Calendar × CoinStack | a.1 ∈ stageEvent a.2 j L t} := by
  change MeasurableSet {a : Calendar × CoinStack |
    stageCondition a.2 j L t a.1 ∧ ∀ u < t, ¬ stageCondition a.2 j L u a.1}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (stageCondition_joint_measurable j L t).inter
    (MeasurableSet.iInter (fun u => MeasurableSet.iInter (fun (_ : u < t) =>
      (stageCondition_joint_measurable j L u).compl)))

 theorem chargeEvent_joint_measurable (j L t n : ℕ) (y : ℝ) :
    MeasurableSet {a : Calendar × CoinStack | a.1 ∈ chargeEvent a.2 j L t n y} := by
  change MeasurableSet {a : Calendar × CoinStack | a.1 ∈ stageEvent a.2 j L t ∧
    ∀ v ∈ Finset.Ico t (t+(n+1)),
      a.1 v (0,stackSuccessSum a.2 0 j,j-stackSuccessSum a.2 0 j) ≤ y}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply (stageEvent_joint_measurable j L t).inter
  apply MeasurableSet.iInter
  intro v
  apply MeasurableSet.iInter
  intro _
  have hs := (stackSuccessSum_measurable 0 j).comp
    (measurable_snd : Measurable (Prod.snd : Calendar × CoinStack → CoinStack))
  apply measurableSet_le _ measurable_const
  exact measurable_selected_table ((measurable_pi_apply v).comp measurable_fst)
    (measurable_const.prodMk (hs.prodMk (measurable_const.sub hs)))

 theorem stageCost_joint_measurable (j L T : ℕ) (y : ℝ) :
    Measurable (fun a : Calendar × CoinStack => stageCost a.2 j L T y a.1) := by
  classical
  exact eventCount_measurable _ _ (fun a _ => chargeEvent_joint_measurable j L a.1 a.2 y)

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open MeasureTheory ProbabilityTheory Set Finset

noncomputable def bernoulliStackLaw (p : unitInterval) : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p)

instance bernoulliStackLaw_probability (p : unitInterval) : IsProbabilityMeasure (bernoulliStackLaw p) := by
  unfold bernoulliStackLaw
  infer_instance

lemma bernoulli_selected_set_law (j : ℕ) (p : unitInterval) :
    (bernoulliStackLaw p).map (fun z : ℕ → Bool => {k | k < j ∧ z k = true}) =
      setBernoulli (Set.Iio j) p := by
  let f : ℕ → Bool → Prop := fun k b => k < j ∧ b = true
  have hf : ∀ k, Measurable (f k) := fun _ => Measurable.of_discrete
  have hm : Measurable (fun z : ℕ → Bool => fun k => f k (z k)) := by fun_prop
  have hmap := Measure.infinitePi_map_pi
    (fun _ : ℕ => bernoulliMeasure true false p) hf
  have he (k : ℕ) : (bernoulliMeasure true false p).map (f k) =
      unitInterval.toNNReal p • Measure.dirac (k ∈ Set.Iio j) +
        unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False := by
    rw [map_bernoulliMeasure' true false (hf k), bernoulliMeasure_def]
    simp [f]
  simp_rw [he] at hmap
  rw [setBernoulli_eq_map]
  rw [← hmap]
  have hset : Measurable (fun a : ℕ → Prop => {i | a i}) := MeasurableEquiv.setOfPred.measurable
  rw [Measure.map_map hset hm]
  rfl

lemma selected_set_card (j : ℕ) (z : ℕ → Bool) :
    Set.ncard {k | k < j ∧ z k = true} =
      ∑ k ∈ Finset.range j, if z k then 1 else 0 := by
  have he : {k | k < j ∧ z k = true} =
      ((Finset.range j).filter (fun k => z k = true) : Set ℕ) := by
    ext k
    simp
  rw [he, Set.ncard_coe_finset, Finset.card_filter]

lemma bernoulli_sum_law (j : ℕ) (p : unitInterval) :
    (bernoulliStackLaw p).map (fun z : ℕ → Bool =>
      ∑ k ∈ Finset.range j, if z k then 1 else 0) = binomial j p := by
  rw [binomial, ← bernoulli_selected_set_law]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  exact (selected_set_card j z).symm

lemma bernoulli_sum_expectation (j : ℕ) (p : unitInterval) (f : ℕ → ℝ) :
    (∫ z, f (∑ k ∈ Finset.range j, if z k then 1 else 0) ∂bernoulliStackLaw p) =
      binomExpectation j p f := by
  rw [binomExpectation_integral, ← bernoulli_sum_law]
  have hm : Measurable (fun z : ℕ → Bool => ∑ k ∈ Finset.range j, if z k then 1 else 0) := by
    apply Finset.measurable_sum
    intro k _
    exact (Measurable.of_discrete (f := fun b : Bool => if b then (1 : ℕ) else 0)).comp
      (measurable_pi_apply k)
  rw [integral_map hm.aemeasurable (by fun_prop)]

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

 noncomputable def coinStackLaw (p : Fin 2 → unitInterval) : Measure CoinStack :=
  Measure.infinitePi (fun k : Fin 2 × ℕ => bernoulliMeasure true false (p k.1))

 instance coinStackLaw_probability (p : Fin 2 → unitInterval) : IsProbabilityMeasure (coinStackLaw p) := by
  unfold coinStackLaw
  infer_instance

 theorem arm_stack_law (p : Fin 2 → unitInterval) (i : Fin 2) :
    (coinStackLaw p).map (fun z n => z (i,n)) = bernoulliStackLaw (p i) := by
  exact product_injective_coordinates _ (fun n => (i,n)) (fun a b h => congrArg Prod.snd h)

 theorem stack_sum_law (p : Fin 2 → unitInterval) (i : Fin 2) (j : ℕ) :
    (coinStackLaw p).map (fun z => stackSuccessSum z i j) = ProbabilityTheory.binomial j (p i) := by
  rw [← bernoulli_sum_law j (p i), ← arm_stack_law p i]
  rw [Measure.map_map]
  · rfl
  · apply Finset.measurable_sum
    intro k _
    exact (measurable_of_countable (fun b : Bool => if b then (1 : ℕ) else 0)).comp
      (measurable_pi_apply k)
  · exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

 theorem stack_sum_expectation (p : Fin 2 → unitInterval) (i : Fin 2) (j : ℕ) (f : ℕ → ℝ) :
    (∫ z, f (stackSuccessSum z i j) ∂coinStackLaw p) = binomExpectation j (p i) f := by
  rw [binomExpectation_integral, ← stack_sum_law p i j]
  exact (integral_map (stackSuccessSum_measurable i j).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable).symm

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

 theorem stack_sum_integrable (p : Fin 2 → unitInterval) (i : Fin 2) (j : ℕ) (f : ℕ → ℝ) :
    Integrable (fun z => f (stackSuccessSum z i j)) (coinStackLaw p) := by
  have hf : Integrable f ((coinStackLaw p).map (fun z => stackSuccessSum z i j)) := by
    rw [stack_sum_law]
    exact integrable_binomial f
  exact (integrable_map_measure (measurable_of_countable f).aestronglyMeasurable
    (stackSuccessSum_measurable i j).aemeasurable).mp hf

 theorem stageCost_joint_integrable (p : Fin 2 → unitInterval) (j L T : ℕ) (y : ℝ) :
    Integrable (fun a : Calendar × CoinStack => stageCost a.2 j L T y a.1)
      ((Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod (coinStackLaw p)) :=
  eventCount_integrable _ _ _ (fun a _ => chargeEvent_joint_measurable j L a.1 a.2 y)

 theorem stageCost_integrated_bound (p : Fin 2 → unitInterval) (j L T : ℕ)
    {y : ℝ} (hy : 0 < y) (hy1 : y < 1) :
    (∫ a : Calendar × CoinStack, stageCost a.2 j L T y a.1
      ∂(Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod (coinStackLaw p)) ≤
    binomExpectation j (p 0) (fun s => posteriorOdds j s y) := by
  have hi := stageCost_joint_integrable p j L T y
  rw [integral_prod_symm _ hi, ← stack_sum_expectation p 0 j (fun s => posteriorOdds j s y)]
  apply integral_mono hi.integral_prod_right
    (stack_sum_integrable p 0 j (fun s => posteriorOdds j s y))
  intro z
  exact stageCost_expectation z j L T hy hy1

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 def extendHistory {T : ℕ} (h : Fin T → Fin 2 × Bool) : History :=
  fun t => if ht : t < T then h ⟨t,ht⟩ else (0,false)

 theorem finite_history_law (ν : StochasticBandit 2)
    (hν : ∀ i, ν.P i (Icc 0 1) = 1) (T : ℕ) :
    (tsLaw ν).map (fun ω => fun t : Fin T => nativeHistory ω t) =
      (stackLaw (fun i => meanParameter (ν.P i) (hν i))).map
        (fun ω => fun t : Fin T => stackHistory ω t) := by
  have hm : Measurable (fun ω : TSOmega 2 => fun t : Fin T => nativeHistory ω t) :=
    measurable_pi_lambda _ (fun t => nativeHistory_measurable t)
  have hs : Measurable (fun ω : StackOmega => fun t : Fin T => stackHistory ω t) :=
    measurable_pi_lambda _ (fun t => stackHistory_measurable t)
  apply Measure.ext_of_singleton
  intro h
  rw [Measure.map_apply hm (measurableSet_singleton _),
    Measure.map_apply hs (measurableSet_singleton _)]
  have hn : (fun ω : TSOmega 2 => fun t : Fin T => nativeHistory ω t) ⁻¹' {h} =
      historyEvent (extendHistory h) T := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, historyEvent, Set.mem_ofPred_eq,
      funext_iff, extendHistory]
    constructor
    · intro hh t ht; simpa only [dif_pos ht] using hh ⟨t,ht⟩
    · intro hh t; simpa only [dif_pos t.isLt] using hh t t.isLt
  have hp : (fun ω : StackOmega => fun t : Fin T => stackHistory ω t) ⁻¹' {h} =
      stackEvent (extendHistory h) T := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, stackEvent, Set.mem_ofPred_eq,
      funext_iff, extendHistory]
    constructor
    · intro hh t ht; simpa only [dif_pos ht] using hh ⟨t,ht⟩
    · intro hh t; simpa only [dif_pos t.isLt] using hh t t.isLt
  rw [hn,hp]
  exact native_stack_history_equal ν hν _ T

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

 instance tsLaw_probability (ν : StochasticBandit 2) : IsProbabilityMeasure (tsLaw ν) := by
  unfold tsLaw
  infer_instance

 theorem optimalMean_two (ν : StochasticBandit 2)
    (h : banditArmMean ν 1 ≤ banditArmMean ν 0) :
    banditOptimalMean ν = banditArmMean ν 0 := by
  unfold banditOptimalMean
  apply le_antisymm
  · apply ciSup_le
    intro i; fin_cases i
    · exact le_rfl
    · exact h
  · exact le_ciSup (Set.finite_range _).bddAbove 0

 theorem gap_two (ν : StochasticBandit 2)
    (h : banditArmMean ν 1 ≤ banditArmMean ν 0) (i : Fin 2) :
    banditGap ν i = if i = 1 then banditArmMean ν 0 - banditArmMean ν 1 else 0 := by
  unfold banditGap
  rw [optimalMean_two ν h]
  fin_cases i <;> simp

 theorem plays_integrable (ν : StochasticBandit 2) (T : ℕ) (i : Fin 2) :
    Integrable (fun ω => (tsPlays ω T i : ℝ)) (tsLaw ν) := by
  apply (integrable_const (T : ℝ)).mono' ((measurable_from_nat : Measurable (fun n : ℕ => (n : ℝ))).comp (plays_measurable T i)).aestronglyMeasurable
  filter_upwards [] with ω
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (tsPlays ω T i) : (0 : ℝ) ≤ _)] using
    (Nat.cast_le.mpr (plays_le_time ω T i) : (tsPlays ω T i : ℝ) ≤ (T : ℝ))

 theorem regret_eq_count (ν : StochasticBandit 2)
    (h : banditArmMean ν 1 ≤ banditArmMean ν 0) (T : ℕ) :
    tsRegret ν T = ENNReal.ofReal ((banditArmMean ν 0 - banditArmMean ν 1) *
      ∫ ω, (tsPlays ω T 1 : ℝ) ∂tsLaw ν) := by
  let Δ := banditArmMean ν 0 - banditArmMean ν 1
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr h
  have he (ω : TSOmega 2) :
      ∑ t ∈ Finset.range T, ENNReal.ofReal (banditGap ν (tsArm ω t)) =
        ENNReal.ofReal (Δ * (tsPlays ω T 1 : ℝ)) := by
    simp only [gap_two ν h]
    rw [ENNReal.ofReal_mul hΔ]
    simp only [tsPlays, ENNReal.ofReal_natCast]
    simp only [apply_ite ENNReal.ofReal, ENNReal.ofReal_zero]
    rw [← Finset.sum_filter]
    simp [Δ, nsmul_eq_mul, mul_comm]
  unfold tsRegret
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal ((plays_integrable ν T 1).const_mul Δ)
    (Filter.Eventually.of_forall (fun ω => mul_nonneg hΔ (Nat.cast_nonneg _))),
    integral_const_mul]

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 theorem historyPlays_fin (h : History) (T : ℕ) (i : Fin 2) :
    historyPlays h T i = ((Finset.univ : Finset (Fin T)).filter (fun t : Fin T => (h t).1 = i)).card := by
  classical
  unfold historyPlays
  apply Finset.card_bij (fun t ht => (⟨t,(Finset.mem_range.mp (Finset.mem_filter.mp ht).1)⟩ : Fin T))
  · intro t ht; simpa using (Finset.mem_filter.mp ht).2
  · intro a ha b hb he; exact congrArg Fin.val he
  · intro b hb
    exact ⟨b, by simpa using And.intro b.isLt (Finset.mem_filter.mp hb).2, rfl⟩

 theorem plays_stack_integral (ν : StochasticBandit 2)
    (hν : ∀ i, ν.P i (Icc 0 1) = 1) (T : ℕ) (i : Fin 2) :
    (∫ ω, (tsPlays ω T i : ℝ) ∂tsLaw ν) =
      ∫ ω, (historyPlays (stackHistory ω) T i : ℝ)
        ∂stackLaw (fun i => meanParameter (ν.P i) (hν i)) := by
  classical
  let f : (Fin T → Fin 2 × Bool) → ℝ := fun h =>
    ((Finset.univ.filter (fun t => (h t).1 = i)).card : ℝ)
  have hf : StronglyMeasurable f := (measurable_of_finite f).stronglyMeasurable
  have hn : Measurable (fun ω : TSOmega 2 => fun t : Fin T => nativeHistory ω t) :=
    measurable_pi_lambda _ (fun t => nativeHistory_measurable t)
  have hs : Measurable (fun ω : StackOmega => fun t : Fin T => stackHistory ω t) :=
    measurable_pi_lambda _ (fun t => stackHistory_measurable t)
  have he := congrArg (fun μ => ∫ h, f h ∂μ) (finite_history_law ν hν T)
  rw [integral_map_of_stronglyMeasurable hn hf, integral_map_of_stronglyMeasurable hs hf] at he
  have hnval (ω : TSOmega 2) : f (fun t : Fin T => nativeHistory ω t) = (tsPlays ω T i : ℝ) := by
    change (((Finset.univ : Finset (Fin T)).filter (fun t : Fin T => (nativeHistory ω t).1 = i)).card : ℝ) = _
    rw [← historyPlays_fin]
    rfl
  have hsval (ω : StackOmega) : f (fun t : Fin T => stackHistory ω t) = (historyPlays (stackHistory ω) T i : ℝ) := by
    change (((Finset.univ : Finset (Fin T)).filter (fun t : Fin T => (stackHistory ω t).1 = i)).card : ℝ) = _
    rw [← historyPlays_fin]
  simpa only [hnval,hsval] using he

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 theorem calendar_plays_measurable (T : ℕ) (i : Fin 2) :
    Measurable (fun a : Calendar × CoinStack =>
      (historyPlays (stackHistory (fromCalendar a.1,a.2)) T i : ℝ)) := by
  simp only [← stack_total]
  exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    ((calendar_counts_joint_measurable T).fst.eval.add (calendar_counts_joint_measurable T).snd.eval)

 theorem calendar_plays_integrable (p : Fin 2 → unitInterval) (T : ℕ) (i : Fin 2) :
    Integrable (fun a : Calendar × CoinStack =>
      (historyPlays (stackHistory (fromCalendar a.1,a.2)) T i : ℝ))
      ((Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod
        (Measure.infinitePi (fun k : Fin 2 × ℕ => bernoulliMeasure true false (p k.1)))) := by
  apply (integrable_const (T : ℝ)).mono' (calendar_plays_measurable T i).aestronglyMeasurable
  filter_upwards [] with a
  have ht : historyPlays (stackHistory (fromCalendar a.1,a.2)) T i ≤ T :=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_range T)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (historyPlays (stackHistory (fromCalendar a.1,a.2)) T i) : (0 : ℝ) ≤ _)] using (Nat.cast_le.mpr ht : (_ : ℝ) ≤ T)

 theorem native_calendar_plays (ν : StochasticBandit 2)
    (hν : ∀ i, ν.P i (Icc 0 1) = 1) (T : ℕ) (i : Fin 2) :
    (∫ ω, (tsPlays ω T i : ℝ) ∂tsLaw ν) =
      ∫ a : Calendar × CoinStack,
        (historyPlays (stackHistory (fromCalendar a.1,a.2)) T i : ℝ)
        ∂(Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod
          (Measure.infinitePi (fun k : Fin 2 × ℕ =>
            bernoulliMeasure true false (meanParameter (ν.P k.1) (hν k.1)))) := by
  rw [plays_stack_integral ν hν T i, ← calendar_stack_law]
  apply integral_map_of_stronglyMeasurable
  · exact fromCalendar_measurable.prodMap measurable_id
  · apply Measurable.stronglyMeasurable
    simp only [← stack_total]
    exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      ((stackCounts_measurable T).fst.eval.add (stackCounts_measurable T).snd.eval)

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory Set

 theorem prefix_current_independent {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (t : ℕ) :
    IndepFun (fun W : ℕ → E => fun i : Finset.range t => W i)
      (fun W => W t) (Measure.infinitePi (fun _ : ℕ => P)) := by
  have hd : Disjoint (Finset.range t) ({t} : Finset ℕ) := by
    simp
  have hi := product_disjoint_blocks (fun _ : ℕ => P) (Finset.range t) {t} hd
  have he := hi.comp measurable_id
    (measurable_pi_apply (⟨t,Finset.mem_singleton_self t⟩ : ({t} : Finset ℕ)))
  exact he

 theorem prefix_current_law {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (t : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => P)).map
      (fun W => ((fun i : Finset.range t => W i),W t)) =
    ((Measure.infinitePi (fun _ : ℕ => P)).map
      (fun W => fun i : Finset.range t => W i)).prod P := by
  rw [(prefix_current_independent P t).map_prod_eq_prod_map_map
    ((measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).aemeasurable)
    (measurable_pi_apply t).aemeasurable, Measure.infinitePi_map_eval]

 theorem predictable_event_bound {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (t : ℕ)
    (A : Set (((Finset.range t) → E) × E)) (hA : MeasurableSet A)
    (c : ENNReal) (hb : ∀ u, P {v | (u,v) ∈ A} ≤ c) :
    (Measure.infinitePi (fun _ : ℕ => P))
      {W | ((fun i : Finset.range t => W i), W t) ∈ A} ≤ c := by
  have he := congrArg (fun μ => μ A) (prefix_current_law P t)
  rw [Measure.map_apply (by fun_prop) hA, Measure.prod_apply hA] at he
  change (Measure.infinitePi (fun _ : ℕ => P))
    ((fun W => ((fun i : Finset.range t => W i),W t)) ⁻¹' A) ≤ c
  rw [he]
  calc
    _ ≤ ∫⁻ _, c ∂(Measure.infinitePi (fun _ : ℕ => P)).map
      (fun W => fun i : Finset.range t => W i) := lintegral_mono hb
    _ = c := by
      rw [lintegral_const, Measure.map_apply (by fun_prop) MeasurableSet.univ]
      simp

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open scoped NNReal

open MeasureTheory ProbabilityTheory AgrawalGoyalTS.TwoArmed Finset

lemma binom_exponential_sum (n : ℕ) (p t : ℝ) :
    binomExpectation n p (fun k => Real.exp (t * k)) =
      (p * Real.exp t + (1 - p)) ^ n := by
  rw [add_pow]
  unfold binomExpectation
  apply sum_congr rfl
  intro k _
  rw [mul_pow, ← Real.exp_nat_mul]
  unfold binomPMF
  dsimp only
  rw [show t * (k : ℝ) = (k : ℝ) * t by ring]
  ring

lemma binom_centered_mgf (n : ℕ) (p : unitInterval) (t : ℝ) :
    mgf (fun k : ℕ => (k : ℝ) - n * (p : ℝ)) (binomial n p) t =
      (Real.exp (-t * p) * ((p : ℝ) * Real.exp t + (1 - p))) ^ n := by
  rw [mgf, ← binomExpectation_integral]
  have he : binomExpectation n p (fun k => Real.exp (t * ((k : ℝ) - n * p))) =
      Real.exp (-t * n * p) * binomExpectation n p (fun k => Real.exp (t * k)) := by
    unfold binomExpectation
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    dsimp only
    rw [show t * ((k : ℝ) - n * p) = (-t * n * p) + t * k by ring,
      Real.exp_add]
    ring
  rw [he, binom_exponential_sum, mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

lemma binomial_one_subGaussian (p : unitInterval) :
    HasSubgaussianMGF (fun k : ℕ => (k : ℝ) - p) (1 / 4) (binomial 1 p) := by
  have hb : ∀ᵐ k : ℕ ∂binomial 1 p, (k : ℝ) ∈ Set.Icc 0 1 := by
    filter_upwards [ae_le_of_hasLaw_binomial (HasLaw.id (μ := binomial 1 p))] with k hk
    exact ⟨by positivity, by exact_mod_cast hk⟩
  have h := hasSubgaussianMGF_of_mem_Icc
    (μ := binomial 1 p) (X := fun k : ℕ => (k : ℝ)) (by fun_prop) hb
  have hm : (∫ k : ℕ, (k : ℝ) ∂binomial 1 p) = p := by
    rw [← binomExpectation_integral, binom_mean]
    simp
  have hparam : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = 1 / 4 := by norm_num
  rw [hparam] at h
  convert h using 1
  funext k
  rw [hm]

lemma binomial_subGaussian (n : ℕ) (p : unitInterval) :
    HasSubgaussianMGF (fun k : ℕ => (k : ℝ) - n * (p : ℝ))
      ((n : ℝ≥0) / 4) (binomial n p) where
  integrable_exp_mul t := integrable_binomial _
  mgf_le t := by
    have h1 := (binomial_one_subGaussian p).mgf_le t
    have he1 := binom_centered_mgf 1 p t
    simp only [Nat.cast_one, one_mul, pow_one] at he1
    rw [he1] at h1
    rw [binom_centered_mgf]
    have hp0 := p.property.1
    have hp1 := p.property.2
    have hn := pow_le_pow_left₀ (by positivity : 0 ≤
      Real.exp (-t * p) * ((p : ℝ) * Real.exp t + (1 - p))) h1 n
    apply hn.trans_eq
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open scoped NNReal

open MeasureTheory ProbabilityTheory AgrawalGoyalTS.TwoArmed Finset Set

lemma binomial_event_real (n : ℕ) (p : unitInterval) (S : Set ℕ) [DecidablePred (· ∈ S)] :
    (binomial n p).real S =
      ∑ k ∈ (range (n + 1)).filter (fun k => k ∈ S), binomPMF n p k := by
  classical
  have hS : MeasurableSet S := Set.to_countable S |>.measurableSet
  have he : (∫ k : ℕ, S.indicator (fun _ => (1 : ℝ)) k ∂binomial n p) =
      (binomial n p).real S := by
    rw [integral_indicator hS]
    simp
  rw [← he, ← binomExpectation_integral]
  unfold binomExpectation
  rw [sum_filter]
  apply sum_congr rfl
  intro k _
  by_cases hk : k ∈ S <;> simp [Set.indicator, hk]

lemma binom_lower_deviation (n : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) {d : ℝ} (hd : 0 ≤ d) :
    (∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n * p - d),
      binomPMF n p k) ≤ Real.exp (-2 * d ^ 2 / n) := by
  let pp : unitInterval := ⟨p, hp, hp1⟩
  have h := (binomial_subGaussian n pp).neg.measure_ge_le hd
  change (binomial n pp).real {k : ℕ | d ≤ -((k : ℝ) - n * (pp : ℝ))} ≤ _ at h
  have he : {k : ℕ | d ≤ -(fun k : ℕ => (k : ℝ) - n * (pp : ℝ)) k} =
      {k : ℕ | (k : ℝ) ≤ n * p - d} := by
    ext k
    simp only [mem_ofPred_eq]
    change (d ≤ -((k : ℝ) - n * p)) ↔ _
    constructor <;> intro h <;> linarith
  rw [he, binomial_event_real] at h
  have hex : -(d ^ 2) / (2 * ((n : ℝ≥0) / 4 : ℝ≥0)) = -2 * d ^ 2 / n := by
    push_cast
    ring
  simpa only [hex, pp, Set.mem_ofPred_eq] using h

lemma binom_upper_deviation (n : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) {d : ℝ} (hd : 0 ≤ d) :
    (∑ k ∈ (range (n + 1)).filter (fun k : ℕ => n * p + d ≤ (k : ℝ)),
      binomPMF n p k) ≤ Real.exp (-2 * d ^ 2 / n) := by
  let pp : unitInterval := ⟨p, hp, hp1⟩
  have h := (binomial_subGaussian n pp).measure_ge_le hd
  have he : {k : ℕ | d ≤ (k : ℝ) - n * (pp : ℝ)} =
      {k : ℕ | n * p + d ≤ (k : ℝ)} := by
    ext k
    change (d ≤ (k : ℝ) - n * p) ↔ n * p + d ≤ (k : ℝ)
    constructor <;> intro h <;> linarith
  rw [he, binomial_event_real] at h
  have hex : -(d ^ 2) / (2 * ((n : ℝ≥0) / 4 : ℝ≥0)) = -2 * d ^ 2 / n := by
    push_cast
    ring
  simpa only [hex, pp, Set.mem_ofPred_eq] using h

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open AgrawalGoyalTS.TwoArmed MeasureTheory ProbabilityTheory Finset Set

lemma posterior_tail_concentration (j s : ℕ) (hsj : s ≤ j) {y d : ℝ}
    (hy : 0 < y) (hy1 : y < 1) (hd : 0 ≤ d) (hdy : d ≤ y)
    (hs : (s : ℝ) ≤ j * (y - d)) :
    (betaMeasure ((s : ℝ) + 1) ((j - s : ℕ) + 1)).real (Ioi y) ≤
      Real.exp (-2 * j * d ^ 2) := by
  rw [beta_binomial_tail j s hsj hy hy1]
  have hh := binom_lower_deviation (j + 1) hy.le hy1.le
    (show 0 ≤ (j + 1 : ℝ) * d by positivity)
  simp only [Nat.cast_add, Nat.cast_one] at hh
  have hthreshold : (s : ℝ) ≤ (j + 1 : ℝ) * y - (j + 1 : ℝ) * d := by nlinarith
  have hsum : binomCDF (j + 1) y s ≤
      ∑ k ∈ (range (j + 1 + 1)).filter
        (fun k : ℕ => (k : ℝ) ≤ (j + 1 : ℝ) * y - (j + 1 : ℝ) * d),
        binomPMF (j + 1) y k := by
    unfold binomCDF
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact mem_filter.mpr ⟨(mem_filter.mp hk).1, (mem_filter.mp hk).2.trans hthreshold⟩
    · intro k _ _
      exact binomPMF_nonneg hy.le hy1.le (j + 1) k
  apply hsum.trans (hh.trans (Real.exp_le_exp.mpr ?_))
  have hj : 0 < (j + 1 : ℝ) := by positivity
  apply (div_le_iff₀ hj).mpr
  nlinarith [sq_nonneg d]

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 theorem slice_tail_bound (i : Fin 2) (s f L : ℕ) {y d : ℝ}
    (hy : 0 < y) (hy1 : y < 1) (hd : 0 ≤ d) (hdy : d ≤ y)
    (hL : L ≤ s+f) (hs : (s : ℝ) ≤ (s+f : ℕ)*(y-d)) :
    sliceLaw {W | y < W (i,s,f)} ≤ ENNReal.ofReal (Real.exp (-2*(L : ℝ)*d^2)) := by
  have ht := posterior_tail_concentration (s+f) s (by omega) hy hy1 hd hdy hs
  have hcast : (s+f-s : ℕ) = f := by omega
  rw [hcast] at ht
  have he : sliceLaw.real {W | y < W (i,s,f)} =
      (betaMeasure ((s : ℝ)+1) ((f : ℝ)+1)).real (Ioi y) := by
    rw [← slice_coordinate_law i s f]
    simp only [Measure.real]
    rw [Measure.map_apply (measurable_pi_apply _) measurableSet_Ioi]
    rfl
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  change sliceLaw.real {W | y < W (i,s,f)} ≤ _
  rw [he]
  apply ht.trans
  apply Real.exp_le_exp.mpr
  have hc : (L : ℝ) ≤ (s+f : ℕ) := Nat.cast_le.mpr hL
  nlinarith [sq_nonneg d]

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 theorem rare_posterior_bound (t L : ℕ)
    (c : ((Finset.range t) → PosteriorSlice) → CountState) (hc : Measurable c)
    {y d : ℝ} (hy : 0 < y) (hy1 : y < 1) (hd : 0 ≤ d) (hdy : d ≤ y) :
    (Measure.infinitePi (fun _ : ℕ => sliceLaw))
      {W | let a := c (fun k => W k)
        L ≤ a.1 1+a.2 1 ∧ (a.1 1 : ℝ) ≤ (a.1 1+a.2 1 : ℕ)*(y-d) ∧
          y < W t (1,a.1 1,a.2 1)} ≤ ENNReal.ofReal (Real.exp (-2*(L : ℝ)*d^2)) := by
  let A : Set ((((Finset.range t) → PosteriorSlice)) × PosteriorSlice) :=
    {a | L ≤ (c a.1).1 1+(c a.1).2 1 ∧
      ((c a.1).1 1 : ℝ) ≤ ((c a.1).1 1+(c a.1).2 1 : ℕ)*(y-d) ∧
      y < a.2 (1,(c a.1).1 1,(c a.1).2 1)}
  have hs : Measurable (fun a : (((Finset.range t) → PosteriorSlice) × PosteriorSlice) => (c a.1).1 1) := hc.fst.eval.comp measurable_fst
  have hf : Measurable (fun a : (((Finset.range t) → PosteriorSlice) × PosteriorSlice) => (c a.1).2 1) := hc.snd.eval.comp measurable_fst
  have hA : MeasurableSet A := by
    apply (measurableSet_le measurable_const (hs.add hf)).inter
    apply MeasurableSet.inter
    · exact measurableSet_le ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hs) (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (hs.add hf)).mul_const (y-d))
    · exact measurableSet_lt measurable_const
        (measurable_selected_table measurable_snd
          (measurable_const.prodMk (hs.prodMk hf)))
  apply predictable_event_bound sliceLaw t A hA
  intro u
  by_cases h : L ≤ (c u).1 1+(c u).2 1 ∧
      ((c u).1 1 : ℝ) ≤ ((c u).1 1+(c u).2 1 : ℕ)*(y-d)
  · apply (measure_mono (show {v | (u,v) ∈ A} ⊆
        {v | y < v (1,(c u).1 1,(c u).2 1)} from fun _ hv => hv.2.2)).trans
    exact slice_tail_bound 1 _ _ L hy hy1 hd hdy h.1 h.2
  · have he : {v | (u,v) ∈ A} = ∅ := by
      ext v; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hv; exact h ⟨hv.1,hv.2.1⟩
    rw [he,measure_empty]
    exact zero_le

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 noncomputable def rareAt (z : CoinStack) (L t : ℕ) (y d : ℝ) : Set Calendar :=
  {W | let c := stackCounts (fromCalendar W,z) t
    L ≤ c.1 1+c.2 1 ∧ (c.1 1 : ℝ) ≤ (c.1 1+c.2 1 : ℕ)*(y-d) ∧
      y < W t (1,c.1 1,c.2 1)}

 theorem rareAt_bound (z : CoinStack) (L t : ℕ) {y d : ℝ}
    (hy : 0 < y) (hy1 : y < 1) (hd : 0 ≤ d) (hdy : d ≤ y) :
    (Measure.infinitePi (fun _ : ℕ => sliceLaw)) (rareAt z L t y d) ≤
      ENNReal.ofReal (Real.exp (-2*(L : ℝ)*d^2)) := by
  have hb := rare_posterior_bound t L
    (fun W => stackCounts (fromCalendar (prefixCalendar t W),z) t)
    (prefix_counts_measurable z t) hy hy1 hd hdy
  simpa only [prefix_counts, rareAt] using hb

 theorem rareAt_joint_measurable (L t : ℕ) (y d : ℝ) :
    MeasurableSet {a : Calendar × CoinStack | a.1 ∈ rareAt a.2 L t y d} := by
  have hc := calendar_counts_joint_measurable t
  have hs : Measurable (fun a : Calendar × CoinStack =>
      (stackCounts (fromCalendar a.1,a.2) t).1 1) := hc.fst.eval
  have hf : Measurable (fun a : Calendar × CoinStack =>
      (stackCounts (fromCalendar a.1,a.2) t).2 1) := hc.snd.eval
  apply (measurableSet_le measurable_const (hs.add hf)).inter
  apply MeasurableSet.inter
  · exact measurableSet_le ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hs) (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (hs.add hf)).mul_const (y-d))
  · exact measurableSet_lt measurable_const
      (measurable_selected_table ((measurable_pi_apply t).comp measurable_fst)
        (measurable_const.prodMk (hs.prodMk hf)))

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory AgrawalGoyalTS.TwoArmed Finset Set

lemma binomial_empirical_upper_tail (p : unitInterval) {d : ℝ} (hd : 0 ≤ d)
    (j L : ℕ) (hLj : L ≤ j) :
    (binomial j p).real {s : ℕ | j * ((p : ℝ) + d) < (s : ℝ)} ≤
      Real.exp (-2 * L * d ^ 2) := by
  classical
  by_cases hj : j = 0
  · have hL : L = 0 := by omega
    simp only [hL, Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero]
    exact measureReal_le_one
  · have hjr : (j : ℝ) ≠ 0 := by exact_mod_cast hj
    have hh := binom_upper_deviation j p.2.1 p.2.2
      (mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hd)
    rw [binomial_event_real]
    calc
      _ ≤ ∑ s ∈ (range (j + 1)).filter (fun s : ℕ => j * (p : ℝ) + j * d ≤ (s : ℝ)),
          binomPMF j p s := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro s hs
          refine mem_filter.mpr ⟨(mem_filter.mp hs).1, ?_⟩
          have hh := (mem_filter.mp hs).2
          change j * ((p : ℝ) + d) < (s : ℝ) at hh
          nlinarith
        · intro s _ _
          exact binomPMF_nonneg p.2.1 p.2.2 j s
      _ ≤ Real.exp (-2 * ((j : ℝ) * d) ^ 2 / j) := hh
      _ = Real.exp (-2 * j * d ^ 2) := by
        congr 1
        field_simp [hjr]
      _ ≤ Real.exp (-2 * L * d ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hLjR : (L : ℝ) ≤ j := by exact_mod_cast hLj
        nlinarith [mul_nonneg (sub_nonneg.mpr hLjR) (sq_nonneg d)]

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 noncomputable def empiricalBad (p : Fin 2 → unitInterval) (L T : ℕ) (d : ℝ) : Set CoinStack :=
  {z | ∃ j < T, L ≤ j ∧ (j : ℝ)*((p 1 : ℝ)+d) < stackSuccessSum z 1 j}

 theorem empiricalBad_measurable (p : Fin 2 → unitInterval) (L T : ℕ) (d : ℝ) :
    MeasurableSet (empiricalBad p L T d) := by
  unfold empiricalBad
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun j => (MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter
      (measurableSet_lt measurable_const ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (stackSuccessSum_measurable 1 j)))))

 theorem empirical_at_bound (p : Fin 2 → unitInterval) (L j : ℕ) {d : ℝ}
    (hd : 0 ≤ d) (hL : L ≤ j) :
    (coinStackLaw p) {z | (j : ℝ)*((p 1 : ℝ)+d) < stackSuccessSum z 1 j} ≤
      ENNReal.ofReal (Real.exp (-2*(L : ℝ)*d^2)) := by
  have ht := binomial_empirical_upper_tail (p 1) hd j L hL
  rw [← stack_sum_law p 1 j] at ht
  simp only [Measure.real] at ht
  rw [Measure.map_apply (stackSuccessSum_measurable 1 j) (measurableSet_lt measurable_const (by fun_prop))] at ht
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact ht

 theorem empiricalBad_bound (p : Fin 2 → unitInterval) (L T : ℕ) {d : ℝ}
    (hd : 0 ≤ d) :
    (coinStackLaw p) (empiricalBad p L T d) ≤
      (T : ENNReal)*ENNReal.ofReal (Real.exp (-2*(L : ℝ)*d^2)) := by
  let A : ℕ → Set CoinStack := fun j =>
    {z | L ≤ j ∧ (j : ℝ)*((p 1 : ℝ)+d) < stackSuccessSum z 1 j}
  have he : empiricalBad p L T d = ⋃ j ∈ Finset.range T, A j := by
    ext z
    simp only [empiricalBad, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, A]
    constructor
    · rintro ⟨j,hj,hh⟩; exact ⟨j,hj,hh⟩
    · rintro ⟨j,hj,hh⟩; exact ⟨j,hj,hh⟩
  rw [he]
  apply (measure_biUnion_finset_le _ _).trans
  calc
    ∑ j ∈ Finset.range T, coinStackLaw p (A j) ≤
      ∑ _j ∈ Finset.range T, ENNReal.ofReal (Real.exp (-2*(L : ℝ)*d^2)) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : L ≤ j
      · exact (measure_mono (fun _ h => h.2)).trans (empirical_at_bound p L j hd hj)
      · simp [A,hj]
    _ = _ := by simp

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 noncomputable def badAt (z : CoinStack) (L t : ℕ) (y : ℝ) : Set Calendar :=
  {W | L ≤ historyPlays (stackHistory (fromCalendar W,z)) t 1 ∧
    y < W t (1,(stackCounts (fromCalendar W,z) t).1 1,(stackCounts (fromCalendar W,z) t).2 1)}

 theorem badAt_joint_measurable (L t : ℕ) (y : ℝ) :
    MeasurableSet {a : Calendar × CoinStack | a.1 ∈ badAt a.2 L t y} := by
  have hc := calendar_counts_joint_measurable t
  have hs : Measurable (fun a : Calendar × CoinStack =>
    (stackCounts (fromCalendar a.1,a.2) t).1 1) := hc.fst.eval
  have hf : Measurable (fun a : Calendar × CoinStack =>
    (stackCounts (fromCalendar a.1,a.2) t).2 1) := hc.snd.eval
  have hw : Measurable (fun a : Calendar × CoinStack =>
      a.1 t (1,(stackCounts (fromCalendar a.1,a.2) t).1 1,
        (stackCounts (fromCalendar a.1,a.2) t).2 1)) :=
    measurable_selected_table ((measurable_pi_apply t).comp measurable_fst)
      (measurable_const.prodMk (hs.prodMk hf))
  have hh : MeasurableSet {a : Calendar × CoinStack |
      L ≤ (stackCounts (fromCalendar a.1,a.2) t).1 1 +
        (stackCounts (fromCalendar a.1,a.2) t).2 1 ∧
      y < a.1 t (1,(stackCounts (fromCalendar a.1,a.2) t).1 1,
        (stackCounts (fromCalendar a.1,a.2) t).2 1)} :=
    (measurableSet_le measurable_const (hs.add hf)).inter
      (measurableSet_lt measurable_const hw)
  simpa only [stack_total, badAt, Set.mem_ofPred_eq] using hh

 theorem not_good_iff (W : Calendar) (z : CoinStack) (L T : ℕ) (y : ℝ) :
    ¬goodCalendar W z L T y ↔ ∃ t < T, W ∈ badAt z L t y := by
  simp only [goodCalendar, badAt, Set.mem_ofPred_eq]
  push Not
  rfl

 theorem not_good_measurable (L T : ℕ) (y : ℝ) :
    MeasurableSet {a : Calendar × CoinStack | ¬goodCalendar a.1 a.2 L T y} := by
  simp only [not_good_iff, Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun t => (MeasurableSet.const _).inter
    (badAt_joint_measurable L t y))

 theorem badAt_empirical_or_rare (p : Fin 2 → unitInterval) (L T t : ℕ)
    {y d : ℝ} (he : y-d=(p 1 : ℝ)+d) (ht : t < T)
    (W : Calendar) (z : CoinStack) (hb : W ∈ badAt z L t y) :
    z ∈ empiricalBad p L T d ∨ W ∈ rareAt z L t y d := by
  classical
  by_cases hz : z ∈ empiricalBad p L T d
  · exact Or.inl hz
  · right
    let j := historyPlays (stackHistory (fromCalendar W,z)) t 1
    have hj : j < T := by
      have hh : j ≤ t := (Finset.card_filter_le _ _).trans_eq (Finset.card_range t)
      omega
    have hs : (stackSuccessSum z 1 j : ℝ) ≤ (j : ℝ)*((p 1 : ℝ)+d) := by
      by_contra hn
      exact hz ⟨j,hj,hb.1,lt_of_not_ge hn⟩
    have hc := stack_counts_at_total (fromCalendar W,z) t j 1 rfl
    change L ≤ (stackCounts (fromCalendar W,z) t).1 1 +
      (stackCounts (fromCalendar W,z) t).2 1 ∧ _
    refine ⟨?_,?_,hb.2⟩
    · rw [stack_total]
      exact hb.1
    · rw [stack_total, hc.1, he]
      exact hs

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set Finset
open scoped Classical

 theorem finite_integral_budget {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Finset ι)
    (f : Ω → ℝ) (g : ι → Ω → ℝ) (B : Set Ω) (a b : ℝ)
    (hf : Integrable f μ) (hg : ∀ j ∈ I, Integrable (g j) μ)
    (hB : MeasurableSet B)
    (hle : ∀ x, f x ≤ a + (∑ j ∈ I, g j x) + b * B.indicator (fun _ => 1) x) :
    (∫ x, f x ∂μ) ≤ a + (∑ j ∈ I, ∫ x, g j x ∂μ) + b * μ.real B := by
  have hsum : Integrable (fun x => ∑ j ∈ I, g j x) μ := integrable_finsetSum I hg
  have hind : Integrable (B.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB
  have hbound : Integrable
      (fun x => a + (∑ j ∈ I, g j x) + b * B.indicator (fun _ => 1) x) μ :=
    ((integrable_const a).add hsum).add (hind.const_mul b)
  have hi := integral_mono hf hbound hle
  rw [integral_add (f := fun x => a + ∑ j ∈ I, g j x)
      (g := fun x => b * B.indicator (fun _ => 1) x)
      ((integrable_const a).add hsum) (hind.const_mul b),
    integral_add (f := fun _ => a) (g := fun x => ∑ j ∈ I, g j x)
      (integrable_const a) hsum, integral_const, integral_const_mul,
    integral_indicator hB, integral_const, integral_finsetSum I hg] at hi
  simpa using hi

 theorem expected_pull_budget (p : Fin 2 → unitInterval) (L T : ℕ) {y : ℝ}
    (hy : 0 < y) (hy1 : y < 1) :
    (∫ a : Calendar × CoinStack,
      (historyPlays (stackHistory (fromCalendar a.1,a.2)) T 1 : ℝ)
      ∂(Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod (coinStackLaw p)) ≤
    (L : ℝ) + (∑ j ∈ range (T+1), binomExpectation j (p 0) (fun s => posteriorOdds j s y)) +
      (T : ℝ)*((Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod (coinStackLaw p)).real
        {a : Calendar × CoinStack | ¬goodCalendar a.1 a.2 L T y} := by
  let μ := (Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod (coinStackLaw p)
  let B : Set (Calendar × CoinStack) := {a | ¬goodCalendar a.1 a.2 L T y}
  have hpoint (a : Calendar × CoinStack) :
      (historyPlays (stackHistory (fromCalendar a.1,a.2)) T 1 : ℝ) ≤
      (L : ℝ) + (∑ j ∈ range (T+1), stageCost a.2 j L T y a.1) +
        (T : ℝ) * B.indicator (fun _ => 1) a := by
    have hh := pathwise_pull_budget a.1 a.2 L T y
    by_cases hgood : goodCalendar a.1 a.2 L T y
    · simpa only [B, Set.indicator, Set.mem_ofPred_eq, hgood, not_true_eq_false,
        if_true, if_false] using hh
    · simpa only [B, Set.indicator, Set.mem_ofPred_eq, hgood, not_false_eq_true,
        if_true, if_false] using hh
  have hi := finite_integral_budget μ (range (T+1))
    (fun a => (historyPlays (stackHistory (fromCalendar a.1,a.2)) T 1 : ℝ))
    (fun j a => stageCost a.2 j L T y a.1) B (L : ℝ) (T : ℝ)
    (calendar_plays_integrable p T 1)
    (fun j _ => stageCost_joint_integrable p j L T y)
    (not_good_measurable L T y) hpoint
  apply hi.trans
  exact add_le_add (add_le_add le_rfl
    (sum_le_sum (fun j _ => stageCost_integrated_bound p j L T hy hy1))) le_rfl

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 theorem saturation_probability (p : Fin 2 → unitInterval) (L T : ℕ) {y d : ℝ}
    (hy : 0 < y) (hy1 : y < 1) (hd : 0 ≤ d) (hdy : d ≤ y)
    (he : y-d=(p 1 : ℝ)+d) :
    ((Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod (coinStackLaw p))
      {a : Calendar × CoinStack | ¬goodCalendar a.1 a.2 L T y} ≤
      2*(T : ENNReal)*ENNReal.ofReal (Real.exp (-2*(L : ℝ)*d^2)) := by
  let μ := (Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod (coinStackLaw p)
  let e := ENNReal.ofReal (Real.exp (-2*(L : ℝ)*d^2))
  let E : Set (Calendar × CoinStack) := {a | a.2 ∈ empiricalBad p L T d}
  let R : ℕ → Set (Calendar × CoinStack) := fun t => {a | a.1 ∈ rareAt a.2 L t y d}
  have hR (t : ℕ) : μ (R t) ≤ e := by
    rw [show μ = (Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod (coinStackLaw p) from rfl,
      Measure.prod_apply_symm (rareAt_joint_measurable L t y d)]
    calc
      _ ≤ ∫⁻ _z, e ∂coinStackLaw p := lintegral_mono (fun z => rareAt_bound z L t hy hy1 hd hdy)
      _ = e := by simp
  have hE : μ E ≤ (T : ENNReal)*e := by
    have hset : E = Set.univ ×ˢ empiricalBad p L T d := by ext a; simp [E]
    rw [hset]
    change (Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod (coinStackLaw p)
      (Set.univ ×ˢ empiricalBad p L T d) ≤ _
    rw [Measure.prod_prod]
    simpa [e] using empiricalBad_bound p L T hd
  have hs : {a : Calendar × CoinStack | ¬goodCalendar a.1 a.2 L T y} ⊆
      E ∪ ⋃ t ∈ Finset.range T, R t := by
    intro a ha
    obtain ⟨t,ht,hb⟩ := (not_good_iff a.1 a.2 L T y).mp ha
    rcases badAt_empirical_or_rare p L T t he ht a.1 a.2 hb with hz | hr
    · exact Or.inl hz
    · exact Or.inr (Set.mem_iUnion.mpr ⟨t,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr ht,hr⟩⟩)
  calc
    _ ≤ μ (E ∪ ⋃ t ∈ Finset.range T, R t) := measure_mono hs
    _ ≤ μ E + μ (⋃ t ∈ Finset.range T, R t) := measure_union_le _ _
    _ ≤ (T : ENNReal)*e + ∑ t ∈ Finset.range T, μ (R t) :=
      add_le_add hE (measure_biUnion_finset_le _ _)
    _ ≤ (T : ENNReal)*e + ∑ _t ∈ Finset.range T, e :=
      add_le_add le_rfl (Finset.sum_le_sum (fun t _ => hR t))
    _ = _ := by simp [e]; ring

end ThompsonSamplingProof


namespace ThompsonSamplingProof

lemma saturation_exponential_bound {Δ : ℝ} (hΔ : 0 < Δ) {T L : ℕ}
    (hT : 2 ≤ T) (hL : 32 * Real.log T / Δ ^ 2 ≤ (L : ℝ)) :
    Real.exp (-2 * L * (Δ / 4) ^ 2) ≤ 1 / (T : ℝ) ^ 4 := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hmul := (div_le_iff₀ (by positivity : 0 < Δ ^ 2)).mp hL
  have he : Real.exp (4 * Real.log (T : ℝ)) = (T : ℝ) ^ 4 := by
    simpa only [Real.exp_log hTp, Nat.cast_ofNat] using Real.exp_nat_mul (Real.log (T : ℝ)) 4
  calc
    _ ≤ Real.exp (-(4 * Real.log (T : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = _ := by rw [Real.exp_neg, he, one_div]

lemma saturation_ceiling_exponential {Δ : ℝ} (hΔ : 0 < Δ) {T : ℕ} (hT : 2 ≤ T) :
    Real.exp (-2 * (Nat.ceil (32 * Real.log T / Δ ^ 2) : ℝ) * (Δ / 4) ^ 2) ≤
      1 / (T : ℝ) ^ 4 :=
  saturation_exponential_bound hΔ hT (Nat.le_ceil _)

lemma saturation_count_penalty {Δ : ℝ} (hΔ : 0 < Δ) {T L : ℕ}
    (hT : 2 ≤ T) (hL : 32 * Real.log T / Δ ^ 2 ≤ (L : ℝ)) :
    2 * (T : ℝ) ^ 2 * Real.exp (-2 * L * (Δ / 4) ^ 2) ≤ 2 / (T : ℝ) ^ 2 := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  calc
    _ ≤ 2 * (T : ℝ) ^ 2 * (1 / (T : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left (saturation_exponential_bound hΔ hT hL) (by positivity)
    _ = _ := by field_simp [hTp.ne']

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed Set

 theorem saturation_real_bound (p : Fin 2 → unitInterval) (L T : ℕ) {y d : ℝ}
    (hy : 0 < y) (hy1 : y < 1) (hd : 0 ≤ d) (hdy : d ≤ y)
    (he : y-d=(p 1 : ℝ)+d) :
    ((Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod (coinStackLaw p)).real
      {a : Calendar × CoinStack | ¬goodCalendar a.1 a.2 L T y} ≤
      2*(T : ℝ)*Real.exp (-2*(L : ℝ)*d^2) := by
  have h := saturation_probability p L T hy hy1 hd hdy he
  have hn : (2*(T : ENNReal)*ENNReal.ofReal (Real.exp (-2*(L : ℝ)*d^2))) ≠ ⊤ := by finiteness
  have ht := ENNReal.toReal_mono hn h
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal (Real.exp_pos _).le] using ht

 theorem saturation_expected_penalty (p : Fin 2 → unitInterval)
    (hp : (p 1 : ℝ) < p 0) (T : ℕ) (hT : 2 ≤ T) :
    let Δ := (p 0 : ℝ)-(p 1 : ℝ)
    let y := ((p 0 : ℝ)+(p 1 : ℝ))/2
    let L := Nat.ceil (32*Real.log T/Δ^2)
    (T : ℝ)*((Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod (coinStackLaw p)).real
      {a : Calendar × CoinStack | ¬goodCalendar a.1 a.2 L T y} ≤ 2/(T : ℝ)^2 := by
  dsimp only
  have h0 : 0 ≤ (p 0 : ℝ) ∧ (p 0 : ℝ) ≤ 1 := (p 0).property
  have h1 : 0 ≤ (p 1 : ℝ) ∧ (p 1 : ℝ) ≤ 1 := (p 1).property
  have hΔ : 0 < (p 0 : ℝ)-(p 1 : ℝ) := sub_pos.mpr hp
  have hb := saturation_real_bound p (Nat.ceil (32*Real.log T/((p 0 : ℝ)-(p 1 : ℝ))^2)) T
    (y := ((p 0 : ℝ)+(p 1 : ℝ))/2) (d := ((p 0 : ℝ)-(p 1 : ℝ))/4)
    (by linarith) (by linarith) (by positivity) (by linarith) (by ring)
  calc
    _ ≤ (T : ℝ)*(2*T*Real.exp (-2*(Nat.ceil (32*Real.log T/((p 0 : ℝ)-(p 1 : ℝ))^2) : ℝ)*
      (((p 0 : ℝ)-(p 1 : ℝ))/4)^2)) := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg T)
    _ = 2*(T : ℝ)^2*Real.exp (-2*(Nat.ceil (32*Real.log T/((p 0 : ℝ)-(p 1 : ℝ))^2) : ℝ)*
      (((p 0 : ℝ)-(p 1 : ℝ))/4)^2) := by ring
    _ ≤ _ := saturation_count_penalty hΔ hT (Nat.le_ceil _)

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open Set

noncomputable def binaryDivergence (y p : ℝ) : ℝ :=
  y * (Real.log y - Real.log p) + (1 - y) * (Real.log (1 - y) - Real.log (1 - p))

lemma binaryDivergence_derivative (y : ℝ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (binaryDivergence y) ((p - y) / (p * (1 - p))) p := by
  have hlog := (Real.hasDerivAt_log (ne_of_gt hp))
  have hlog1 := (((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).log
    (ne_of_gt (sub_pos.mpr hp1)))
  have hd := (((hasDerivAt_const p (Real.log y)).sub hlog).const_mul y).add
    (((hasDerivAt_const p (Real.log (1 - y))).sub hlog1).const_mul (1 - y))
  convert hd using 1 <;> try rfl
  simp only [Pi.sub_apply, id_eq]
  field_simp [ne_of_gt hp, ne_of_gt (sub_pos.mpr hp1)]
  ring

lemma binaryDivergence_lower {y p : ℝ} (hy : 0 < y) (hyp : y ≤ p) (hp1 : p < 1) :
    2 * (p - y) ^ 2 ≤ binaryDivergence y p := by
  let F : ℝ → ℝ := fun u => binaryDivergence y u - 2 * (u - y) ^ 2
  have hderiv (u : ℝ) (hu : u ∈ Icc y p) :
      HasDerivAt F ((u - y) / (u * (1 - u)) - 4 * (u - y)) u := by
    have hd := (binaryDivergence_derivative y (hy.trans_le hu.1) (hu.2.trans_lt hp1)).sub
      ((((hasDerivAt_id u).sub_const y).pow 2).const_mul 2)
    convert hd using 1 <;> try rfl
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one, id_eq]
    ring
  have hcont : ContinuousOn F (Icc y p) := fun u hu => (hderiv u hu).continuousAt.continuousWithinAt
  have hmono : MonotoneOn F (Icc y p) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc y p) hcont
      (fun u hu => (hderiv u (interior_subset hu)).hasDerivWithinAt)
    intro u hu
    have hu' := interior_subset hu
    have hu0 : 0 < u := hy.trans_le hu'.1
    have hu1 : u < 1 := hu'.2.trans_lt hp1
    have hden : 0 < u * (1 - u) := mul_pos hu0 (sub_pos.mpr hu1)
    have hquad : 4 * (u * (1 - u)) ≤ 1 := by nlinarith [sq_nonneg (2 * u - 1)]
    have hprod := mul_nonneg (sub_nonneg.mpr hu'.1) (sub_nonneg.mpr hquad)
    have hd : 4 * (u - y) ≤ (u - y) / (u * (1 - u)) :=
      (le_div_iff₀ hden).mpr (by nlinarith)
    linarith
  have he := hmono ⟨le_rfl, hyp⟩ ⟨hyp, le_rfl⟩ hyp
  simp only [F, binaryDivergence, sub_self, mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0)] at he
  exact sub_nonneg.mp he

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open AgrawalGoyalTS.TwoArmed

lemma binom_adjacent (n k : ℕ) (hk : k < n) (p : ℝ) :
    (k + 1 : ℝ) * (1 - p) * binomPMF n p (k + 1) =
      ((n : ℝ) - k) * p * binomPMF n p k := by
  have hc : (n.choose (k + 1) : ℝ) * (k + 1 : ℝ) =
      (n.choose k : ℝ) * ((n : ℝ) - k) := by
    have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq n k)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk.le] using h
  have he : n - k = (n - (k + 1)) + 1 := by omega
  unfold binomPMF
  rw [pow_succ, he, pow_succ]
  calc
    _ = ((n.choose (k + 1) : ℝ) * (k + 1 : ℝ)) *
      (p ^ k * p * (1 - p) ^ (n - (k + 1)) * (1 - p)) := by ring
    _ = _ := by rw [hc]; ring

lemma binom_step_up {n k : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hk : k < n) (hm : (k + 1 : ℝ) ≤ (n + 1 : ℝ) * p) :
    binomPMF n p k ≤ binomPMF n p (k + 1) := by
  have he := binom_adjacent n k hk p
  have hf := binomPMF_nonneg hp.le hp1.le n k
  have ha : 0 < (k + 1 : ℝ) * (1 - p) := by positivity
  have hd : 0 ≤ (((n : ℝ) - k) * p - (k + 1 : ℝ) * (1 - p)) *
      binomPMF n p k := mul_nonneg (by nlinarith) hf
  nlinarith

lemma binom_step_down {n k : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hm : (n + 1 : ℝ) * p ≤ (k + 1 : ℝ)) :
    binomPMF n p (k + 1) ≤ binomPMF n p k := by
  by_cases hk : k < n
  · have he := binom_adjacent n k hk p
    have hf := binomPMF_nonneg hp.le hp1.le n k
    have ha : 0 < (k + 1 : ℝ) * (1 - p) := by positivity
    have hd : 0 ≤ ((k + 1 : ℝ) * (1 - p) - ((n : ℝ) - k) * p) *
        binomPMF n p k := mul_nonneg (by nlinarith) hf
    nlinarith
  · have hz : binomPMF n p (k + 1) = 0 := by
      simp [binomPMF, Nat.choose_eq_zero_of_lt (show n < k + 1 by omega)]
    rw [hz]
    exact binomPMF_nonneg hp.le hp1.le n k

lemma binom_mode_dominates {n m : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hmn : m ≤ n) (hml : (m : ℝ) ≤ (n + 1 : ℝ) * p)
    (hmu : (n + 1 : ℝ) * p ≤ (m + 1 : ℝ)) (k : ℕ) :
    binomPMF n p k ≤ binomPMF n p m := by
  by_cases hkm : k ≤ m
  · have hmono : MonotoneOn (binomPMF n p) (Set.Icc 0 m) := by
      apply monotoneOn_of_le_succ Set.ordConnected_Icc
      intro a _ _ ha
      have ham : a + 1 ≤ m := ha.2
      apply binom_step_up hp hp1 (by omega)
      exact (by exact_mod_cast ham : (a + 1 : ℝ) ≤ m).trans hml
    exact hmono ⟨Nat.zero_le _, hkm⟩ ⟨Nat.zero_le _, le_rfl⟩ hkm
  · have hanti : AntitoneOn (binomPMF n p) (Set.Ici m) := by
      apply antitoneOn_nat_Ici_of_succ_le
      intro a ha
      apply binom_step_down hp hp1
      exact hmu.trans (by exact_mod_cast Nat.add_le_add_right ha 1)
    have hmk : m ≤ k := by omega
    exact hanti (a := m) (b := k) (by simp) (by simpa using hmk) hmk

lemma exists_binom_mode (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∃ m : ℕ, m ≤ n ∧ (∀ k, binomPMF n p k ≤ binomPMF n p m) ∧
      ∀ s : ℕ, (n : ℝ) * p ≤ s → m ≤ s := by
  let m := Nat.floor ((n + 1 : ℝ) * p)
  have hx : 0 ≤ (n + 1 : ℝ) * p := by positivity
  have hml : (m : ℝ) ≤ (n + 1 : ℝ) * p := Nat.floor_le hx
  have hmu : (n + 1 : ℝ) * p < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmn : m ≤ n := by
    have hh : m < n + 1 := (Nat.floor_lt hx).mpr (by push_cast; nlinarith)
    omega
  refine ⟨m, hmn, binom_mode_dominates hp hp1 hmn hml hmu.le, ?_⟩
  intro s hs
  by_contra h
  have hh : (s : ℝ) + 1 ≤ m := by exact_mod_cast (show s + 1 ≤ m by omega)
  nlinarith

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open Finset

lemma nat_interval_card_bound (s : Finset ℕ) (a r : ℝ) (hr : 0 ≤ r)
    (hs : ∀ k ∈ s, |(k : ℝ) - a| < r) : (s.card : ℝ) ≤ 2 * r + 1 := by
  let lo : ℤ := Int.ceil (a - r)
  let hi : ℤ := Int.floor (a + r)
  have hsub : s.image (fun k : ℕ => (k : ℤ)) ⊆ Icc lo hi := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hz
    have hb := abs_lt.mp (hs k hk)
    simp only [mem_Icc]
    constructor
    · exact Int.ceil_le.mpr (by push_cast; linarith)
    · exact Int.le_floor.mpr (by push_cast; linarith)
  have hc : s.card ≤ (Icc lo hi).card := by
    calc
      s.card = (s.image (fun k : ℕ => (k : ℤ))).card :=
        (card_image_of_injective s Nat.cast_injective).symm
      _ ≤ _ := card_le_card hsub
  by_cases horder : lo ≤ hi + 1
  · have he := Int.card_Icc_of_le lo hi horder
    have he' : ((Icc lo hi).card : ℝ) = (hi : ℝ) + 1 - lo := by
      exact_mod_cast he
    have hlo : a - r ≤ (lo : ℝ) := Int.le_ceil _
    have hhi : (hi : ℝ) ≤ a + r := Int.floor_le _
    have hcr : (s.card : ℝ) ≤ (Icc lo hi).card := by exact_mod_cast hc
    linarith
  · have he : Icc lo hi = ∅ := Icc_eq_empty_of_lt (by omega)
    rw [he, card_empty] at hc
    have hz : s.card = 0 := Nat.eq_zero_of_le_zero hc
    rw [hz, Nat.cast_zero]
    linarith

lemma finite_mass_near_bound (s : Finset ℕ) (w : ℕ → ℝ) (a r M : ℝ)
    (hr : 0 ≤ r) (hm : 0 ≤ M) (hM : ∀ k ∈ s, w k ≤ M) :
    ∑ k ∈ s.filter (fun k : ℕ => |(k : ℝ) - a| < r), w k ≤ (2 * r + 1) * M := by
  calc
    _ ≤ ∑ _k ∈ s.filter (fun k : ℕ => |(k : ℝ) - a| < r), M :=
      sum_le_sum (fun k hk => hM k (mem_filter.mp hk).1)
    _ = ((s.filter (fun k : ℕ => |(k : ℝ) - a| < r)).card : ℝ) * M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (nat_interval_card_bound _ a r hr (fun k hk => (mem_filter.mp hk).2)) hm

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open AgrawalGoyalTS.TwoArmed Finset

lemma binom_mode_mass {n m : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hm : ∀ k, binomPMF n p k ≤ binomPMF n p m) :
    1 / (4 * Real.sqrt (n + 1)) ≤ binomPMF n p m := by
  let r : ℝ := Real.sqrt (n + 1)
  let w : ℕ → ℝ := binomPMF n p
  let near := (range (n + 1)).filter (fun k : ℕ => |(k : ℝ) - n * p| < r)
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hr1 : 1 ≤ r := by nlinarith [sq_nonneg (r - 1), Nat.cast_nonneg (α := ℝ) n]
  have hw : ∀ k, 0 ≤ w k := fun k => binomPMF_nonneg hp.le hp1.le n k
  have hpoint (k : ℕ) : r ^ 2 * w k ≤
      r ^ 2 * (if |(k : ℝ) - n * p| < r then w k else 0) +
        w k * ((k : ℝ) - n * p) ^ 2 := by
    split_ifs with h
    · nlinarith [mul_nonneg (hw k) (sq_nonneg ((k : ℝ) - n * p))]
    · have hab : r ≤ |(k : ℝ) - n * p| := le_of_not_gt h
      have hsq : r ^ 2 ≤ ((k : ℝ) - n * p) ^ 2 := by
        nlinarith [sq_abs ((k : ℝ) - n * p), abs_nonneg ((k : ℝ) - n * p)]
      simpa only [mul_zero, zero_mul, zero_add, add_zero, mul_comm] using mul_le_mul_of_nonneg_left hsq (hw k)
  have hsum := sum_le_sum (fun k (_hk : k ∈ range (n + 1)) => hpoint k)
  have he : (∑ k ∈ range (n + 1),
      (r ^ 2 * (if |(k : ℝ) - n * p| < r then w k else 0) +
        w k * ((k : ℝ) - n * p) ^ 2)) =
      r ^ 2 * (∑ k ∈ near, w k) + n * p * (1 - p) := by
    rw [sum_add_distrib, ← mul_sum]
    change r ^ 2 * (∑ k ∈ range (n + 1),
      if |(k : ℝ) - n * p| < r then w k else 0) +
      binomExpectation n p (fun k => ((k : ℝ) - n * p) ^ 2) = _
    rw [binom_centered_second, ← sum_filter]
  rw [← mul_sum] at hsum
  have hw1 : (∑ k ∈ range (n + 1), w k) = 1 := binomPMF_sum n p
  rw [hw1, mul_one, he, hr2] at hsum
  have hv : (n : ℝ) * p * (1 - p) ≤ n / 4 := by
    have hh : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
    nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) n)]
  have hnear : 3 / 4 ≤ ∑ k ∈ near, w k := by
    by_contra h
    have hn := mul_nonneg (Nat.cast_nonneg (α := ℝ) n)
      (show 0 ≤ 3 / 4 - ∑ k ∈ near, w k by linarith)
    nlinarith
  have hupper : (∑ k ∈ near, w k) ≤ (2 * r + 1) * w m :=
    finite_mass_near_bound _ w (n * p) r (w m) hr.le
      (hw m) (fun k _ => hm k)
  have hh : 1 ≤ 4 * r * w m := by
    have hmul : (2 * r + 1) * w m ≤ 3 * r * w m := by
      nlinarith [hw m]
    linarith
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.sqrt (n + 1))).mpr
  simpa only [mul_comm] using hh

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open AgrawalGoyalTS.TwoArmed Finset

lemma binomPMF_succ_lower {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (n k : ℕ) (hk : k ≤ n) :
    (1 - p) * binomPMF n p k ≤ binomPMF (n + 1) p k := by
  have he : n + 1 - k = (n - k) + 1 := by omega
  have hc : (n.choose k : ℝ) ≤ ((n + 1).choose k : ℝ) := by
    exact_mod_cast Nat.choose_le_succ n k
  unfold binomPMF
  rw [he, pow_succ]
  have hh := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ p ^ k * (1 - p) ^ (n - k) * (1 - p) by positivity)
  nlinarith

lemma binomCDF_succ_lower {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) (x : ℝ) : (1 - p) * binomCDF n p x ≤ binomCDF (n + 1) p x := by
  unfold binomCDF
  rw [mul_sum]
  calc
    _ ≤ ∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ x),
        binomPMF (n + 1) p k := by
      apply sum_le_sum
      intro k hk
      exact binomPMF_succ_lower hp hp1 n k (by simpa using (mem_filter.mp hk).1)
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        rcases mem_filter.mp hk with ⟨hk, hx⟩
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hk; omega), hx⟩
      · intro k _ _
        exact binomPMF_nonneg hp hp1 (n + 1) k

lemma binomCDF_above_mean {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (n s : ℕ) (hs : (n : ℝ) * p ≤ s) :
    1 / (4 * Real.sqrt (n + 1)) ≤ binomCDF n p s := by
  obtain ⟨m, hmn, hm, hms⟩ := exists_binom_mode n hp hp1
  have hmem : m ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ s) := by
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), by exact_mod_cast hms s hs⟩
  exact (binom_mode_mass hp hp1 hm).trans
    (single_le_sum (fun k _ => binomPMF_nonneg hp.le hp1.le n k) hmem)

lemma posterior_success_lower {y : ℝ} (hy : 0 < y) (hy1 : y < 1)
    (j s : ℕ) (hs : (j : ℝ) * y ≤ s) :
    (1 - y) / (4 * Real.sqrt (j + 1)) ≤ binomCDF (j + 1) y s := by
  calc
    _ = (1 - y) * (1 / (4 * Real.sqrt (j + 1))) := by ring
    _ ≤ (1 - y) * binomCDF j y s :=
      mul_le_mul_of_nonneg_left (binomCDF_above_mean hy hy1 j s hs) (by linarith)
    _ ≤ _ := binomCDF_succ_lower hy.le hy1.le j s

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open AgrawalGoyalTS.TwoArmed Finset

lemma binom_likelihood_ratio (n s : ℕ) (hs : s ≤ n) {y p : ℝ}
    (hy : 0 < y) (hy1 : y < 1) (_hp : 0 < p) (hp1 : p < 1) :
    binomPMF n p s / binomPMF n y s =
      ((1 - p) / (1 - y)) ^ n * (p * (1 - y) / (y * (1 - p))) ^ s := by
  have hc : (n.choose s : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hs).ne'
  have hyn : y ≠ 0 := ne_of_gt hy
  have hy1n : 1 - y ≠ 0 := ne_of_gt (sub_pos.mpr hy1)
  have hp1n : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  unfold binomPMF
  conv_rhs => rw [show n = s + (n - s) from (Nat.add_sub_of_le hs).symm]
  simp only [pow_add, div_pow, mul_pow]
  field_simp

lemma likelihood_log_identity {y p : ℝ} (hy : 0 < y) (hyp : y < p) (hp1 : p < 1) :
    Real.log ((1 - p) / (1 - y)) +
      y * Real.log (p * (1 - y) / (y * (1 - p))) = -binaryDivergence y p := by
  have hp := hy.trans hyp
  have hy1 := hyp.trans hp1
  rw [Real.log_div (ne_of_gt (sub_pos.mpr hp1)) (ne_of_gt (sub_pos.mpr hy1)),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul hp.ne' (ne_of_gt (sub_pos.mpr hy1)),
    Real.log_mul hy.ne' (ne_of_gt (sub_pos.mpr hp1))]
  unfold binaryDivergence
  ring

lemma likelihood_at_mean_bound (n m : ℕ) {y p : ℝ}
    (hy : 0 < y) (hyp : y < p) (hp1 : p < 1) (hm : (m : ℝ) ≤ n * y) :
    ((1 - p) / (1 - y)) ^ n * (p * (1 - y) / (y * (1 - p))) ^ m ≤
      Real.exp (-2 * n * (p - y) ^ 2) := by
  let B := (1 - p) / (1 - y)
  let R := p * (1 - y) / (y * (1 - p))
  have hp := hy.trans hyp
  have hy1 := hyp.trans hp1
  have hB : 0 < B := div_pos (sub_pos.mpr hp1) (sub_pos.mpr hy1)
  have hR : 1 < R := (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hlog : 0 ≤ Real.log R := Real.log_nonneg hR.le
  have he : B ^ n * R ^ m = Real.exp ((n : ℝ) * Real.log B + (m : ℝ) * Real.log R) := by
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hB,
      Real.exp_log (zero_lt_one.trans hR)]
  change B ^ n * R ^ m ≤ _
  rw [he]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right hm hlog
  have hkl := mul_le_mul_of_nonneg_left (binaryDivergence_lower hy hyp.le hp1)
    (Nat.cast_nonneg (α := ℝ) n)
  have hid : Real.log B + y * Real.log R = -binaryDivergence y p :=
    likelihood_log_identity hy hyp hp1
  nlinarith

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open AgrawalGoyalTS.TwoArmed Finset

lemma posterior_inverse_point_bound (j s : ℕ) (hs : s ≤ j) {y p : ℝ}
    (hy : 0 < y) (hy1 : y < 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    binomPMF j p s / binomCDF (j + 1) y s ≤
      (binomPMF j p s / binomPMF j y s) / (1 - y) := by
  have hmem : s ∈ (range (j + 1)).filter (fun k : ℕ => (k : ℝ) ≤ s) := by simp [hs]
  have hpoint : binomPMF j y s ≤ binomCDF j y s :=
    single_le_sum (fun k _ => binomPMF_nonneg hy.le hy1.le j k) hmem
  have hlow : (1 - y) * binomPMF j y s ≤ binomCDF (j + 1) y s :=
    (mul_le_mul_of_nonneg_left hpoint (by linarith)).trans
      (binomCDF_succ_lower hy.le hy1.le j s)
  have hh := div_le_div_of_nonneg_left (binomPMF_nonneg hp hp1 j s)
    (mul_pos (sub_pos.mpr hy1) (binomPMF_pos hy hy1 hs)) hlow
  convert hh using 1 <;> try rfl
  simp only [div_div, mul_comm]

lemma low_band_inverse_bound (j : ℕ) {y p : ℝ}
    (hy : 0 < y) (hyp : y < p) (hp1 : p < 1) :
    (∑ s ∈ (range (j + 1)).filter (fun s : ℕ => (s : ℝ) < j * y),
      binomPMF j p s / binomCDF (j + 1) y s) ≤
      p / (p - y) * Real.exp (-2 * j * (p - y) ^ 2) := by
  let m := Nat.floor ((j : ℝ) * y)
  let B := (1 - p) / (1 - y)
  let R := p * (1 - y) / (y * (1 - p))
  have hp := hy.trans hyp
  have hy1 := hyp.trans hp1
  have hB : 0 < B := div_pos (sub_pos.mpr hp1) (sub_pos.mpr hy1)
  have hR : 1 < R := by
    apply (lt_div_iff₀ (mul_pos hy (sub_pos.mpr hp1))).mpr
    nlinarith
  have hm : (m : ℝ) ≤ j * y := Nat.floor_le (by positivity)
  have hsum : (∑ s ∈ (range (j + 1)).filter (fun s : ℕ => (s : ℝ) < j * y),
      binomPMF j p s / binomCDF (j + 1) y s) ≤
      B ^ j / (1 - y) * ∑ s ∈ range (m + 1), R ^ s := by
    calc
      _ ≤ ∑ s ∈ (range (j + 1)).filter (fun s : ℕ => (s : ℝ) < j * y),
          B ^ j / (1 - y) * R ^ s := by
        apply sum_le_sum
        intro s hs
        have hsj : s ≤ j := by have := (mem_filter.mp hs).1; simpa using this
        have hh := posterior_inverse_point_bound j s hsj hy hy1 hp.le hp1.le
        rw [binom_likelihood_ratio j s hsj hy hy1 hp hp1] at hh
        convert hh using 1 <;> try rfl
        ring
      _ ≤ ∑ s ∈ range (m + 1), B ^ j / (1 - y) * R ^ s := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro s hs
          have hsm : s ≤ m := Nat.le_floor (le_of_lt (mem_filter.mp hs).2)
          exact mem_range.mpr (by omega)
        · intro s _ _
          positivity
      _ = _ := (mul_sum _ _ _).symm
  have hgeom : (∑ s ∈ range (m + 1), R ^ s) ≤ R ^ (m + 1) / (R - 1) := by
    apply (le_div_iff₀ (sub_pos.mpr hR)).mpr
    rw [geom_sum_mul]
    linarith
  have hid : R / ((1 - y) * (R - 1)) = p / (p - y) := by
    dsimp [R]
    field_simp [hy.ne', (sub_pos.mpr hp1).ne', (sub_pos.mpr hy1).ne',
      (sub_pos.mpr hyp).ne']
    ring_nf
    nlinarith [mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hyp))]
  have hrat : B ^ j / (1 - y) * (R ^ (m + 1) / (R - 1)) =
      (p / (p - y)) * (B ^ j * R ^ m) := by
    rw [pow_succ]
    calc
      _ = (R / ((1 - y) * (R - 1))) * (B ^ j * R ^ m) := by
        field_simp
      _ = _ := by rw [hid]
  have hmean := likelihood_at_mean_bound j m hy hyp hp1 hm
  exact hsum.trans ((mul_le_mul_of_nonneg_left hgeom (by positivity)).trans
    (hrat.le.trans (mul_le_mul_of_nonneg_left hmean (by positivity))))

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open AgrawalGoyalTS.TwoArmed Finset

lemma posteriorOdds_eq {y : ℝ} (hy : 0 < y) (hy1 : y < 1) (j s : ℕ) :
    posteriorOdds j s y = (1 - binomCDF (j + 1) y s) / binomCDF (j + 1) y s := by
  have hq := binomCDF_pos hy hy1 (j + 1) (show 0 ≤ (s : ℝ) by positivity)
  unfold posteriorOdds
  field_simp

lemma posterior_inverse_above_mean {y d : ℝ} (hy : 0 < y) (hy1 : y < 1)
    (hd : 0 < d) (hdy : d ≤ 1 - y) (j s : ℕ) (hs : j * y ≤ (s : ℝ)) :
    (binomCDF (j + 1) y s)⁻¹ ≤ 4 * Real.sqrt (j + 1) / d := by
  have hr : 0 < 4 * Real.sqrt (j + 1) := by positivity
  have hlow : d / (4 * Real.sqrt (j + 1)) ≤ binomCDF (j + 1) y s :=
    (div_le_div_of_nonneg_right hdy hr.le).trans (posterior_success_lower hy hy1 j s hs)
  have hh := inv_anti₀ (div_pos hd hr) hlow
  simpa only [inv_div] using hh

lemma binomCDF_complement (n s : ℕ) (p : ℝ) :
    1 - binomCDF n p s =
      ∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (s : ℝ) < k), binomPMF n p k := by
  have h := sum_filter_add_sum_filter_not (range (n + 1))
    (fun k : ℕ => (k : ℝ) ≤ s) (binomPMF n p)
  simp only [not_le] at h
  rw [binomPMF_sum] at h
  change binomCDF n p s + _ = 1 at h
  linarith

lemma posterior_failure_large (j s : ℕ) {y d : ℝ}
    (hy : 0 < y) (hy1 : y < 1) (hd : 0 < d) (_hd1 : d ≤ 1 / 2)
    (hj : 4 ≤ (j : ℝ) * d) (hs : j * (y + d / 2) ≤ (s : ℝ)) :
    1 - binomCDF (j + 1) y s ≤ Real.exp (-j * d ^ 2 / 16) := by
  have hj0 : (1 : ℝ) ≤ j := by
    by_contra h
    have hjnat : j < 1 := by exact_mod_cast (show (j : ℝ) < 1 by linarith)
    have : j = 0 := by omega
    norm_num [this] at hj
  have hthreshold : (j + 1 : ℝ) * y + j * d / 4 ≤ s := by nlinarith
  rw [binomCDF_complement]
  have hsum : (∑ k ∈ (range (j + 1 + 1)).filter (fun k : ℕ => (s : ℝ) < k),
      binomPMF (j + 1) y k) ≤
      ∑ k ∈ (range (j + 1 + 1)).filter
        (fun k : ℕ => (j + 1 : ℝ) * y + j * d / 4 ≤ k), binomPMF (j + 1) y k := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact mem_filter.mpr ⟨(mem_filter.mp hk).1, hthreshold.trans (mem_filter.mp hk).2.le⟩
    · intro k _ _
      exact binomPMF_nonneg hy.le hy1.le (j + 1) k
  have hh := binom_upper_deviation (j + 1) hy.le hy1.le
    (show 0 ≤ (j : ℝ) * d / 4 by positivity)
  simp only [Nat.cast_add, Nat.cast_one] at hh
  apply hsum.trans (hh.trans (Real.exp_le_exp.mpr ?_))
  have hden : 0 < (j + 1 : ℝ) := by positivity
  apply (div_le_iff₀ hden).mpr
  nlinarith [mul_nonneg (show 0 ≤ (j : ℝ) - 1 by linarith) (sq_nonneg d)]

lemma posterior_failure_upper (j s : ℕ) {y d : ℝ}
    (hy : 0 < y) (hy1 : y < 1) (hd : 0 < d) (hd1 : d ≤ 1 / 2)
    (hs : j * (y + d / 2) ≤ (s : ℝ)) :
    1 - binomCDF (j + 1) y s ≤ Real.exp 1 * Real.exp (-j * d ^ 2 / 16) := by
  by_cases hj : 4 ≤ (j : ℝ) * d
  · exact (posterior_failure_large j s hy hy1 hd hd1 hj hs).trans
      (le_mul_of_one_le_left (Real.exp_pos _).le (Real.one_le_exp_iff.mpr (by norm_num)))
  · have hh : (j : ℝ) * d ^ 2 / 16 ≤ 1 := by
      have hp := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hj)) hd.le
      nlinarith
    have he : 1 ≤ Real.exp 1 * Real.exp (-j * d ^ 2 / 16) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    have hq := binomCDF_nonneg hy.le hy1.le (j + 1) s
    linarith

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open AgrawalGoyalTS.TwoArmed Finset

lemma binom_subset_mass (j : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset ℕ) (hS : S ⊆ range (j + 1)) : ∑ s ∈ S, binomPMF j p s ≤ 1 := by
  rw [← binomPMF_sum j p]
  exact sum_le_sum_of_subset_of_nonneg hS (fun s _ _ => binomPMF_nonneg hp hp1 j s)

lemma posterior_middle_mass (j : ℕ) {y p d : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hd : 0 < d) (hpd : p = y + d) :
    (∑ s ∈ (range (j + 1)).filter (fun s : ℕ => (s : ℝ) < j * (y + d / 2)),
      binomPMF j p s) ≤ Real.exp (-j * d ^ 2 / 2) := by
  have hh := binom_lower_deviation j hp hp1 (show 0 ≤ (j : ℝ) * d / 2 by positivity)
  have hsum : (∑ s ∈ (range (j + 1)).filter (fun s : ℕ => (s : ℝ) < j * (y + d / 2)),
      binomPMF j p s) ≤
      ∑ s ∈ (range (j + 1)).filter (fun s : ℕ => (s : ℝ) ≤ j * p - j * d / 2),
        binomPMF j p s := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro s hs
      refine mem_filter.mpr ⟨(mem_filter.mp hs).1, ?_⟩
      rw [hpd]
      nlinarith [(mem_filter.mp hs).2]
    · intro s _ _
      exact binomPMF_nonneg hp hp1 j s
  apply hsum.trans
  by_cases hj : j = 0
  · simpa [hj] using hh
  · have hjr : (j : ℝ) ≠ 0 := by exact_mod_cast hj
    convert hh using 1
    congr 1
    field_simp

lemma posterior_odds_point_upper (j s : ℕ) {y d : ℝ}
    (hy : 0 < y) (hy1 : y < 1) (hd : 0 < d) (hd1 : d ≤ 1 / 2)
    (hdy : d ≤ 1 - y) (hs : j * (y + d / 2) ≤ (s : ℝ)) :
    posteriorOdds j s y ≤ (4 * Real.sqrt (j + 1) / d) *
      (Real.exp 1 * Real.exp (-j * d ^ 2 / 16)) := by
  have hs0 : (j : ℝ) * y ≤ s := by nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hi := posterior_inverse_above_mean hy hy1 hd hdy j s hs0
  have hf := posterior_failure_upper j s hy hy1 hd hd1 hs
  rw [posteriorOdds_eq hy hy1, div_eq_mul_inv]
  have hh := mul_le_mul hf hi (inv_nonneg.mpr (binomCDF_nonneg hy.le hy1.le _ _))
    (by positivity : 0 ≤ Real.exp 1 * Real.exp (-j * d ^ 2 / 16))
  simpa only [mul_comm] using hh

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open AgrawalGoyalTS.TwoArmed Finset

lemma posterior_expectation_envelope (j : ℕ) {y p d : ℝ}
    (hy : 0 < y) (hyp : y < p) (hp1 : p < 1) (hd : 0 < d)
    (hd1 : d ≤ 1 / 2) (hpd : p = y + d) :
    binomExpectation j p (fun s => posteriorOdds j s y) ≤
      (5 + 4 * Real.exp 1) * (Real.sqrt (j + 1) / d) * Real.exp (-j * d ^ 2 / 16) := by
  have hp := hy.trans hyp
  have hy1 := hyp.trans hp1
  have hdy : d ≤ 1 - y := by linarith
  let E := Real.exp (-(j : ℝ) * d ^ 2 / 16)
  let A := 4 * Real.sqrt (j + 1) / d
  let w : ℕ → ℝ := fun s => binomPMF j p s * posteriorOdds j s y
  let L := (range (j + 1)).filter (fun s : ℕ => (s : ℝ) < j * y)
  let M := (range (j + 1)).filter (fun s : ℕ => j * y ≤ (s : ℝ) ∧ (s : ℝ) < j * (y + d / 2))
  let U := (range (j + 1)).filter (fun s : ℕ => j * y ≤ (s : ℝ) ∧ j * (y + d / 2) ≤ (s : ℝ))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hA : 0 ≤ A := by positivity
  have hsplit : binomExpectation j p (fun s => posteriorOdds j s y) =
      (∑ s ∈ L, w s) + (∑ s ∈ M, w s) + ∑ s ∈ U, w s := by
    unfold binomExpectation
    dsimp [L, M, U, w]
    rw [sum_filter, sum_filter, sum_filter, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro s _
    by_cases h1 : (s : ℝ) < j * y
    · simp [h1, not_le.mpr h1]
    · by_cases h2 : (s : ℝ) < j * (y + d / 2)
      · simp [h1, le_of_not_gt h1, h2, not_le.mpr h2]
      · simp [h1, le_of_not_gt h1, h2, le_of_not_gt h2]
  have hlow : (∑ s ∈ L, w s) ≤ E / d := by
    have hbound := low_band_inverse_bound j hy hyp hp1
    have hdif : p - y = d := by linarith
    rw [hdif] at hbound
    have he : Real.exp (-2 * j * d ^ 2) ≤ E := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) (sq_nonneg d)]
    calc
      _ ≤ ∑ s ∈ L, binomPMF j p s / binomCDF (j + 1) y s := by
        apply sum_le_sum
        intro s _
        dsimp [w]
        unfold posteriorOdds
        have hw := binomPMF_nonneg hp.le hp1.le j s
        rw [div_eq_mul_inv]
        nlinarith
      _ ≤ p / d * Real.exp (-2 * j * d ^ 2) := hbound
      _ ≤ (1 / d) * E := mul_le_mul
        (div_le_div_of_nonneg_right hp1.le hd.le) he (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hmiddle : (∑ s ∈ M, w s) ≤ A * E := by
    have hmass := posterior_middle_mass j hp.le hp1.le hd hpd
    have he : Real.exp (-j * d ^ 2 / 2) ≤ E := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) (sq_nonneg d)]
    calc
      _ ≤ A * ∑ s ∈ M, binomPMF j p s := by
        rw [mul_sum]
        apply sum_le_sum
        intro s hs
        have hi := posterior_inverse_above_mean hy hy1 hd hdy j s (mem_filter.mp hs).2.1
        dsimp [w]
        unfold posteriorOdds
        have hw := binomPMF_nonneg hp.le hp1.le j s
        nlinarith
      _ ≤ A * (∑ s ∈ (range (j + 1)).filter (fun s : ℕ => (s : ℝ) < j * (y + d / 2)),
          binomPMF j p s) := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply sum_le_sum_of_subset_of_nonneg
        · intro s hs
          exact mem_filter.mpr ⟨(mem_filter.mp hs).1, (mem_filter.mp hs).2.2⟩
        · intro s _ _
          exact binomPMF_nonneg hp.le hp1.le j s
      _ ≤ A * E := mul_le_mul_of_nonneg_left (hmass.trans he) hA
  have hupper : (∑ s ∈ U, w s) ≤ A * (Real.exp 1 * E) := by
    calc
      _ ≤ (A * (Real.exp 1 * E)) * ∑ s ∈ U, binomPMF j p s := by
        rw [mul_sum]
        apply sum_le_sum
        intro s hs
        have hh := posterior_odds_point_upper j s hy hy1 hd hd1 hdy (mem_filter.mp hs).2.2
        have hm := mul_le_mul_of_nonneg_left hh (binomPMF_nonneg hp.le hp1.le j s)
        simpa only [w, mul_comm] using hm
      _ ≤ (A * (Real.exp 1 * E)) * 1 :=
        mul_le_mul_of_nonneg_left (binom_subset_mass j hp.le hp1.le U (filter_subset _ _))
          (by positivity)
      _ = _ := mul_one _
  have hsqrt : 1 ≤ Real.sqrt (j + 1) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hscale : E / d ≤ (Real.sqrt (j + 1) / d) * E := by
    have hh := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsqrt hd.le) hE
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hh
  rw [hsplit]
  calc
    _ ≤ (Real.sqrt (j + 1) / d) * E + A * E + A * (Real.exp 1 * E) := by linarith
    _ = _ := by dsimp [A, E]; ring

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open Finset

lemma sqrt_scale_bound {d : ℝ} (hd : 0 < d) (j : ℕ) :
    Real.sqrt (j + 1) / d ≤ (j + 1 : ℝ) + 1 / d ^ 2 := by
  have hs : (Real.sqrt (j + 1)) ^ 2 = (j + 1 : ℝ) := Real.sq_sqrt (by positivity)
  have hsq := sq_nonneg (d * Real.sqrt (j + 1) - 1)
  apply (div_le_iff₀ hd).mpr
  have he : ((j + 1 : ℝ) + 1 / d ^ 2) * d =
      ((d * Real.sqrt (j + 1)) ^ 2 + 1) / d := by
    rw [mul_pow, hs]
    field_simp
  rw [he]
  apply (le_div_iff₀ hd).mpr
  have hnon : 0 ≤ d * Real.sqrt (j + 1) := by positivity
  nlinarith

lemma gaussian_envelope_sum {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1 / 2) (J : ℕ) :
    ∑ j ∈ range J, (Real.sqrt (j + 1) / d) * Real.exp (-j * d ^ 2 / 16) ≤
      1056 / d ^ 4 := by
  have ha : 0 < d ^ 2 / 16 := by positivity
  have ha1 : d ^ 2 / 16 ≤ 1 := by nlinarith
  have he (j : ℕ) : -(j : ℝ) * d ^ 2 / 16 = -(d ^ 2 / 16) * j := by ring
  simp_rw [he]
  calc
    _ ≤ ∑ j ∈ range J, ((j + 1 : ℝ) + 1 / d ^ 2) * Real.exp (-(d ^ 2 / 16) * j) := by
      apply sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (sqrt_scale_bound hd j) (Real.exp_pos _).le
    _ = (∑ j ∈ range J, (j + 1 : ℝ) * Real.exp (-(d ^ 2 / 16) * j)) +
        (1 / d ^ 2) * ∑ j ∈ range J, Real.exp (-(d ^ 2 / 16) * j) := by
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ 4 / (d ^ 2 / 16) ^ 2 + (1 / d ^ 2) * (2 / (d ^ 2 / 16)) :=
      add_le_add (exponential_weighted_prefix_bound ha ha1 J)
        (mul_le_mul_of_nonneg_left (exponential_prefix_bound ha ha1 J) (by positivity))
    _ = _ := by ring

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open AgrawalGoyalTS.TwoArmed Finset

lemma binomCDF_last (j : ℕ) (y : ℝ) :
    binomCDF (j + 1) y j = 1 - y ^ (j + 1) := by
  have h := binomCDF_complement (j + 1) j y
  have he : (range (j + 1 + 1)).filter (fun k : ℕ => (j : ℝ) < k) = {j + 1} := by
    ext k
    simp only [mem_filter, mem_range, Nat.cast_lt, mem_singleton]
    omega
  rw [he, sum_singleton] at h
  simp only [binomPMF, Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, mul_one] at h
  linarith

lemma binomExpectation_one (j : ℕ) (f : ℕ → ℝ) : binomExpectation j 1 f = f j := by
  unfold binomExpectation
  rw [sum_eq_single j]
  · simp [binomPMF]
  · intro k hk hkj
    have hklt : k < j := by have := mem_range.mp hk; omega
    have hz : j - k ≠ 0 := by omega
    simp [binomPMF, zero_pow hz]
  · simp

lemma posteriorOdds_endpoint_bound {y : ℝ} (hy : 0 < y) (hy1 : y < 1) (j : ℕ) :
    posteriorOdds j j y ≤ y ^ j / (1 - y) := by
  have hq : 0 < 1 - y ^ (j + 1) := by
    rw [← binomCDF_last]
    exact binomCDF_pos hy hy1 (j + 1) (by positivity)
  have hypow : y ^ (j + 1) ≤ y := by
    rw [pow_succ]
    exact mul_le_of_le_one_left hy.le (pow_le_one₀ hy.le hy1.le)
  rw [posteriorOdds_eq hy hy1, binomCDF_last]
  have he : 1 - (1 - y ^ (j + 1)) = y ^ (j + 1) := by ring
  rw [he]
  calc
    _ ≤ y ^ (j + 1) / (1 - y) := div_le_div_of_nonneg_left (by positivity)
      (sub_pos.mpr hy1) (by linarith)
    _ ≤ y ^ j / (1 - y) := div_le_div_of_nonneg_right
      (by rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) hy1.le)
      (sub_pos.mpr hy1).le

lemma posterior_endpoint_sum {y : ℝ} (hy : 0 < y) (hy1 : y < 1) (J : ℕ) :
    ∑ j ∈ range J, binomExpectation j 1 (fun s => posteriorOdds j s y) ≤
      1 / (1 - y) ^ 2 := by
  simp_rw [binomExpectation_one]
  calc
    _ ≤ ∑ j ∈ range J, y ^ j / (1 - y) :=
      sum_le_sum (fun j _ => posteriorOdds_endpoint_bound hy hy1 j)
    _ = (∑ j ∈ range J, y ^ j) / (1 - y) := (sum_div _ _ _).symm
    _ ≤ (1 / (1 - y)) / (1 - y) := div_le_div_of_nonneg_right
      (geometric_prefix_bound hy.le hy1 J) (sub_pos.mpr hy1).le
    _ = _ := by rw [div_div, pow_two]

end ThompsonSamplingProof


namespace ThompsonSamplingProof

open AgrawalGoyalTS.TwoArmed Finset

lemma posterior_prefix_interior {y p d : ℝ}
    (hy : 0 < y) (hyp : y < p) (hp1 : p < 1) (hd : 0 < d)
    (hd1 : d ≤ 1 / 2) (hpd : p = y + d) (J : ℕ) :
    (∑ j ∈ range J, binomExpectation j p (fun s => posteriorOdds j s y)) ≤
      ((5 + 4 * Real.exp 1) * 1056) / d ^ 4 := by
  calc
    _ ≤ ∑ j ∈ range J, (5 + 4 * Real.exp 1) *
        ((Real.sqrt (j + 1) / d) * Real.exp (-j * d ^ 2 / 16)) := by
      apply sum_le_sum
      intro j _
      simpa only [mul_assoc] using posterior_expectation_envelope j hy hyp hp1 hd hd1 hpd
    _ = (5 + 4 * Real.exp 1) * ∑ j ∈ range J,
        (Real.sqrt (j + 1) / d) * Real.exp (-j * d ^ 2 / 16) := (mul_sum _ _ _).symm
    _ ≤ (5 + 4 * Real.exp 1) * (1056 / d ^ 4) :=
      mul_le_mul_of_nonneg_left (gaussian_envelope_sum hd hd1 J) (by positivity)
    _ = _ := by ring

 theorem posterior_waiting_sum : ∃ C : ℝ, 0 < C ∧
    ∀ ν μ : ℝ, 0 ≤ ν → ν < μ → μ ≤ 1 → ∀ J : ℕ,
      (∑ j ∈ range J, binomExpectation j μ (fun s => posteriorOdds j s ((μ + ν) / 2))) ≤
        C / ((μ - ν) / 2) ^ 4 := by
  let C := (5 + 4 * Real.exp 1) * 1056
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [Real.exp_pos 1]
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC, ?_⟩
  intro ν μ hν hνμ hμ J
  let d := (μ - ν) / 2
  let y := (μ + ν) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hd1 : d ≤ 1 / 2 := by dsimp [d]; linarith
  have hy : 0 < y := by dsimp [y]; linarith
  have hym : y < μ := by dsimp [y]; linarith
  have hy1 : y < 1 := hym.trans_le hμ
  have hmd : μ = y + d := by dsimp [y, d]; ring
  change (∑ j ∈ range J, binomExpectation j μ (fun s => posteriorOdds j s y)) ≤ C / d ^ 4
  rcases lt_or_eq_of_le hμ with hμ | rfl
  · exact posterior_prefix_interior hy hym hμ hd hd1 hmd J
  · have hyd : 1 - y = d := by linarith
    have hh := posterior_endpoint_sum hy hy1 J
    rw [hyd] at hh
    apply hh.trans
    have hdp : 0 < d ^ 4 := by positivity
    apply (div_le_div_iff₀ (by positivity : 0 < d ^ 2) hdp).mpr
    have hd2 : d ^ 2 ≤ 1 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hC (sq_nonneg d)
    nlinarith [mul_nonneg (sq_nonneg d) (show 0 ≤ 1 - d ^ 2 by linarith)]

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory ProbabilityTheory AgrawalGoyalTS.TwoArmed

 theorem calendar_count_bound {C : ℝ}
    (hC : ∀ ν μ : ℝ, 0 ≤ ν → ν < μ → μ ≤ 1 → ∀ J : ℕ,
      (∑ j ∈ Finset.range J, binomExpectation j μ (fun s => posteriorOdds j s ((μ+ν)/2))) ≤
        C / ((μ-ν)/2)^4)
    (p : Fin 2 → unitInterval) (hp : (p 1 : ℝ) < p 0) (T : ℕ) (hT : 2 ≤ T) :
    (∫ a : Calendar × CoinStack,
      (historyPlays (stackHistory (fromCalendar a.1,a.2)) T 1 : ℝ)
      ∂(Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod (coinStackLaw p)) ≤
      (Nat.ceil (32*Real.log T/((p 0 : ℝ)-(p 1 : ℝ))^2) : ℝ) +
        C / (((p 0 : ℝ)-(p 1 : ℝ))/2)^4 + 2/(T : ℝ)^2 := by
  have h0 : 0 ≤ (p 0 : ℝ) ∧ (p 0 : ℝ) ≤ 1 := (p 0).property
  have h1 : 0 ≤ (p 1 : ℝ) ∧ (p 1 : ℝ) ≤ 1 := (p 1).property
  have hb := expected_pull_budget p
    (Nat.ceil (32*Real.log T/((p 0 : ℝ)-(p 1 : ℝ))^2)) T
    (y := ((p 0 : ℝ)+(p 1 : ℝ))/2) (by linarith) (by linarith)
  have hs := hC (p 1) (p 0) h1.1 hp h0.2 (T+1)
  have he := saturation_expected_penalty p hp T hT
  dsimp only at he
  linarith

end ThompsonSamplingProof


namespace ThompsonSamplingProof

lemma saturation_ceiling_bound {Δ : ℝ} (_hΔ : 0 < Δ) {T : ℕ} (hT : 2 ≤ T) :
    (Nat.ceil (32 * Real.log T / Δ ^ 2) : ℝ) ≤ 32 * Real.log T / Δ ^ 2 + 1 := by
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  exact (Nat.ceil_lt_add_one (div_nonneg
    (mul_nonneg (by norm_num) (Real.log_nonneg hTr)) (sq_nonneg Δ))).le

lemma regret_rate_from_count {C Δ b : ℝ} (hC : 0 ≤ C)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) {T L : ℕ} (hT : 2 ≤ T)
    (hL : (L : ℝ) ≤ 32 * Real.log T / Δ ^ 2 + 1)
    (hb : b ≤ L + C / (Δ / 2) ^ 4 + 2 / (T : ℝ) ^ 2) :
    Δ * b ≤ (35 + 16 * C) * (Real.log T / Δ + 1 / Δ ^ 3) := by
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have hlog : 0 ≤ Real.log T / Δ := div_nonneg (Real.log_nonneg hTr) hΔ.le
  have htail : 2 / (T : ℝ) ^ 2 ≤ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < (T : ℝ) ^ 2)).mpr
    nlinarith
  have hdsmall : Δ ≤ 1 / Δ ^ 3 := by
    apply (le_div_iff₀ (by positivity : 0 < Δ ^ 3)).mpr
    have hh : Δ ^ 4 ≤ 1 := pow_le_one₀ hΔ.le hΔ1
    nlinarith
  have he : Δ * (32 * Real.log T / Δ ^ 2 + 1 + C / (Δ / 2) ^ 4 + 2) =
      32 * (Real.log T / Δ) + 16 * C * (1 / Δ ^ 3) + 3 * Δ := by
    field_simp [hΔ.ne']
    ring
  calc
    Δ * b ≤ Δ * (32 * Real.log T / Δ ^ 2 + 1 + C / (Δ / 2) ^ 4 + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hΔ.le
    _ = 32 * (Real.log T / Δ) + 16 * C * (1 / Δ ^ 3) + 3 * Δ := he
    _ ≤ (35 + 16 * C) * (Real.log T / Δ + 1 / Δ ^ 3) := by
      nlinarith [mul_nonneg hC hlog]

 theorem regret_rate_constant {C : ℝ} (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (Δ b : ℝ) (T : ℕ), 0 < Δ → Δ ≤ 1 → 2 ≤ T →
      b ≤ (Nat.ceil (32 * Real.log T / Δ ^ 2) : ℝ) + C / (Δ / 2) ^ 4 +
        2 / (T : ℝ) ^ 2 →
      Δ * b ≤ D * (Real.log T / Δ + 1 / Δ ^ 3) := by
  refine ⟨35 + 16 * C, by positivity, ?_⟩
  intro Δ b T hΔ hΔ1 hT hb
  exact regret_rate_from_count hC hΔ hΔ1 hT (saturation_ceiling_bound hΔ hT) hb

end ThompsonSamplingProof


namespace ThompsonSamplingProof
open MeasureTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

 theorem full_native_regret :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : StochasticBandit 2, (∀ i, ν.P i (Set.Icc 0 1) = 1) →
      banditArmMean ν 1 < banditArmMean ν 0 → ∀ T : ℕ, 2 ≤ T →
        tsRegret ν T ≤
          ENNReal.ofReal (C * (Real.log T / (banditArmMean ν 0 - banditArmMean ν 1) +
            1 / (banditArmMean ν 0 - banditArmMean ν 1) ^ 3)) := by
  obtain ⟨C,hC,hwait⟩ := posterior_waiting_sum
  obtain ⟨D,hD,hrate⟩ := regret_rate_constant hC.le
  refine ⟨D,hD,?_⟩
  intro ν hν hp T hT
  let p : Fin 2 → unitInterval := fun i => meanParameter (ν.P i) (hν i)
  have he (i : Fin 2) : (p i : ℝ) = banditArmMean ν i := rfl
  have hp' : (p 1 : ℝ) < p 0 := by simpa only [he] using hp
  have hb := calendar_count_bound hwait p hp' T hT
  have ht := native_calendar_plays ν hν T 1
  change (∫ ω, (tsPlays ω T 1 : ℝ) ∂tsLaw ν) =
    (∫ a : Calendar × CoinStack,
      (historyPlays (stackHistory (fromCalendar a.1,a.2)) T 1 : ℝ)
      ∂(Measure.infinitePi (fun _ : ℕ => sliceLaw)).prod (coinStackLaw p)) at ht
  rw [← ht] at hb
  simp only [he] at hb
  have hΔ : 0 < banditArmMean ν 0-banditArmMean ν 1 := sub_pos.mpr hp
  have hΔ1 : banditArmMean ν 0-banditArmMean ν 1 ≤ 1 := by
    have h0 := (p 0).property.2
    have h1 := (p 1).property.1
    rw [he] at h0 h1
    linarith
  rw [regret_eq_count ν hp.le T]
  exact ENNReal.ofReal_le_ofReal (hrate _ _ T hΔ hΔ1 hT hb)

end ThompsonSamplingProof


open MeasureTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed

namespace AgrawalGoyalTS.TwoArmed

/-- Theorem 1 (p. 3): there is an absolute constant `C > 0` such that for every two-armed
stochastic bandit with rewards supported in `[0,1]` and `μ₁ > μ₂` (arm `0` is the paper's arm 1),
and every horizon `T ≥ 2`, Thompson Sampling (Algorithm 2) has expected regret
`E[R(T)] ≤ C (ln T / Δ + 1 / Δ³)`, `Δ = μ₁ - μ₂`. -/
theorem thompson_sampling_two_armed_regret :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : StochasticBandit 2, (∀ i, ν.P i (Set.Icc 0 1) = 1) →
      banditArmMean ν 1 < banditArmMean ν 0 → ∀ T : ℕ, 2 ≤ T →
        tsRegret ν T ≤
          ENNReal.ofReal (C * (Real.log T / (banditArmMean ν 0 - banditArmMean ν 1) +
            1 / (banditArmMean ν 0 - banditArmMean ν 1) ^ 3)) := by
  exact ThompsonSamplingProof.full_native_regret 

end AgrawalGoyalTS.TwoArmed

open AgrawalGoyalTS.TwoArmed

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : StochasticBandit 2, (∀ i, ν.P i (Set.Icc 0 1) = 1) →
      banditArmMean ν 1 < banditArmMean ν 0 → ∀ T : ℕ, 2 ≤ T →
        tsRegret ν T ≤
          ENNReal.ofReal (C * (Real.log T / (banditArmMean ν 0 - banditArmMean ν 1) +
            1 / (banditArmMean ν 0 - banditArmMean ν 1) ^ 3)) := AgrawalGoyalTS.TwoArmed.thompson_sampling_two_armed_regret 
