-- Prove2me | solution 1 for AgrawalGoyalTS.NArmed.saturated_regret_interval_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:19:35.111581+00:00
-- url     : https://prove2.me/submissions/05628fa8-861e-4e6c-be9b-56293c06c23b

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_AgrawalGoyalTS_NArmed_BetaBinomial
import Definitions.Def_AgrawalGoyalTS_NArmed_ThompsonSampling
import Definitions.Def_AgrawalGoyalTS_NArmed_Saturation

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed AgrawalGoyalTS.NArmed

namespace P549

variable {N : ℕ} [NeZero N]

/-! ## L1 combinatorics -/

lemma tsCounts_succ' (ω : TSOmega N) (t : ℕ) :
    tsCounts ω (t + 1) =
      if ((ω.2.2 (tsArm ω t, t) : ℝ) < ω.2.1 (tsArm ω t, t)) then
        (Function.update (tsCounts ω t).1 (tsArm ω t) ((tsCounts ω t).1 (tsArm ω t) + 1),
          (tsCounts ω t).2)
      else ((tsCounts ω t).1,
        Function.update (tsCounts ω t).2 (tsArm ω t) ((tsCounts ω t).2 (tsArm ω t) + 1)) := by
  rfl

lemma tsPlays_succ (ω : TSOmega N) (t : ℕ) (i : Fin N) :
    tsPlays ω (t + 1) i = tsPlays ω t i + if tsArm ω t = i then 1 else 0 := by
  unfold tsPlays
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma tsPlays_eq (ω : TSOmega N) (t : ℕ) (i : Fin N) :
    tsPlays ω t i = (tsCounts ω t).1 i + (tsCounts ω t).2 i := by
  induction t with
  | zero => simp [tsPlays, tsCounts]
  | succ t ih =>
    rw [tsPlays_succ, ih, tsCounts_succ']
    by_cases ha : tsArm ω t = i
    · subst ha
      split_ifs <;> simp <;> omega
    · have hb : i ≠ tsArm ω t := Ne.symm ha
      split_ifs <;> simp [Function.update_of_ne hb, ha]

lemma tsS_eq (ω : TSOmega N) (t : ℕ) (i : Fin N) :
    (tsCounts ω t).1 i =
      ((Finset.range t).filter (fun u => tsArm ω u = i ∧ tsCoin ω u = true)).card := by
  induction t with
  | zero => simp [tsCounts]
  | succ t ih =>
    rw [Finset.range_add_one, Finset.filter_insert, tsCounts_succ']
    have hc : tsCoin ω t = decide ((ω.2.2 (tsArm ω t, t) : ℝ) < ω.2.1 (tsArm ω t, t)) := rfl
    by_cases ha : tsArm ω t = i
    · subst ha
      by_cases hco : ((ω.2.2 (tsArm ω t, t) : ℝ) < ω.2.1 (tsArm ω t, t))
      · rw [if_pos hco, if_pos ⟨rfl, by simp [hc, hco]⟩, Finset.card_insert_of_notMem (by simp)]
        simp [ih]
      · rw [if_neg hco, if_neg (by simp [hc, hco])]
        exact ih
    · rw [if_neg (show ¬(tsArm ω t = i ∧ tsCoin ω t = true) from fun h => ha h.1)]
      split_ifs <;> simp [Function.update_of_ne (Ne.symm ha), ih]

lemma tsPlays_mono (ω : TSOmega N) (i : Fin N) {t t' : ℕ} (h : t ≤ t') :
    tsPlays ω t i ≤ tsPlays ω t' i := by
  unfold tsPlays
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

lemma stack_eq (ω : TSOmega N) (t j : ℕ) (h : tsPlays ω t 0 = j) :
    stackSuccesses ω 0 j = (tsCounts ω t).1 0 := by
  rw [tsS_eq]
  unfold stackSuccesses
  rw [← Set.ncard_coe_finset]
  congr 1
  ext u
  simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range]
  constructor
  · rintro ⟨ha, hp, hc⟩
    refine ⟨?_, ha, hc⟩
    by_contra hu
    push_neg at hu
    have := tsPlays_mono ω 0 hu
    omega
  · rintro ⟨hu, ha, hc⟩
    refine ⟨ha, ?_, hc⟩
    have h1 := tsPlays_mono ω 0 (Nat.succ_le_of_lt hu)
    rw [tsPlays_succ, if_pos ha] at h1
    omega

/-! ## L2 locality -/

def updW (k0 : Fin N × ℕ × ℕ × ℕ) (c : ℝ) (ω : TSOmega N) : TSOmega N :=
  (Function.update ω.1 k0 c, ω.2)

lemma tsCounts_updW (k0 : Fin N × ℕ × ℕ × ℕ) (c : ℝ) (ω : TSOmega N) :
    ∀ u, u ≤ k0.2.1 → tsCounts (updW k0 c ω) u = tsCounts ω u := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
    intro hu
    have ih' := ih (by omega)
    have harm : tsArm (updW k0 c ω) u = tsArm ω u := by
      unfold tsArm tsTheta tsSuccesses tsFailures
      rw [ih']
      congr 1
      funext i
      simp only [updW]
      rw [Function.update_of_ne]
      intro h
      have := congrArg (fun x => x.2.1) h
      simp at this
      omega
    rw [tsCounts_succ', tsCounts_succ', harm, ih'] <;> rfl

lemma tsPlays_updW (k0 : Fin N × ℕ × ℕ × ℕ) (c : ℝ) (ω : TSOmega N) (u : ℕ)
    (hu : u ≤ k0.2.1) : tsPlays (updW k0 c ω) u = tsPlays ω u := by
  funext i
  rw [tsPlays_eq, tsPlays_eq, tsCounts_updW k0 c ω u hu]

lemma sat_congr (ν : StochasticBandit N) (T : ℕ) {ω ω' : TSOmega N} {t t' : ℕ}
    (h : tsPlays ω t = tsPlays ω' t') : saturated ν T ω t = saturated ν T ω' t' := by
  unfold saturated
  rw [h]

lemma best_congr (ν : StochasticBandit N) (T : ℕ) {ω ω' : TSOmega N} {t t' : ℕ}
    (h : tsPlays ω t = tsPlays ω' t') : bestSaturated ν T ω t = bestSaturated ν T ω' t' := by
  unfold bestSaturated
  rw [sat_congr ν T h]

/-! ## L3 measurability -/

lemma mset_factor {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] {κ : Ω → β} (hκ : Measurable κ) (P : Ω → Prop)
    (hP : ∀ ω ω', κ ω = κ ω' → P ω → P ω') : MeasurableSet {ω | P ω} := by
  have : {ω | P ω} = κ ⁻¹' (κ '' {ω | P ω}) := by
    ext ω
    constructor
    · intro h
      exact ⟨ω, h, rfl⟩
    · rintro ⟨ω', h', e⟩
      exact hP _ _ e h'
  rw [this]
  exact hκ (Set.to_countable _).measurableSet

lemma argmaxMin_measurable : Measurable (argmaxMin : (Fin N → ℝ) → Fin N) := by
  let d : (Fin N → ℝ) → (Fin N → Bool) := fun θ k => decide (∀ j, θ j ≤ θ k)
  have hd : Measurable d := by
    refine measurable_pi_lambda _ (fun k => measurable_to_bool ?_)
    have : (fun θ : Fin N → ℝ => d θ k) ⁻¹' {true} = ⋂ j, {θ | θ j ≤ θ k} := by
      ext θ
      simp [d]
    rw [this]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le (measurable_pi_apply j) (measurable_pi_apply k)
  refine measurable_to_countable' fun i => mset_factor hd (fun θ => argmaxMin θ = i) ?_
  intro θ θ' h hθ
  have hθ' : argmaxMin θ = i := hθ
  show argmaxMin θ' = i
  have hS : (Finset.univ.filter (fun i => ∀ j, θ j ≤ θ i)) =
      Finset.univ.filter (fun i => ∀ j, θ' j ≤ θ' i) := by
    ext k
    have := congrFun h k
    simp only [d, decide_eq_decide] at this
    simp [this]
  rw [← hθ']
  unfold argmaxMin
  rw [hS]

lemma tsCounts_measurable (t : ℕ) : Measurable (fun ω : TSOmega N => tsCounts ω t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    let F : TSOmega N × ((Fin N → ℕ) × (Fin N → ℕ)) → (Fin N → ℕ) × (Fin N → ℕ) := fun p =>
      if ((p.1.2.2 (argmaxMin (fun i => p.1.1 (i, t, p.2.1 i, p.2.2 i)), t) : ℝ) <
          p.1.2.1 (argmaxMin (fun i => p.1.1 (i, t, p.2.1 i, p.2.2 i)), t)) then
        (Function.update p.2.1 (argmaxMin (fun i => p.1.1 (i, t, p.2.1 i, p.2.2 i)))
          (p.2.1 (argmaxMin (fun i => p.1.1 (i, t, p.2.1 i, p.2.2 i))) + 1), p.2.2)
      else (p.2.1, Function.update p.2.2 (argmaxMin (fun i => p.1.1 (i, t, p.2.1 i, p.2.2 i)))
          (p.2.2 (argmaxMin (fun i => p.1.1 (i, t, p.2.1 i, p.2.2 i))) + 1))
    have hF : Measurable F := by
      apply measurable_from_prod_countable_left
      intro c
      let G : TSOmega N × Fin N → (Fin N → ℕ) × (Fin N → ℕ) := fun q =>
        if ((q.1.2.2 (q.2, t) : ℝ) < q.1.2.1 (q.2, t)) then
          (Function.update c.1 q.2 (c.1 q.2 + 1), c.2)
        else (c.1, Function.update c.2 q.2 (c.2 q.2 + 1))
      have hG : Measurable G := by
        apply measurable_from_prod_countable_left
        intro a
        show Measurable fun x : TSOmega N =>
          if ((x.2.2 (a, t) : ℝ) < x.2.1 (a, t)) then (Function.update c.1 a (c.1 a + 1), c.2)
          else (c.1, Function.update c.2 a (c.2 a + 1))
        refine Measurable.ite ?_ measurable_const measurable_const
        exact measurableSet_lt
          (measurable_subtype_coe.comp ((measurable_pi_apply (a, t)).comp
            (measurable_snd.comp measurable_snd)))
          ((measurable_pi_apply (a, t)).comp (measurable_fst.comp measurable_snd))
      have hA : Measurable (fun ω : TSOmega N => argmaxMin (fun i => ω.1 (i, t, c.1 i, c.2 i))) :=
        argmaxMin_measurable.comp
          (measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_fst)
      exact hG.comp (measurable_id.prodMk hA)
    have : (fun ω : TSOmega N => tsCounts ω (t + 1)) = F ∘ (fun ω => (ω, tsCounts ω t)) := by
      funext ω
      rfl
    rw [this]
    exact hF.comp (measurable_id.prodMk ih)

/-! ## L4 freshness -/

noncomputable abbrev μW (N : ℕ) : Fin N × ℕ × ℕ × ℕ → Measure ℝ :=
  fun k => betaMeasure ((k.2.2.1 : ℝ) + 1) ((k.2.2.2 : ℝ) + 1)

def updf (k0 : Fin N × ℕ × ℕ × ℕ) (p : ℝ × (Fin N × ℕ × ℕ × ℕ → ℝ)) :
    Fin N × ℕ × ℕ × ℕ → ℝ :=
  Function.update p.2 k0 p.1

lemma updf_measurable (k0 : Fin N × ℕ × ℕ × ℕ) : Measurable (updf (N := N) k0) :=
  measurable_update'.comp measurable_swap

lemma upd_map (k0 : Fin N × ℕ × ℕ × ℕ) :
    ((μW N k0).prod (Measure.infinitePi (μW N))).map (updf k0) =
      Measure.infinitePi (μW N) := by
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply (updf_measurable k0)
    (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  by_cases hk : k0 ∈ s
  · have : updf k0 ⁻¹' (Set.pi (↑s) t) = t k0 ×ˢ Set.pi (↑(s.erase k0)) t := by
      ext ⟨c, w⟩
      simp only [updf, Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
        Finset.mem_erase]
      constructor
      · intro h
        refine ⟨by simpa using h k0 hk, fun i ⟨hne, hi⟩ => ?_⟩
        simpa [Function.update_of_ne hne] using h i hi
      · rintro ⟨h1, h2⟩ i hi
        by_cases hik : i = k0
        · subst hik
          simpa using h1
        · simpa [Function.update_of_ne hik] using h2 i ⟨hik, hi⟩
    rw [this, Measure.prod_prod, Measure.infinitePi_pi (μW N) (fun i _ => ht i)]
    exact Finset.mul_prod_erase s (fun i => μW N i (t i)) hk
  · have : updf k0 ⁻¹' (Set.pi (↑s) t) = Set.univ ×ˢ Set.pi (↑s) t := by
      ext ⟨c, w⟩
      simp only [updf, Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
        Set.mem_univ, true_and]
      refine forall₂_congr fun i hi => ?_
      have hik : i ≠ k0 := fun h => hk (h ▸ hi)
      simp [Function.update_of_ne hik]
    rw [this, Measure.prod_prod, Measure.infinitePi_pi (μW N) (fun i _ => ht i), measure_univ, one_mul]

lemma fresh (ν : StochasticBandit N) (k0 : Fin N × ℕ × ℕ × ℕ) (y : ℝ)
    (H : TSOmega N → ENNReal) (hH : Measurable H)
    (hinv : ∀ c ω, H (Function.update ω.1 k0 c, ω.2) = H ω) :
    ∫⁻ ω, (Set.Iic y).indicator 1 (ω.1 k0) * H ω ∂(tsLaw ν) =
      μW N k0 (Set.Iic y) * ∫⁻ ω, H ω ∂(tsLaw ν) := by
  set R := (Measure.infinitePi (fun k : Fin N × ℕ => ν.P k.1)).prod
    (Measure.infinitePi (fun _ : Fin N × ℕ => (volume : Measure unitInterval))) with hR
  have hlaw : tsLaw ν = (Measure.infinitePi (μW N)).prod R := rfl
  have hm := updf_measurable (N := N) k0
  have h1 : tsLaw ν =
      (((μW N k0).prod (Measure.infinitePi (μW N))).prod R).map (Prod.map (updf k0) id) := by
    rw [hlaw, ← Measure.map_prod_map _ _ hm measurable_id, upd_map, Measure.map_id]
  have hI : Measurable (fun ω : TSOmega N => (Set.Iic y).indicator (1 : ℝ → ENNReal) (ω.1 k0)) :=
    (measurable_one.indicator measurableSet_Iic).comp ((measurable_pi_apply k0).comp measurable_fst)
  have hI1 : Measurable ((Set.Iic y).indicator (1 : ℝ → ENNReal)) :=
    measurable_one.indicator measurableSet_Iic
  have hIH : Measurable (fun ω : TSOmega N => (Set.Iic y).indicator (1 : ℝ → ENNReal) (ω.1 k0) * H ω) :=
    hI.mul hH
  conv_lhs => rw [h1]
  rw [lintegral_map hIH (hm.prodMap measurable_id)]
  have hpt : ∀ x : (ℝ × (Fin N × ℕ × ℕ × ℕ → ℝ)) × ((Fin N × ℕ → ℝ) × (Fin N × ℕ → unitInterval)),
      (Set.Iic y).indicator (1 : ℝ → ENNReal) ((Prod.map (updf k0) id x).1 k0) *
        H (Prod.map (updf k0) id x) =
      (Set.Iic y).indicator 1 x.1.1 * H (x.1.2, x.2) := by
    intro x
    have e1 : (Prod.map (updf k0) id x).1 k0 = x.1.1 := by
      simp [updf]
    have e2 : H (Prod.map (updf k0) id x) = H (x.1.2, x.2) := hinv x.1.1 (x.1.2, x.2)
    rw [e1, e2]
  simp_rw [hpt]
  have hPA := measurePreserving_prodAssoc (μW N k0) (Measure.infinitePi (μW N)) R
  have e3 : ∫⁻ x : (ℝ × (Fin N × ℕ × ℕ × ℕ → ℝ)) × ((Fin N × ℕ → ℝ) × (Fin N × ℕ → unitInterval)),
      (Set.Iic y).indicator (1 : ℝ → ENNReal) x.1.1 * H (x.1.2, x.2)
        ∂(((μW N k0).prod (Measure.infinitePi (μW N))).prod R) =
      ∫⁻ z, (Set.Iic y).indicator (1 : ℝ → ENNReal) z.1 * H z.2
        ∂((μW N k0).prod ((Measure.infinitePi (μW N)).prod R)) :=
    hPA.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
      (fun z => (Set.Iic y).indicator (1 : ℝ → ENNReal) z.1 * H z.2)
  rw [e3, lintegral_prod_mul hI1.aemeasurable hH.aemeasurable, lintegral_indicator_one measurableSet_Iic,
    hlaw]


instance tsLaw_prob (ν : StochasticBandit N) : IsProbabilityMeasure (tsLaw ν) := by
  unfold tsLaw
  infer_instance

/-! ## Saturation facts -/

lemma best_prop (ν : StochasticBandit N) (T : ℕ) {ω : TSOmega N} {u : ℕ} {a : Fin N}
    (ha : a ∈ saturated ν T ω u) (hb : bestSaturated ν T ω u = a) :
    ∀ i ∈ saturated ν T ω u, banditArmMean ν i ≤ banditArmMean ν a := by
  simp only [bestSaturated] at hb
  split_ifs at hb with h
  · have hm := Finset.min'_mem _ h
    rw [hb] at hm
    exact (Finset.mem_filter.1 hm).2
  · exfalso
    subst hb
    simp [saturated] at ha

noncomputable def gg (T : ℕ) (q : ENNReal) (k : ℕ) : ENNReal :=
  ∑ i ∈ Finset.range (T - k), q ^ (i + 1)

noncomputable def qq (s j : ℕ) (y : ℝ) : ENNReal :=
  betaMeasure ((s : ℝ) + 1) (((j - s : ℕ) : ℝ) + 1) (Set.Iic y)

lemma gg_step (T : ℕ) (q : ENNReal) {k : ℕ} (hk : k < T) :
    q * (1 + gg T q (k + 1)) = gg T q k := by
  unfold gg
  obtain ⟨n, hn⟩ : ∃ n, T - k = n + 1 := ⟨T - k - 1, by omega⟩
  have hn' : T - (k + 1) = n := by omega
  rw [hn, hn', Finset.sum_range_succ', mul_add, mul_one, Finset.mul_sum, add_comm q]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · simp

/-! ## The process for fixed `a`, `s` -/

section Proc
variable (ν : StochasticBandit N) (T j s : ℕ) (a : Fin N) (y : ℝ)

def trial (ω : TSOmega N) (u : ℕ) : Prop :=
  u < T ∧ tsPlays ω u 0 = j ∧ (tsCounts ω u).1 0 = s ∧ a ∈ saturated ν T ω u ∧
    bestSaturated ν T ω u = a

def fail (ω : TSOmega N) (u : ℕ) : Prop :=
  trial ν T j s a ω u ∧ ω.1 (0, u, s, j - s) ≤ y

def succ (ω : TSOmega N) (u : ℕ) : Prop :=
  trial ν T j s a ω u ∧ y < ω.1 (0, u, s, j - s)

open Classical in
noncomputable def st (ω : TSOmega N) : ℕ → ℕ
  | 0 => 0
  | u + 1 => if fail ν T j s a y ω u then st ω u + 1
      else if succ ν T j s a y ω u then 0 else st ω u

open Classical in
noncomputable def Fc (ω : TSOmega N) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun u => fail ν T j s a y ω u)).card

open Classical in
noncomputable def Sc (ω : TSOmega N) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun u => succ ν T j s a y ω u)).card

def Bv (ω : TSOmega N) : Prop := ∃ u < T, tsPlays ω u 0 = j ∧ (tsCounts ω u).1 0 = s

open Classical in
noncomputable def LHSf (t : ℕ) (ω : TSOmega N) : ENNReal :=
  (Fc ν T j s a y ω t : ENNReal) + if Bv T j s ω then gg T (qq s j y) (st ν T j s a y ω t) else 0

open Classical in
noncomputable def RHSf (t : ℕ) (ω : TSOmega N) : ENNReal :=
  if Bv T j s ω then gg T (qq s j y) 0 * ((Sc ν T j s a y ω t : ENNReal) + 1) else 0

open Classical in
noncomputable def Xf (t : ℕ) (ω : TSOmega N) : ENNReal :=
  (Fc ν T j s a y ω t : ENNReal) +
    if Bv T j s ω ∧ ¬ trial ν T j s a ω t then gg T (qq s j y) (st ν T j s a y ω t) else 0

open Classical in
noncomputable def Ff (t : ℕ) (ω : TSOmega N) : ENNReal :=
  if fail ν T j s a y ω t then 1 + gg T (qq s j y) (st ν T j s a y ω t + 1) else 0

open Classical in
noncomputable def Sf (t : ℕ) (ω : TSOmega N) : ENNReal :=
  if succ ν T j s a y ω t then 1 else 0

open Classical in
noncomputable def Hf (t : ℕ) (ω : TSOmega N) : ENNReal :=
  if trial ν T j s a ω t then 1 + gg T (qq s j y) (st ν T j s a y ω t + 1) else 0

open Classical in
noncomputable def Gf (t : ℕ) (ω : TSOmega N) : ENNReal :=
  if trial ν T j s a ω t then gg T (qq s j y) (st ν T j s a y ω t) else 0

lemma trial_congr {ω ω' : TSOmega N} {u : ℕ} (h : tsCounts ω u = tsCounts ω' u) :
    trial ν T j s a ω u ↔ trial ν T j s a ω' u := by
  have hp : tsPlays ω u = tsPlays ω' u := by
    funext i
    rw [tsPlays_eq, tsPlays_eq, h]
  unfold trial
  rw [hp, h, sat_congr ν T hp, best_congr ν T hp]

lemma trial_B {ω : TSOmega N} {u : ℕ} (h : trial ν T j s a ω u) : Bv T j s ω :=
  ⟨u, h.1, h.2.1, h.2.2.1⟩

lemma fail_not_succ {ω : TSOmega N} {u : ℕ} (h : fail ν T j s a y ω u) :
    ¬ succ ν T j s a y ω u :=
  fun h' => absurd h.2 (not_le.2 h'.2)

lemma trial_cases {ω : TSOmega N} {u : ℕ} (h : trial ν T j s a ω u) :
    fail ν T j s a y ω u ∨ succ ν T j s a y ω u := by
  rcases le_or_gt (ω.1 (0, u, s, j - s)) y with h1 | h1
  · exact Or.inl ⟨h, h1⟩
  · exact Or.inr ⟨h, h1⟩

lemma st_le (ω : TSOmega N) (u : ℕ) : st ν T j s a y ω u ≤ u := by
  induction u with
  | zero => simp [st]
  | succ u ih =>
    simp only [st]
    split_ifs <;> omega

lemma st_fail {ω : TSOmega N} {u : ℕ} (h : fail ν T j s a y ω u) :
    st ν T j s a y ω (u + 1) = st ν T j s a y ω u + 1 := by
  simp only [st]
  rw [if_pos h]

lemma st_succ {ω : TSOmega N} {u : ℕ} (h : succ ν T j s a y ω u) :
    st ν T j s a y ω (u + 1) = 0 := by
  have h' : ¬ fail ν T j s a y ω u := fun hf => fail_not_succ ν T j s a y hf h
  simp only [st]
  rw [if_neg h', if_pos h]

lemma st_none {ω : TSOmega N} {u : ℕ} (h1 : ¬ fail ν T j s a y ω u)
    (h2 : ¬ succ ν T j s a y ω u) :
    st ν T j s a y ω (u + 1) = st ν T j s a y ω u := by
  simp only [st]
  rw [if_neg h1, if_neg h2]

open Classical in
lemma Fc_succ (ω : TSOmega N) (t : ℕ) :
    (Fc ν T j s a y ω (t + 1) : ENNReal) =
      Fc ν T j s a y ω t + if fail ν T j s a y ω t then 1 else 0 := by
  unfold Fc
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
    simp
  · simp

open Classical in
lemma Sc_succ (ω : TSOmega N) (t : ℕ) :
    (Sc ν T j s a y ω (t + 1) : ENNReal) =
      Sc ν T j s a y ω t + if succ ν T j s a y ω t then 1 else 0 := by
  unfold Sc
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
    simp
  · simp

lemma theta_eq {ω : TSOmega N} {u : ℕ} (h : trial ν T j s a ω u) :
    tsTheta ω u 0 = ω.1 (0, u, s, j - s) := by
  obtain ⟨_, hp, hs, _, _⟩ := h
  have := tsPlays_eq ω u 0
  have hf : (tsCounts ω u).2 0 = j - s := by omega
  unfold tsTheta tsSuccesses tsFailures
  rw [hs, hf]

lemma eventM_of_succ (hy : y = banditArmMean ν a + gapTo0 ν a / 2) {ω : TSOmega N} {u : ℕ}
    (h : succ ν T j s a y ω u) : eventM ν T ω u := by
  intro i hi
  have hb := best_prop ν T h.1.2.2.2.1 h.1.2.2.2.2 i hi
  rw [theta_eq ν T j s a h.1]
  have h2 := h.2
  unfold gapTo0 at hy ⊢
  linarith

lemma fail_of_notM (hy : y = banditArmMean ν a + gapTo0 ν a / 2) {ω : TSOmega N} {t : ℕ}
    (ht : t ∈ interval T ω j) (hM : ¬ eventM ν T ω t) (ha : a ∈ saturated ν T ω t)
    (hb : bestSaturated ν T ω t = a) (hs : (tsCounts ω t).1 0 = s) :
    fail ν T j s a y ω t := by
  simp only [interval, Finset.mem_filter, Finset.mem_range] at ht
  have htr : trial ν T j s a ω t := ⟨ht.1, ht.2.1, hs, ha, hb⟩
  refine ⟨htr, ?_⟩
  unfold eventM at hM
  push_neg at hM
  obtain ⟨i, hi, hle⟩ := hM
  have hbi := best_prop ν T ha hb i hi
  rw [theta_eq ν T j s a htr] at hle
  unfold gapTo0 at hy hle
  linarith

/-! measurability -/

lemma trial_meas (u : ℕ) : MeasurableSet {ω : TSOmega N | trial ν T j s a ω u} :=
  mset_factor (tsCounts_measurable u) (fun ω => trial ν T j s a ω u)
    fun _ _ h ht => (trial_congr ν T j s a h).1 ht

lemma coord_meas (k : Fin N × ℕ × ℕ × ℕ) : Measurable (fun ω : TSOmega N => ω.1 k) :=
  (measurable_pi_apply k).comp measurable_fst

lemma fail_meas (u : ℕ) : MeasurableSet {ω : TSOmega N | fail ν T j s a y ω u} :=
  (trial_meas ν T j s a u).inter (measurableSet_le (coord_meas _) measurable_const)

lemma succ_meas (u : ℕ) : MeasurableSet {ω : TSOmega N | succ ν T j s a y ω u} :=
  (trial_meas ν T j s a u).inter (measurableSet_lt measurable_const (coord_meas _))

open Classical in
lemma st_meas (u : ℕ) : Measurable (fun ω : TSOmega N => st ν T j s a y ω u) := by
  induction u with
  | zero =>
    simp only [st]
    exact measurable_const
  | succ u ih =>
    have e : (fun ω : TSOmega N => st ν T j s a y ω (u + 1)) = fun ω =>
        if fail ν T j s a y ω u then st ν T j s a y ω u + 1
        else if succ ν T j s a y ω u then 0 else st ν T j s a y ω u := by
      funext ω
      simp only [st]
    rw [e]
    exact Measurable.ite (fail_meas ν T j s a y u)
      ((measurable_of_countable (fun n : ℕ => n + 1)).comp ih)
      (Measurable.ite (succ_meas ν T j s a y u) measurable_const ih)

lemma Bv_meas : MeasurableSet {ω : TSOmega N | Bv T j s ω} := by
  have e : {ω : TSOmega N | Bv T j s ω} =
      ⋃ u : ℕ, {ω | u < T ∧ tsPlays ω u 0 = j ∧ (tsCounts ω u).1 0 = s} := by
    ext ω
    simp only [Bv, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [e]
  refine MeasurableSet.iUnion fun u => mset_factor (tsCounts_measurable u)
    (fun ω => u < T ∧ tsPlays ω u 0 = j ∧ (tsCounts ω u).1 0 = s) ?_
  intro ω ω' h hω
  refine ⟨hω.1, ?_, ?_⟩
  · rw [tsPlays_eq, ← h, ← tsPlays_eq]
    exact hω.2.1
  · rw [← h]
    exact hω.2.2

open Classical in
lemma Fc_meas (t : ℕ) : Measurable (fun ω : TSOmega N => (Fc ν T j s a y ω t : ENNReal)) := by
  have e : (fun ω : TSOmega N => (Fc ν T j s a y ω t : ENNReal)) =
      fun ω => ∑ u ∈ Finset.range t, if fail ν T j s a y ω u then (1 : ENNReal) else 0 := by
    funext ω
    unfold Fc
    rw [Finset.card_filter]
    push_cast
    try rfl
  rw [e]
  exact Finset.measurable_sum _ fun u _ =>
    Measurable.ite (fail_meas ν T j s a y u) measurable_const measurable_const

/-! locality of `st` -/

lemma st_updW (t : ℕ) (c : ℝ) (ω : TSOmega N) : ∀ u ≤ t,
    st ν T j s a y (updW (0, t, s, j - s) c ω) u = st ν T j s a y ω u := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
    intro hu
    have hc : tsCounts (updW (0, t, s, j - s) c ω) u = tsCounts ω u :=
      tsCounts_updW _ c ω u (by show u ≤ t; omega)
    have hk : (updW (0, t, s, j - s) c ω).1 (0, u, s, j - s) = ω.1 (0, u, s, j - s) := by
      simp only [updW]
      rw [Function.update_of_ne]
      intro h
      have := congrArg (fun x => x.2.1) h
      simp at this
      omega
    have hf : fail ν T j s a y (updW (0, t, s, j - s) c ω) u ↔ fail ν T j s a y ω u := by
      unfold fail
      rw [trial_congr ν T j s a hc, hk]
    have hs : succ ν T j s a y (updW (0, t, s, j - s) c ω) u ↔ succ ν T j s a y ω u := by
      unfold succ
      rw [trial_congr ν T j s a hc, hk]
    simp only [st, ih (by omega)]
    by_cases h1 : fail ν T j s a y ω u
    · rw [if_pos (hf.2 h1), if_pos h1]
    · rw [if_neg (fun h => h1 (hf.1 h)), if_neg h1]
      by_cases h2 : succ ν T j s a y ω u
      · rw [if_pos (hs.2 h2), if_pos h2]
      · rw [if_neg (fun h => h2 (hs.1 h)), if_neg h2]

/-! the invariant -/

lemma invariant (t : ℕ) :
    ∫⁻ ω, LHSf ν T j s a y t ω ∂(tsLaw ν) = ∫⁻ ω, RHSf ν T j s a y t ω ∂(tsLaw ν) := by
  classical
  induction t with
  | zero =>
    refine lintegral_congr fun ω => ?_
    simp [LHSf, RHSf, Fc, Sc, st]
  | succ t ih =>
    have hst := st_meas ν T j s a y t
    have hIfail : Measurable (Ff ν T j s a y t) :=
      Measurable.ite (fail_meas ν T j s a y t)
        ((measurable_of_countable (fun n => 1 + gg T (qq s j y) (n + 1))).comp hst) measurable_const
    have hIsucc : Measurable (Sf ν T j s a y t) :=
      Measurable.ite (succ_meas ν T j s a y t) measurable_const measurable_const
    have hH : Measurable (Hf ν T j s a y t) :=
      Measurable.ite (trial_meas ν T j s a t)
        ((measurable_of_countable (fun n => 1 + gg T (qq s j y) (n + 1))).comp hst) measurable_const
    have hTG : Measurable (Gf ν T j s a y t) :=
      Measurable.ite (trial_meas ν T j s a t)
        ((measurable_of_countable (fun n => gg T (qq s j y) n)).comp hst) measurable_const
    have hinv : ∀ (c : ℝ) (ω : TSOmega N),
        Hf ν T j s a y t (Function.update ω.1 (0, t, s, j - s) c, ω.2) = Hf ν T j s a y t ω := by
      intro c ω
      have h1 : trial ν T j s a (Function.update ω.1 (0, t, s, j - s) c, ω.2) t ↔
          trial ν T j s a ω t :=
        trial_congr ν T j s a (tsCounts_updW (0, t, s, j - s) c ω t le_rfl)
      have h2 : st ν T j s a y (Function.update ω.1 (0, t, s, j - s) c, ω.2) t =
          st ν T j s a y ω t := st_updW ν T j s a y t c ω t le_rfl
      unfold Hf
      rw [h2]
      simp only [h1]
    have hfr := fresh ν (0, t, s, j - s) y (Hf ν T j s a y t) hH hinv
    have e1 : ∀ ω : TSOmega N, Ff ν T j s a y t ω =
        (Set.Iic y).indicator 1 (ω.1 (0, t, s, j - s)) * Hf ν T j s a y t ω := by
      intro ω
      unfold Ff Hf
      by_cases htr : trial ν T j s a ω t
      · by_cases hle : ω.1 (0, t, s, j - s) ≤ y
        · have hf : fail ν T j s a y ω t := ⟨htr, hle⟩
          simp [hf, htr, Set.indicator_apply, hle]
        · have hf : ¬ fail ν T j s a y ω t := fun h => hle h.2
          simp [hf, htr, Set.indicator_apply, hle]
      · have hf : ¬ fail ν T j s a y ω t := fun h => htr h.1
        simp [hf, htr]
    have e2 : ∀ ω : TSOmega N, qq s j y * Hf ν T j s a y t ω = Gf ν T j s a y t ω := by
      intro ω
      unfold Hf Gf
      by_cases htr : trial ν T j s a ω t
      · rw [if_pos htr, if_pos htr]
        exact gg_step T _ (lt_of_le_of_lt (st_le ν T j s a y ω t) htr.1)
      · simp [htr]
    have hfail_int : ∫⁻ ω, Ff ν T j s a y t ω ∂(tsLaw ν) = ∫⁻ ω, Gf ν T j s a y t ω ∂(tsLaw ν) := by
      rw [lintegral_congr e1, hfr, ← lintegral_const_mul _ hH]
      exact lintegral_congr e2
    have hpt : ∀ ω : TSOmega N, LHSf ν T j s a y (t + 1) ω =
        Xf ν T j s a y t ω + (Ff ν T j s a y t ω + gg T (qq s j y) 0 * Sf ν T j s a y t ω) := by
      intro ω
      unfold LHSf Xf Ff Sf
      rw [Fc_succ]
      by_cases hf : fail ν T j s a y ω t
      · have hB := trial_B ν T j s a hf.1
        have hs := fail_not_succ ν T j s a y hf
        rw [st_fail ν T j s a y hf]
        simp [hf, hs, hB, hf.1] <;> ring
      · by_cases hs : succ ν T j s a y ω t
        · have hB := trial_B ν T j s a hs.1
          rw [st_succ ν T j s a y hs]
          simp [hf, hs, hB, hs.1]
        · have htr : ¬ trial ν T j s a ω t := fun h => (trial_cases ν T j s a y h).elim hf hs
          rw [st_none ν T j s a y hf hs]
          simp [hf, hs, htr]
    have hpt2 : ∀ ω : TSOmega N, RHSf ν T j s a y (t + 1) ω =
        RHSf ν T j s a y t ω + gg T (qq s j y) 0 * Sf ν T j s a y t ω := by
      intro ω
      unfold RHSf Sf
      rw [Sc_succ]
      by_cases hs : succ ν T j s a y ω t
      · have hB := trial_B ν T j s a hs.1
        simp [hs, hB] <;> ring
      · simp [hs]
    have hpt3 : ∀ ω : TSOmega N,
        Xf ν T j s a y t ω + Gf ν T j s a y t ω = LHSf ν T j s a y t ω := by
      intro ω
      unfold Xf Gf LHSf
      by_cases htr : trial ν T j s a ω t
      · have hB := trial_B ν T j s a htr
        simp [htr, hB]
      · simp [htr]
    have hSm : Measurable (fun ω => gg T (qq s j y) 0 * Sf ν T j s a y t ω) :=
      hIsucc.const_mul _
    have hR : Measurable (fun ω => Ff ν T j s a y t ω + gg T (qq s j y) 0 * Sf ν T j s a y t ω) :=
      hIfail.add hSm
    calc ∫⁻ ω, LHSf ν T j s a y (t + 1) ω ∂(tsLaw ν)
        = ∫⁻ ω, Xf ν T j s a y t ω + (Ff ν T j s a y t ω + gg T (qq s j y) 0 * Sf ν T j s a y t ω)
            ∂(tsLaw ν) := lintegral_congr hpt
      _ = ∫⁻ ω, Xf ν T j s a y t ω ∂(tsLaw ν) + (∫⁻ ω, Ff ν T j s a y t ω ∂(tsLaw ν) +
            gg T (qq s j y) 0 * ∫⁻ ω, Sf ν T j s a y t ω ∂(tsLaw ν)) := by
        rw [lintegral_add_right _ hR, lintegral_add_left hIfail,
          lintegral_const_mul _ hIsucc]
      _ = (∫⁻ ω, Xf ν T j s a y t ω ∂(tsLaw ν) + ∫⁻ ω, Gf ν T j s a y t ω ∂(tsLaw ν)) +
            gg T (qq s j y) 0 * ∫⁻ ω, Sf ν T j s a y t ω ∂(tsLaw ν) := by
        rw [hfail_int, add_assoc]
      _ = ∫⁻ ω, LHSf ν T j s a y t ω ∂(tsLaw ν) +
            gg T (qq s j y) 0 * ∫⁻ ω, Sf ν T j s a y t ω ∂(tsLaw ν) := by
        rw [← lintegral_add_right _ hTG, lintegral_congr hpt3]
      _ = ∫⁻ ω, RHSf ν T j s a y t ω ∂(tsLaw ν) +
            gg T (qq s j y) 0 * ∫⁻ ω, Sf ν T j s a y t ω ∂(tsLaw ν) := by
        rw [ih]
      _ = ∫⁻ ω, RHSf ν T j s a y t ω + gg T (qq s j y) 0 * Sf ν T j s a y t ω ∂(tsLaw ν) := by
        rw [lintegral_add_right _ hSm, lintegral_const_mul _ hIsucc]
      _ = ∫⁻ ω, RHSf ν T j s a y (t + 1) ω ∂(tsLaw ν) := (lintegral_congr hpt2).symm

/-! endgame for fixed `a`, `s` -/

lemma sc_bound (hy : y = banditArmMean ν a + gapTo0 ν a / 2) (ω : TSOmega N) :
    Sc ν T j s a y ω T ≤ gammaCount ν T ω j + 1 ∧
      (Sc ν T j s a y ω T ≤ gammaCount ν T ω j ∨ st ν T j s a y ω T = 0) := by
  classical
  set S := (Finset.range T).filter (fun u => succ ν T j s a y ω u) with hS
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun u => tsArm ω u = 0)
  have hSc : Sc ν T j s a y ω T = S.card := rfl
  have h1 : (S.filter fun u => ¬ tsArm ω u = 0).card ≤ gammaCount ν T ω j := by
    unfold gammaCount
    apply Finset.card_le_card
    intro u hu
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hu
    simp only [interval, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨hu.1.1, hu.1.2.1.2.1, hu.2⟩, eventM_of_succ ν T j s a y hy hu.1.2⟩
  have hA0 : ∀ u ∈ S.filter (fun u => tsArm ω u = 0), ∀ v, u < v → ¬ trial ν T j s a ω v := by
    intro u hu v huv htr
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hu
    have h1 := tsPlays_mono ω 0 (Nat.succ_le_of_lt huv)
    rw [tsPlays_succ, if_pos hu.2, hu.1.2.1.2.1] at h1
    have := htr.2.1
    omega
  have hmemS : ∀ v ∈ S.filter (fun u => tsArm ω u = 0), trial ν T j s a ω v := by
    intro v hv
    simp only [hS, Finset.mem_filter] at hv
    exact hv.1.2.1
  have h0 : (S.filter fun u => tsArm ω u = 0).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro u hu v hv
    rcases lt_trichotomy u v with huv | huv | huv
    · exact absurd (hmemS v hv) (hA0 u hu v huv)
    · exact huv
    · exact absurd (hmemS u hu) (hA0 v hv u huv)
  rw [hSc]
  rcases (S.filter fun u => tsArm ω u = 0).eq_empty_or_nonempty with he | ⟨u, hu⟩
  · rw [he, Finset.card_empty] at hsplit
    exact ⟨by omega, Or.inl (by omega)⟩
  · refine ⟨by omega, Or.inr ?_⟩
    have hu' := hu
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hu'
    have hsu : succ ν T j s a y ω u := hu'.1.2
    have key : ∀ v, u + 1 ≤ v → st ν T j s a y ω v = 0 := by
      intro v hv
      induction v, hv using Nat.le_induction with
      | base => exact st_succ ν T j s a y hsu
      | succ v hv ih =>
        have hnt := hA0 u hu v (by omega)
        rw [st_none ν T j s a y (fun h => hnt h.1) (fun h => hnt h.1), ih]
    exact key T (by omega)

open Classical in
noncomputable def Zf (ω : TSOmega N) : ENNReal :=
  if Bv T j s ω then gg T (qq s j y) (st ν T j s a y ω T) else 0

lemma per_as (hy : y = banditArmMean ν a + gapTo0 ν a / 2) :
    ∫⁻ ω, (Fc ν T j s a y ω T : ENNReal) ∂(tsLaw ν) ≤
      gg T (qq s j y) 0 * ∫⁻ ω in {ω | stackSuccesses ω 0 j = s},
        ((gammaCount ν T ω j : ENNReal) + 1) ∂(tsLaw ν) := by
  classical
  have hq : qq s j y ≠ ⊤ := measure_ne_top _ _
  have hm_top : gg T (qq s j y) 0 ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun i _ => ENNReal.pow_ne_top hq
  have hgle : ∀ k, gg T (qq s j y) k ≤ gg T (qq s j y) 0 := fun k =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  have hZm : Measurable (Zf ν T j s a y) :=
    Measurable.ite (Bv_meas T j s)
      ((measurable_of_countable (fun n : ℕ => gg T (qq s j y) n)).comp (st_meas ν T j s a y T))
      measurable_const
  have hZint : ∫⁻ ω, Zf ν T j s a y ω ∂(tsLaw ν) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, gg T (qq s j y) 0 ∂(tsLaw ν)) ?_
      (lintegral_mono fun ω => ?_)
    · rw [lintegral_const, measure_univ, mul_one]
      exact hm_top
    · unfold Zf
      split_ifs
      · exact hgle _
      · exact zero_le
  have hpt : ∀ ω, RHSf ν T j s a y T ω ≤
      {ω | stackSuccesses ω 0 j = s}.indicator
        (fun ω => gg T (qq s j y) 0 * ((gammaCount ν T ω j : ENNReal) + 1)) ω +
        Zf ν T j s a y ω := by
    intro ω
    unfold RHSf
    by_cases hB : Bv T j s ω
    · have hB' := hB
      obtain ⟨u, hu, hp, hs⟩ := hB'
      have hst : stackSuccesses ω 0 j = s := (stack_eq ω u j hp).trans hs
      have eZ : Zf ν T j s a y ω = gg T (qq s j y) (st ν T j s a y ω T) := by
        unfold Zf
        rw [if_pos hB]
      rw [Set.indicator_of_mem (show ω ∈ {ω | stackSuccesses ω 0 j = s} from hst), eZ, if_pos hB]
      obtain ⟨hb1, hb2⟩ := sc_bound ν T j s a y hy ω
      rcases hb2 with hb2 | hb2
      · calc gg T (qq s j y) 0 * ((Sc ν T j s a y ω T : ENNReal) + 1)
            ≤ gg T (qq s j y) 0 * ((gammaCount ν T ω j : ENNReal) + 1) := by
              gcongr
              all_goals exact_mod_cast hb2
          _ ≤ _ := le_self_add
      · rw [hb2]
        calc gg T (qq s j y) 0 * ((Sc ν T j s a y ω T : ENNReal) + 1)
            ≤ gg T (qq s j y) 0 * ((gammaCount ν T ω j : ENNReal) + 1 + 1) := by
              gcongr
              exact_mod_cast hb1
          _ = _ := by ring
    · rw [if_neg hB]
      exact zero_le
  have hmain : ∫⁻ ω, (Fc ν T j s a y ω T : ENNReal) ∂(tsLaw ν) + ∫⁻ ω, Zf ν T j s a y ω ∂(tsLaw ν) ≤
      ∫⁻ ω, {ω | stackSuccesses ω 0 j = s}.indicator
        (fun ω => gg T (qq s j y) 0 * ((gammaCount ν T ω j : ENNReal) + 1)) ω ∂(tsLaw ν) +
        ∫⁻ ω, Zf ν T j s a y ω ∂(tsLaw ν) := by
    rw [← lintegral_add_right _ hZm, ← lintegral_add_right _ hZm]
    calc ∫⁻ ω, (Fc ν T j s a y ω T : ENNReal) + Zf ν T j s a y ω ∂(tsLaw ν)
        = ∫⁻ ω, LHSf ν T j s a y T ω ∂(tsLaw ν) := rfl
      _ = ∫⁻ ω, RHSf ν T j s a y T ω ∂(tsLaw ν) := invariant ν T j s a y T
      _ ≤ _ := lintegral_mono hpt
  have h2 := ENNReal.le_of_add_le_add_right hZint hmain
  calc _ ≤ _ := h2
    _ ≤ ∫⁻ ω in {ω | stackSuccesses ω 0 j = s},
          gg T (qq s j y) 0 * ((gammaCount ν T ω j : ENNReal) + 1) ∂(tsLaw ν) :=
        lintegral_indicator_le _ _
    _ = _ := lintegral_const_mul' _ _ hm_top

end Proc

/-! ## L5 geometric lower bound -/

lemma geom_le (s j T : ℕ) (y : ℝ) :
    gg T (qq s j y) 0 ≤ ∫⁻ w, min (ENat.toENNReal (firstExceed y w)) (T : ENNReal)
      ∂(betaTrials s (j - s)) := by
  classical
  let A : ℕ → Set (ℕ → ℝ) := fun k => Set.pi (↑(Finset.range (k + 1))) (fun _ => Set.Iic y)
  have hA : ∀ k, MeasurableSet (A k) := fun k =>
    MeasurableSet.pi (Finset.range (k + 1)).countable_toSet (fun _ _ => measurableSet_Iic)
  have hpt : ∀ w, ∑ k ∈ Finset.range T, (A k).indicator (1 : (ℕ → ℝ) → ENNReal) w ≤
      min (ENat.toENNReal (firstExceed y w)) (T : ENNReal) := by
    intro w
    have e : ∑ k ∈ Finset.range T, (A k).indicator (1 : (ℕ → ℝ) → ENNReal) w =
        (((Finset.range T).filter (fun k => w ∈ A k)).card : ENNReal) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hw : w ∈ A k <;> simp [hw]
    rw [e]
    refine le_min ?_ ?_
    · have hk : ∀ k ∈ (Finset.range T).filter (fun k => w ∈ A k),
          ((k + 1 : ℕ) : ℕ∞) ≤ firstExceed y w := by
        intro k hk
        rw [Finset.mem_filter] at hk
        unfold firstExceed
        refine le_iInf₂ fun n hn => ?_
        have : k < n := by
          by_contra hcon
          push_neg at hcon
          have h3 : w n ∈ Set.Iic y := hk.2 n (by simp; omega)
          rw [Set.mem_Iic] at h3
          linarith
        exact_mod_cast this
      by_cases htop : firstExceed y w = ⊤
      · rw [htop]
        simp
      · obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1 htop
        rw [← hM, ENat.toENNReal_coe]
        have hsub : (Finset.range T).filter (fun k => w ∈ A k) ⊆ Finset.range M := by
          intro k hk'
          have := hk k hk'
          rw [← hM] at this
          rw [Finset.mem_range]
          exact_mod_cast this
        exact_mod_cast (Finset.card_le_card hsub).trans (by simp)
    · exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  calc gg T (qq s j y) 0 = ∑ k ∈ Finset.range T, betaTrials s (j - s) (A k) := by
        unfold gg
        rw [Nat.sub_zero]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [betaTrials, Measure.infinitePi_pi _ (fun _ _ => measurableSet_Iic)]
        simp only [Finset.prod_const, Finset.card_range]
        rfl
    _ = ∫⁻ w, ∑ k ∈ Finset.range T, (A k).indicator 1 w ∂(betaTrials s (j - s)) := by
        rw [lintegral_finsetSum _ (fun k _ => measurable_one.indicator (hA k))]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [lintegral_indicator_one (hA k)]
    _ ≤ _ := lintegral_mono hpt

/-! ## L8 counting -/

lemma V_bound (ν : StochasticBandit N) (T j : ℕ) (a : Fin N) (y : ℝ)
    (hy : y = banditArmMean ν a + gapTo0 ν a / 2) (ω : TSOmega N) :
    ∑ ℓ ∈ Finset.Icc 1 (gammaCount ν T ω j + 1), Vcount ν T ω j ℓ a ≤
      ∑ s ∈ Finset.range (j + 1), Fc ν T j s a y ω T := by
  classical
  set X := (interval T ω j).filter (fun t => ¬ eventM ν T ω t ∧
    (a ∈ saturated ν T ω t ∧ bestSaturated ν T ω t = a)) with hX
  set f : ℕ → ℕ := fun t =>
    ((interval T ω j).filter (fun t' => t' < t ∧ eventM ν T ω t')).card + 1 with hf
  have e1 : ∀ ℓ, Vcount ν T ω j ℓ a = (X.filter (fun t => f t = ℓ)).card := by
    intro ℓ
    unfold Vcount subinterval
    congr 1
    ext t
    simp only [hX, hf, Finset.mem_filter]
    tauto
  have h1 : ∑ ℓ ∈ Finset.Icc 1 (gammaCount ν T ω j + 1), Vcount ν T ω j ℓ a ≤ X.card := by
    simp_rw [e1]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact Finset.card_filter_le _ _
  have h2 : X.card = ∑ s ∈ Finset.range (j + 1),
      (X.filter (fun t => (tsCounts ω t).1 0 = s)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro t ht
    rw [Finset.mem_coe] at ht
    rw [Finset.mem_coe, Finset.mem_range]
    have ht' := (Finset.mem_filter.1 ht).1
    simp only [interval, Finset.mem_filter, Finset.mem_range] at ht'
    obtain ⟨-, hp, -⟩ := ht'
    have := tsPlays_eq ω t 0
    show (tsCounts ω t).1 0 < j + 1
    omega
  refine h1.trans (h2.le.trans (Finset.sum_le_sum fun s _ => ?_))
  unfold Fc
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_filter] at ht
  have hX' := ht.1
  rw [hX, Finset.mem_filter] at hX'
  have htI := hX'.1
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, fail_of_notM ν T j s a y hy htI hX'.2.1 hX'.2.2.1 hX'.2.2.2 ht.2⟩
  simp only [interval, Finset.mem_filter, Finset.mem_range] at htI
  exact htI.1

end P549

open MeasureTheory BanditAlgorithm AgrawalGoyalTS.NArmed in
theorem solution {N : ℕ} [NeZero N] (ν : StochasticBandit N)
    (hsupp : ∀ i, ν.P i (Set.Icc 0 1) = 1)
    (hopt : ∀ i, i ≠ 0 → banditArmMean ν i < banditArmMean ν 0) (T j : ℕ) :
    ∫⁻ ω, ∑ ℓ ∈ Finset.Icc 1 (gammaCount ν T ω j + 1),
        ∑ a ∈ Finset.univ.filter (fun a : Fin N => a ≠ 0),
          (Vcount ν T ω j ℓ a : ENNReal) * ENNReal.ofReal (gapTo0 ν a) ∂(AgrawalGoyalTS.TwoArmed.tsLaw ν) ≤
      ∑ s ∈ Finset.range (j + 1),
        (∫⁻ ω in {ω | stackSuccesses ω 0 j = s},
            ((gammaCount ν T ω j : ENNReal) + 1) ∂(AgrawalGoyalTS.TwoArmed.tsLaw ν)) *
          ∑ a ∈ Finset.univ.filter (fun a : Fin N => a ≠ 0),
            ENNReal.ofReal (gapTo0 ν a) *
              ∫⁻ w, min (ENat.toENNReal
                  (AgrawalGoyalTS.TwoArmed.firstExceed (banditArmMean ν a + gapTo0 ν a / 2) w)) (T : ENNReal)
                ∂(AgrawalGoyalTS.TwoArmed.betaTrials s (j - s)) := by
  classical
  have key : ∀ a : Fin N, ∀ s : ℕ,
      ∫⁻ ω, (P549.Fc ν T j s a (banditArmMean ν a + gapTo0 ν a / 2) ω T : ENNReal)
          ∂(AgrawalGoyalTS.TwoArmed.tsLaw ν) ≤
        (∫⁻ ω in {ω | stackSuccesses ω 0 j = s},
            ((gammaCount ν T ω j : ENNReal) + 1) ∂(AgrawalGoyalTS.TwoArmed.tsLaw ν)) *
          ∫⁻ w, min (ENat.toENNReal
              (AgrawalGoyalTS.TwoArmed.firstExceed (banditArmMean ν a + gapTo0 ν a / 2) w)) (T : ENNReal)
            ∂(AgrawalGoyalTS.TwoArmed.betaTrials s (j - s)) := by
    intro a s
    refine (P549.per_as ν T j s a _ rfl).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (P549.geom_le s j T _) (zero_le)
  have hmeas : ∀ (a : Fin N) (s : ℕ), Measurable (fun ω =>
      (P549.Fc ν T j s a (banditArmMean ν a + gapTo0 ν a / 2) ω T : ENNReal)) :=
    fun a s => P549.Fc_meas ν T j s a _ T
  calc ∫⁻ ω, ∑ ℓ ∈ Finset.Icc 1 (gammaCount ν T ω j + 1),
        ∑ a ∈ Finset.univ.filter (fun a : Fin N => a ≠ 0),
          (Vcount ν T ω j ℓ a : ENNReal) * ENNReal.ofReal (gapTo0 ν a) ∂(AgrawalGoyalTS.TwoArmed.tsLaw ν)
      ≤ ∫⁻ ω, ∑ a ∈ Finset.univ.filter (fun a : Fin N => a ≠ 0), ∑ s ∈ Finset.range (j + 1),
          ENNReal.ofReal (gapTo0 ν a) *
            (P549.Fc ν T j s a (banditArmMean ν a + gapTo0 ν a / 2) ω T : ENNReal)
          ∂(AgrawalGoyalTS.TwoArmed.tsLaw ν) := by
        refine lintegral_mono fun ω => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun a _ => ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum, mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ (zero_le)
        exact_mod_cast P549.V_bound ν T j a _ rfl ω
    _ = ∑ a ∈ Finset.univ.filter (fun a : Fin N => a ≠ 0), ∑ s ∈ Finset.range (j + 1),
          ENNReal.ofReal (gapTo0 ν a) *
            ∫⁻ ω, (P549.Fc ν T j s a (banditArmMean ν a + gapTo0 ν a / 2) ω T : ENNReal)
              ∂(AgrawalGoyalTS.TwoArmed.tsLaw ν) := by
        rw [lintegral_finsetSum _ (fun a _ => Finset.measurable_sum _ fun s _ =>
          (hmeas a s).const_mul _)]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [lintegral_finsetSum _ (fun s _ => (hmeas a s).const_mul _)]
        refine Finset.sum_congr rfl fun s _ => ?_
        exact lintegral_const_mul _ (hmeas a s)
    _ ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin N => a ≠ 0), ∑ s ∈ Finset.range (j + 1),
          ENNReal.ofReal (gapTo0 ν a) *
            ((∫⁻ ω in {ω | stackSuccesses ω 0 j = s},
              ((gammaCount ν T ω j : ENNReal) + 1) ∂(AgrawalGoyalTS.TwoArmed.tsLaw ν)) *
            ∫⁻ w, min (ENat.toENNReal
              (AgrawalGoyalTS.TwoArmed.firstExceed (banditArmMean ν a + gapTo0 ν a / 2) w)) (T : ENNReal)
              ∂(AgrawalGoyalTS.TwoArmed.betaTrials s (j - s))) := by
        gcongr with a ha s hs
        exact key a s
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
