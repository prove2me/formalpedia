-- Prove2me | solution 1 for AndOrSched.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:12:10.324107+00:00
-- url     : https://prove2.me/submissions/ef90b3f3-46e6-43d7-bf17-66d345dc9633

import Mathlib
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_Compat
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_IsNormalized
import Definitions.Def_AndOrSched_LP1Feasible
import Definitions.Def_AndOrSched_LP1Obj
import Definitions.Def_AndOrSched_LP1Optimal
import Definitions.Def_AndOrSched_alphaPoint
import Definitions.Def_AndOrSched_cost
import Definitions.Def_AndOrSched_delta
import Definitions.Def_AndOrSched_key
import Definitions.Def_AndOrSched_listC
import Definitions.Def_AndOrSched_nonRedPred
import Definitions.Def_AndOrSched_orPred
import Definitions.Def_AndOrSched_worstCost
open scoped Classical NNReal


namespace Aux_AOS_lp1

open AndOrSched

theorem sigma_lin {N α : Type} [Fintype N] [LinearOrder α] (f : N → α)
    (hf : Function.Injective f) :
    ∃ σ : N ≃ Fin (Fintype.card N), ∀ i j, σ i < σ j ↔ f i < f j := by
  let g : N → ℕ := fun j => (Finset.univ.filter (fun i => f i < f j)).card
  have hg_lt : ∀ j, g j < Fintype.card N := by
    intro j
    have hss : (Finset.univ.filter (fun i => f i < f j)) ⊂ Finset.univ := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun h => ?_⟩
      have : j ∈ Finset.univ.filter (fun i => f i < f j) := by rw [h]; exact Finset.mem_univ j
      simp at this
    have := Finset.card_lt_card hss
    simpa using this
  have hg_mono : ∀ i j, f i < f j → g i < g j := by
    intro i j hij
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun h => ?_⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact lt_trans hk hij
    · have : i ∈ Finset.univ.filter (fun k => f k < f j) := by simp [hij]
      rw [← h] at this
      simp at this
  have hinj : Function.Injective (fun j => (⟨g j, hg_lt j⟩ : Fin (Fintype.card N))) := by
    intro i j hij
    simp only [Fin.mk.injEq] at hij
    by_contra hne
    rcases lt_trichotomy (f i) (f j) with h | h | h
    · exact absurd hij (ne_of_lt (hg_mono i j h))
    · exact hne (hf h)
    · exact absurd hij (ne_of_gt (hg_mono j i h))
  have hbij : Function.Bijective (fun j => (⟨g j, hg_lt j⟩ : Fin (Fintype.card N))) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩
  refine ⟨Equiv.ofBijective _ hbij, fun i j => ?_⟩
  simp only [Equiv.ofBijective_apply, Fin.mk_lt_mk]
  constructor
  · intro h
    rcases lt_trichotomy (f i) (f j) with h' | h' | h'
    · exact h'
    · rw [hf h'] at h; exact absurd h (lt_irrefl _)
    · exact absurd h (not_lt.mpr (hg_mono j i h').le)
  · exact hg_mono i j

theorem lex_lt (a b x y M : ℕ) (hx : x < M) (hab : a < b) : a * M + x < b * M + y := by
  have h1 : (a + 1) * M ≤ b * M := Nat.mul_le_mul_right M hab
  have h2 : (a + 1) * M = a * M + M := by ring
  omega

def kind (I : Instance) : I.N → ℕ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

noncomputable def ht (I : Instance) : I.N → ℕ
  | Sum.inl a => (Finset.univ.filter (fun a' => Relation.TransGen I.andA a' a)).card
  | Sum.inr b => (Finset.univ.filter (fun b' => Relation.TransGen I.andB b' b)).card

theorem ht_lt (I : Instance) (j : I.N) : ht I j < Fintype.card I.N + 1 := by
  rw [Fintype.card_sum]
  cases j with
  | inl a =>
    show (Finset.univ.filter (fun a' => Relation.TransGen I.andA a' a)).card < _
    have := Finset.card_filter_le (Finset.univ : Finset I.A) (fun a' => Relation.TransGen I.andA a' a)
    rw [Finset.card_univ] at this
    omega
  | inr b =>
    show (Finset.univ.filter (fun b' => Relation.TransGen I.andB b' b)).card < _
    have := Finset.card_filter_le (Finset.univ : Finset I.B) (fun b' => Relation.TransGen I.andB b' b)
    rw [Finset.card_univ] at this
    omega

theorem ht_A (I : Instance) (hI : Acyclic I) (a a' : I.A) (h : I.andA a a') :
    ht I (Sum.inl a) < ht I (Sum.inl a') := by
  show (Finset.univ.filter (fun c => Relation.TransGen I.andA c a)).card <
    (Finset.univ.filter (fun c => Relation.TransGen I.andA c a')).card
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun he => ?_⟩
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact Relation.TransGen.tail hc h
  · have : a ∈ Finset.univ.filter (fun c => Relation.TransGen I.andA c a') := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.TransGen.single h
    rw [← he] at this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact hI.1 a this

theorem ht_B (I : Instance) (hI : Acyclic I) (b b' : I.B) (h : I.andB b b') :
    ht I (Sum.inr b) < ht I (Sum.inr b') := by
  show (Finset.univ.filter (fun c => Relation.TransGen I.andB c b)).card <
    (Finset.univ.filter (fun c => Relation.TransGen I.andB c b')).card
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun he => ?_⟩
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact Relation.TransGen.tail hc h
  · have : b ∈ Finset.univ.filter (fun c => Relation.TransGen I.andB c b') := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.TransGen.single h
    rw [← he] at this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact hI.2 b this

/-- secondary score: kind, then AND-height, then an index -/
noncomputable def sec (I : Instance) (j : I.N) : ℕ :=
  (kind I j * (Fintype.card I.N + 1) + ht I j) * Fintype.card I.N + (Fintype.equivFin I.N j).val

theorem sec_inj (I : Instance) : Function.Injective (sec I) := by
  intro i j h
  have h1 : sec I i % Fintype.card I.N = (Fintype.equivFin I.N i).val :=
    Nat.mul_add_mod_of_lt (Fintype.equivFin I.N i).isLt
  have h2 : sec I j % Fintype.card I.N = (Fintype.equivFin I.N j).val :=
    Nat.mul_add_mod_of_lt (Fintype.equivFin I.N j).isLt
  have : (Fintype.equivFin I.N i).val = (Fintype.equivFin I.N j).val := by rw [← h1, ← h2, h]
  exact (Fintype.equivFin I.N).injective (Fin.ext this)

theorem sec_lt_kind (I : Instance) (i j : I.N) (h : kind I i < kind I j) : sec I i < sec I j := by
  unfold sec
  exact lex_lt _ _ _ _ _ (Fintype.equivFin I.N i).isLt (lex_lt _ _ _ _ _ (ht_lt I i) h)

theorem sec_lt_ht (I : Instance) (i j : I.N) (h1 : kind I i = kind I j) (h2 : ht I i < ht I j) :
    sec I i < sec I j := by
  unfold sec
  apply lex_lt _ _ _ _ _ (Fintype.equivFin I.N i).isLt
  rw [h1]; omega

theorem and_sec (I : Instance) (hI : Acyclic I) (i j : I.N) (h : andRel I i j) : sec I i < sec I j := by
  cases i with
  | inl a =>
    cases j with
    | inl a' => exact sec_lt_ht I _ _ rfl (ht_A I hI a a' h)
    | inr b' => exact absurd h (by simp [andRel])
  | inr b =>
    cases j with
    | inl a' => exact absurd h (by simp [andRel])
    | inr b' => exact sec_lt_ht I _ _ rfl (ht_B I hI b b' h)

theorem pval (I : Instance) (hN : IsNormalized I) (hp : ∀ j, I.p j ≤ 1) (j : I.N) :
    ((I.p j : ℚ≥0) : ℝ) = (pN I j : ℝ) ∧ pN I j ≤ 1 := by
  have hN' := hN
  unfold IsNormalized at hN'
  obtain ⟨n, hn⟩ := hN'.2.1 j
  have hpN : pN I j = n := by unfold pN; rw [hn, Nat.floor_natCast]
  have hn1 : n ≤ 1 := by
    have := hp j
    rw [hn] at this
    exact_mod_cast this
  refine ⟨?_, by omega⟩
  rw [hpN, hn]
  simp

/-- integral completion count for an order -/
noncomputable def cnt (I : Instance) (σ : I.N ≃ Fin (Fintype.card I.N)) (j : I.N) : ℕ :=
  (Finset.univ.filter (fun i => σ i ≤ σ j ∧ pN I i = 1)).card

/-- the integral LP solution of an order -/
noncomputable def xOf (I : Instance) (σ : I.N ≃ Fin (Fintype.card I.N)) : I.N → ℕ → ℝ :=
  fun j t => if t = cnt I σ j then 1 else 0

theorem cnt_mono (I : Instance) (σ : I.N ≃ Fin (Fintype.card I.N)) (i j : I.N) (h : σ i ≤ σ j) :
    cnt I σ i ≤ cnt I σ j := by
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact ⟨le_trans hk.1 h, hk.2⟩

theorem cnt_lt (I : Instance) (hN : IsNormalized I) (hp : ∀ j, I.p j ≤ 1)
    (σ : I.N ≃ Fin (Fintype.card I.N)) (i j : I.N) (h : σ i < σ j) :
    cnt I σ i + pN I j ≤ cnt I σ j := by
  have hj1 := (pval I hN hp j).2
  by_cases hpj : pN I j = 1
  · rw [hpj]
    have : cnt I σ i < cnt I σ j := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun he => ?_⟩
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact ⟨le_trans hk.1 h.le, hk.2⟩
      · have : j ∈ Finset.univ.filter (fun k => σ k ≤ σ j ∧ pN I k = 1) := by
          simp [hpj]
        rw [← he] at this
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact absurd this.1 (not_le.mpr h)
    omega
  · have : pN I j = 0 := by omega
    rw [this]
    exact cnt_mono I σ i j h.le

theorem cnt_pos (I : Instance) (hN : IsNormalized I) (hp : ∀ j, I.p j ≤ 1)
    (σ : I.N ≃ Fin (Fintype.card I.N))
    (hAND : ∀ i j, andRel I i j → σ i < σ j)
    (hOR : ∀ b, (orPred I b).Nonempty → ∃ a ∈ orPred I b, σ (Sum.inl a) < σ (Sum.inr b)) :
    ∀ j, 1 ≤ cnt I σ j := by
  have key : ∀ m, ∀ j, (σ j).val = m → 1 ≤ cnt I σ j := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hj
      by_cases hpj : pN I j = 1
      · apply Finset.card_pos.mpr
        exact ⟨j, by simp [hpj]⟩
      · have hp0 : (I.p j : ℝ) = 0 := by
          rw [(pval I hN hp j).1]; have := (pval I hN hp j).2
          have : pN I j = 0 := by omega
          rw [this]; simp
        have hpred : HasPred I j := by
          by_contra hno
          have hN' := hN
          unfold IsNormalized at hN'
          have := hN'.2.2.1 j hno
          have h1 : (1 : ℝ) ≤ ((I.p j : ℚ≥0) : ℝ) := by exact_mod_cast this
          linarith
        rcases hpred with ⟨i, hi⟩ | ⟨b, rfl, hb⟩
        · have hlt := hAND i j hi
          have := ih (σ i).val (by rw [← hj]; exact hlt) i rfl
          exact le_trans this (cnt_mono I σ i j hlt.le)
        · obtain ⟨a, _, hlt⟩ := hOR b hb
          have := ih (σ (Sum.inl a)).val (by rw [← hj]; exact hlt) (Sum.inl a) rfl
          exact le_trans this (cnt_mono I σ _ _ hlt.le)
  exact fun j => key _ j rfl

theorem cnt_le (I : Instance) (σ : I.N ≃ Fin (Fintype.card I.N)) (j : I.N) :
    cnt I σ j ≤ horizon I := by
  unfold cnt horizon
  calc (Finset.univ.filter (fun i => σ i ≤ σ j ∧ pN I i = 1)).card
      = ∑ i ∈ Finset.univ.filter (fun i => σ i ≤ σ j ∧ pN I i = 1), pN I i := by
        rw [Finset.card_eq_sum_ones]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_filter] at hi
        rw [hi.2.2]
    _ ≤ ∑ i, pN I i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)

theorem cum_xOf (I : Instance) (σ : I.N ≃ Fin (Fintype.card I.N)) (hpos : ∀ j, 1 ≤ cnt I σ j)
    (j : I.N) (t : ℕ) : cum (xOf I σ) j t = if cnt I σ j ≤ t then 1 else 0 := by
  unfold cum xOf
  rw [Finset.sum_ite_eq']
  by_cases h : cnt I σ j ≤ t
  · rw [if_pos (Finset.mem_Icc.mpr ⟨hpos j, h⟩), if_pos h]
  · rw [if_neg (fun hm => h (Finset.mem_Icc.mp hm).2), if_neg h]

theorem lp_of_order (I : Instance) (hN : IsNormalized I) (hp : ∀ j, I.p j ≤ 1)
    (σ : I.N ≃ Fin (Fintype.card I.N))
    (hAND : ∀ i j, andRel I i j → σ i < σ j)
    (hOR : ∀ b, (orPred I b).Nonempty → ∃ a ∈ orPred I b, σ (Sum.inl a) < σ (Sum.inr b)) :
    LP1Feasible I (xOf I σ) ∧
      LP1Obj I (xOf I σ) = ∑ b, (I.w (Sum.inr b) : ℝ) * (cnt I σ (Sum.inr b) : ℝ) := by
  have hpos := cnt_pos I hN hp σ hAND hOR
  have hcum := cum_xOf I σ hpos
  have hle := cnt_le I σ
  have hcnn : ∀ j t, 0 ≤ cum (xOf I σ) j t := by
    intro j t; rw [hcum]; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · unfold LP1Feasible
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j; rw [hcum, if_pos (hle j)]
    · intro t ht
      rw [Finset.mem_Icc] at ht
      have hterm : ∀ j, ∑ s ∈ Finset.Ioc (t - pN I j) t, xOf I σ j s =
          if pN I j = 1 ∧ cnt I σ j = t then 1 else 0 := by
        intro j
        have hj1 := (pval I hN hp j).2
        by_cases hpj : pN I j = 1
        · have hI : Finset.Ioc (t - pN I j) t = {t} := by
            ext s; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
          rw [hI, Finset.sum_singleton]
          unfold xOf
          by_cases hc : cnt I σ j = t
          · rw [if_pos hc.symm, if_pos ⟨hpj, hc⟩]
          · rw [if_neg (fun e => hc e.symm), if_neg (fun e => hc e.2)]
        · have hI : Finset.Ioc (t - pN I j) t = ∅ := by
            ext s; simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]; omega
          rw [hI, Finset.sum_empty, if_neg (fun e => hpj e.1)]
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_boole]
      have : (Finset.univ.filter (fun j => pN I j = 1 ∧ cnt I σ j = t)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro i hi k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hk
        by_contra hne
        rcases lt_or_gt_of_ne (fun e => hne (σ.injective e)) with h | h
        · have := cnt_lt I hN hp σ i k h; omega
        · have := cnt_lt I hN hp σ k i h; omega
      exact_mod_cast this
    · intro b hb t ht
      rw [Finset.mem_Icc] at ht
      obtain ⟨a, ha, hlt⟩ := hOR b hb
      have h1 := cnt_lt I hN hp σ _ _ hlt
      rw [hcum]
      by_cases hc : cnt I σ (Sum.inr b) ≤ t + pN I (Sum.inr b)
      · rw [if_pos hc]
        have h2 : (1 : ℝ) ≤ ∑ a ∈ orPred I b, cum (xOf I σ) (Sum.inl a) t := by
          have h3 : cum (xOf I σ) (Sum.inl a) t = 1 := by
            rw [hcum, if_pos (show cnt I σ (Sum.inl a) ≤ t by omega)]
          calc (1 : ℝ) = cum (xOf I σ) (Sum.inl a) t := h3.symm
            _ ≤ _ := Finset.single_le_sum (f := fun a => cum (xOf I σ) (Sum.inl a) t)
              (fun a _ => hcnn _ _) ha
        linarith
      · rw [if_neg hc]
        have : 0 ≤ ∑ a ∈ orPred I b, cum (xOf I σ) (Sum.inl a) t :=
          Finset.sum_nonneg (fun a _ => hcnn _ _)
        linarith
    · intro i j hij t ht
      rw [Finset.mem_Icc] at ht
      have h1 := cnt_lt I hN hp σ _ _ (hAND i j hij)
      rw [hcum, hcum]
      by_cases hc : cnt I σ j ≤ t + pN I j
      · rw [if_pos hc, if_pos (show cnt I σ i ≤ t by omega)]; norm_num
      · rw [if_neg hc]; split_ifs <;> norm_num
    · intro j t _
      unfold xOf; split_ifs <;> norm_num
  · unfold LP1Obj
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    unfold xOf
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_Icc.mpr ⟨hpos _, hle _⟩)]

theorem order_of_sched (I : Instance) (hI : Acyclic I) (hN : IsNormalized I)
    (hp : ∀ j, I.p j ≤ 1) (C : I.N → ℝ) (hC : IsFeasible I C) :
    ∃ σ : I.N ≃ Fin (Fintype.card I.N), (∀ i j, andRel I i j → σ i < σ j) ∧
      (∀ b, (orPred I b).Nonempty → ∃ a ∈ orPred I b, σ (Sum.inl a) < σ (Sum.inr b)) ∧
      ∀ j, (cnt I σ j : ℝ) ≤ C j := by
  let f : I.N → Lex (ℝ × ℕ) := fun j => toLex (C j, sec I j)
  have hf : Function.Injective f := by
    intro i j h
    have := congrArg (fun z => (ofLex z).2) h
    exact sec_inj I this
  obtain ⟨σ, hσ⟩ := sigma_lin f hf
  have hlt : ∀ i j, f i < f j ↔ C i < C j ∨ (C i = C j ∧ sec I i < sec I j) := by
    intro i j
    exact Prod.Lex.toLex_lt_toLex
  have hC' := hC
  unfold IsFeasible at hC'
  obtain ⟨hC1, hC2, hC3, hC4⟩ := hC'
  have hpnn : ∀ j, (0 : ℝ) ≤ ((I.p j : ℚ≥0) : ℝ) := fun j => by positivity
  have hAND : ∀ i j, andRel I i j → σ i < σ j := by
    intro i j hij
    rw [hσ, hlt]
    have h1 := hC3 i j hij
    have h2 := hpnn j
    rcases lt_or_eq_of_le (show C i ≤ C j by linarith) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, and_sec I hI i j hij⟩
  have hOR : ∀ b, (orPred I b).Nonempty → ∃ a ∈ orPred I b, σ (Sum.inl a) < σ (Sum.inr b) := by
    intro b hb
    obtain ⟨a, ha, h1⟩ := hC4 b hb
    refine ⟨a, ha, ?_⟩
    rw [hσ, hlt]
    have h2 := hpnn (Sum.inr b)
    rcases lt_or_eq_of_le (show C (Sum.inl a) ≤ C (Sum.inr b) by linarith) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, sec_lt_kind I _ _ (by simp [kind])⟩
  refine ⟨σ, hAND, hOR, fun j => ?_⟩
  -- count the unit jobs before j through their floors
  have hCj0 : 0 ≤ C j := le_trans (hpnn j) (hC1 j)
  have hcard : cnt I σ j ≤ ⌊C j⌋₊ := by
    unfold cnt
    have := Finset.card_le_card_of_injOn (fun i => ⌊C i⌋₊)
      (s := Finset.univ.filter (fun i => σ i ≤ σ j ∧ pN I i = 1)) (t := Finset.Icc 1 ⌊C j⌋₊)
      (fun i hi => by
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
        have hp1 : ((I.p i : ℚ≥0) : ℝ) = 1 := by
          rw [(pval I hN hp i).1, hi.2]; simp
        have hCi : 1 ≤ C i := by have := hC1 i; linarith
        have hCij : C i ≤ C j := by
          by_contra hcon
          push_neg at hcon
          have : f j < f i := (hlt j i).mpr (Or.inl hcon)
          have := (hσ j i).mpr this
          exact absurd hi.1 (not_le.mpr this)
        simp only [Finset.coe_Icc, Set.mem_Icc]
        exact ⟨Nat.one_le_floor_iff _ |>.mpr hCi, Nat.floor_le_floor hCij⟩)
      (fun i hi k hk hik => by
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hk
        by_contra hne
        have hpi : ((I.p i : ℚ≥0) : ℝ) = 1 := by rw [(pval I hN hp i).1, hi.2]; simp
        have hpk : ((I.p k : ℚ≥0) : ℝ) = 1 := by rw [(pval I hN hp k).1, hk.2]; simp
        have hCi0 : 0 ≤ C i := le_trans (hpnn i) (hC1 i)
        have hCk0 : 0 ≤ C k := le_trans (hpnn k) (hC1 k)
        rcases hC2 i k hne with h | h
        · have : C i + 1 ≤ C k := by linarith
          have h3 : ⌊C i + 1⌋₊ ≤ ⌊C k⌋₊ := Nat.floor_le_floor this
          rw [Nat.floor_add_one hCi0] at h3
          have hik' : ⌊C i⌋₊ = ⌊C k⌋₊ := hik
          omega
        · have : C k + 1 ≤ C i := by linarith
          have h3 : ⌊C k + 1⌋₊ ≤ ⌊C i⌋₊ := Nat.floor_le_floor this
          rw [Nat.floor_add_one hCk0] at h3
          have hik' : ⌊C i⌋₊ = ⌊C k⌋₊ := hik
          omega)
    rw [Nat.card_Icc] at this
    omega
  calc (cnt I σ j : ℝ) ≤ (⌊C j⌋₊ : ℝ) := by exact_mod_cast hcard
    _ ≤ C j := Nat.floor_le hCj0

theorem cost_ge (I : Instance) (hN : IsNormalized I) (C : I.N → ℝ) (c : I.N → ℕ)
    (hc : ∀ j, (c j : ℝ) ≤ C j) :
    ∑ b, (I.w (Sum.inr b) : ℝ) * (c (Sum.inr b) : ℝ) ≤ cost I C := by
  unfold cost
  rw [Fintype.sum_sum_type]
  have hA : ∑ a, (I.w (Sum.inl a) : ℝ) * C (Sum.inl a) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    have hN' := hN
    unfold IsNormalized at hN'
    rw [hN'.1 a]; simp
  rw [hA, zero_add]
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left (hc _) (by positivity)

/-- truncation outside the horizon -/
noncomputable def trunc (I : Instance) (y : I.N → ℕ → ℝ) : I.N → ℕ → ℝ :=
  fun j t => if t ∈ Finset.Icc 1 (horizon I) then y j t else 0

theorem cum_trunc (I : Instance) (y : I.N → ℕ → ℝ) (j : I.N) (t : ℕ) (ht : t ≤ horizon I) :
    cum (trunc I y) j t = cum y j t := by
  unfold cum trunc
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_Icc] at hs
  rw [if_pos (Finset.mem_Icc.mpr ⟨hs.1, by omega⟩)]

theorem trunc_feasible (I : Instance) (y : I.N → ℕ → ℝ) (hy : LP1Feasible I y) :
    LP1Feasible I (trunc I y) := by
  unfold LP1Feasible at hy ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hy
  refine ⟨fun j => by rw [cum_trunc I y j _ le_rfl]; exact h1 j, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have := h2 t ht
    rw [Finset.mem_Icc] at ht
    have e : ∀ j, ∑ s ∈ Finset.Ioc (t - pN I j) t, trunc I y j s =
        ∑ s ∈ Finset.Ioc (t - pN I j) t, y j s := by
      intro j
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mem_Ioc] at hs
      unfold trunc
      rw [if_pos (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
    rw [Finset.sum_congr rfl (fun j _ => e j)]
    exact this
  · intro b hb t ht
    have := h3 b hb t ht
    rw [Finset.mem_Icc] at ht
    rw [cum_trunc I y (Sum.inr b) (t + pN I (Sum.inr b)) (by omega)]
    rw [Finset.sum_congr rfl (fun a _ => cum_trunc I y (Sum.inl a) t (by omega))]
    exact this
  · intro i j hij t ht
    have := h4 i j hij t ht
    rw [Finset.mem_Icc] at ht
    rw [cum_trunc I y j (t + pN I j) (by omega), cum_trunc I y i t (by omega)]
    exact this
  · intro j t ht
    unfold trunc
    rw [if_pos ht]
    exact h5 j t ht

theorem obj_trunc (I : Instance) (y : I.N → ℕ → ℝ) : LP1Obj I (trunc I y) = LP1Obj I y := by
  unfold LP1Obj
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  unfold trunc
  rw [if_pos ht]

theorem obj_cont (I : Instance) : Continuous (LP1Obj I) := by
  unfold LP1Obj
  apply continuous_finsetSum
  intro b _
  apply Continuous.mul continuous_const
  apply continuous_finsetSum
  intro t _
  exact continuous_const.mul ((continuous_apply t).comp (continuous_apply (Sum.inr b)))

theorem cum_cont (I : Instance) (j : I.N) (t : ℕ) :
    Continuous (fun y : I.N → ℕ → ℝ => cum y j t) := by
  unfold cum
  apply continuous_finsetSum
  intro s _
  exact (continuous_apply s).comp (continuous_apply j)

theorem feasible_closed (I : Instance) : IsClosed {y : I.N → ℕ → ℝ | LP1Feasible I y} := by
  unfold LP1Feasible
  simp only [Set.setOf_and, Set.setOf_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))
  · exact isClosed_iInter fun j => isClosed_eq (cum_cont I j _) continuous_const
  · refine isClosed_iInter fun t => isClosed_iInter fun _ => isClosed_le ?_ continuous_const
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro s _
    exact (continuous_apply s).comp (continuous_apply j)
  · refine isClosed_iInter fun b => isClosed_iInter fun _ => isClosed_iInter fun t =>
      isClosed_iInter fun _ => isClosed_le ?_ continuous_const
    apply Continuous.sub (cum_cont I _ _)
    apply continuous_finsetSum
    intro a _
    exact cum_cont I _ _
  · refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun t => isClosed_iInter fun _ => isClosed_le ?_ continuous_const
    exact Continuous.sub (cum_cont I _ _) (cum_cont I _ _)
  · refine isClosed_iInter fun j => isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_le continuous_const ?_
    exact (continuous_apply t).comp (continuous_apply j)

end Aux_AOS_lp1

open AndOrSched Aux_AOS_lp1 in
theorem Aux_AOS_L1.lp_le_cost (I : AndOrSched.Instance) (hI : AndOrSched.Acyclic I)
    (hN : AndOrSched.IsNormalized I) (hp : ∀ j, I.p j ≤ 1) (x : I.N → ℕ → ℝ)
    (hx : AndOrSched.LP1Optimal I x) (C : I.N → ℝ) (hC : AndOrSched.IsFeasible I C) :
    AndOrSched.LP1Obj I x ≤ AndOrSched.cost I C := by
  obtain ⟨σ, hAND, hOR, hcnt⟩ := order_of_sched I hI hN hp C hC
  obtain ⟨hfeas, hobj⟩ := lp_of_order I hN hp σ hAND hOR
  have hx' := hx
  unfold LP1Optimal at hx'
  have h1 := hx'.2 _ hfeas
  rw [hobj] at h1
  exact le_trans h1 (cost_ge I hN C (cnt I σ) hcnt)



namespace Aux_AOS_feas

open AndOrSched

theorem sigma_of_injective {N : Type} [Fintype N] (f : N → ℕ) (hf : Function.Injective f) :
    ∃ σ : N ≃ Fin (Fintype.card N), ∀ i j, σ i < σ j ↔ f i < f j := by
  let g : N → ℕ := fun j => (Finset.univ.filter (fun i => f i < f j)).card
  have hg_lt : ∀ j, g j < Fintype.card N := by
    intro j
    have hss : (Finset.univ.filter (fun i => f i < f j)) ⊂ Finset.univ := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun h => ?_⟩
      have : j ∈ Finset.univ.filter (fun i => f i < f j) := by rw [h]; exact Finset.mem_univ j
      simp at this
    have := Finset.card_lt_card hss
    simpa using this
  have hg_mono : ∀ i j, f i < f j → g i < g j := by
    intro i j hij
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun h => ?_⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact lt_trans hk hij
    · have : i ∈ Finset.univ.filter (fun k => f k < f j) := by simp [hij]
      rw [← h] at this
      simp at this
  have hinj : Function.Injective (fun j => (⟨g j, hg_lt j⟩ : Fin (Fintype.card N))) := by
    intro i j hij
    simp only [Fin.mk.injEq] at hij
    by_contra hne
    rcases lt_trichotomy (f i) (f j) with h | h | h
    · exact absurd hij (ne_of_lt (hg_mono i j h))
    · exact hne (hf h)
    · exact absurd hij (ne_of_gt (hg_mono j i h))
  have hbij : Function.Bijective (fun j => (⟨g j, hg_lt j⟩ : Fin (Fintype.card N))) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩
  refine ⟨Equiv.ofBijective _ hbij, fun i j => ?_⟩
  simp only [Equiv.ofBijective_apply, Fin.mk_lt_mk]
  constructor
  · intro h
    rcases lt_trichotomy (f i) (f j) with h' | h' | h'
    · exact h'
    · rw [hf h'] at h; exact absurd h (lt_irrefl _)
    · exact absurd h (not_lt.mpr (hg_mono j i h').le)
  · exact hg_mono i j

theorem lex_lt (a b x y M : ℕ) (hx : x < M) (hab : a < b) : a * M + x < b * M + y := by
  have h1 : (a + 1) * M ≤ b * M := Nat.mul_le_mul_right M hab
  have h2 : (a + 1) * M = a * M + M := by ring
  omega

def kind (I : Instance) : I.N → ℕ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

noncomputable def ht (I : Instance) : I.N → ℕ
  | Sum.inl a => (Finset.univ.filter (fun a' => Relation.TransGen I.andA a' a)).card
  | Sum.inr b => (Finset.univ.filter (fun b' => Relation.TransGen I.andB b' b)).card

theorem ht_lt (I : Instance) (j : I.N) : ht I j < Fintype.card I.N + 1 := by
  rw [Fintype.card_sum]
  cases j with
  | inl a =>
    show (Finset.univ.filter (fun a' => Relation.TransGen I.andA a' a)).card < _
    have := Finset.card_filter_le (Finset.univ : Finset I.A) (fun a' => Relation.TransGen I.andA a' a)
    rw [Finset.card_univ] at this
    omega
  | inr b =>
    show (Finset.univ.filter (fun b' => Relation.TransGen I.andB b' b)).card < _
    have := Finset.card_filter_le (Finset.univ : Finset I.B) (fun b' => Relation.TransGen I.andB b' b)
    rw [Finset.card_univ] at this
    omega

theorem ht_A (I : Instance) (hI : Acyclic I) (a a' : I.A) (h : I.andA a a') :
    ht I (Sum.inl a) < ht I (Sum.inl a') := by
  show (Finset.univ.filter (fun c => Relation.TransGen I.andA c a)).card <
    (Finset.univ.filter (fun c => Relation.TransGen I.andA c a')).card
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun he => ?_⟩
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact Relation.TransGen.tail hc h
  · have : a ∈ Finset.univ.filter (fun c => Relation.TransGen I.andA c a') := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.TransGen.single h
    rw [← he] at this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact hI.1 a this

theorem ht_B (I : Instance) (hI : Acyclic I) (b b' : I.B) (h : I.andB b b') :
    ht I (Sum.inr b) < ht I (Sum.inr b') := by
  show (Finset.univ.filter (fun c => Relation.TransGen I.andB c b)).card <
    (Finset.univ.filter (fun c => Relation.TransGen I.andB c b')).card
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun he => ?_⟩
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact Relation.TransGen.tail hc h
  · have : b ∈ Finset.univ.filter (fun c => Relation.TransGen I.andB c b') := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.TransGen.single h
    rw [← he] at this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact hI.2 b this

theorem andRel_irrefl (I : Instance) (hI : Acyclic I) (i : I.N) : ¬ andRel I i i := by
  cases i with
  | inl a => exact fun h => hI.1 a (Relation.TransGen.single h)
  | inr b => exact fun h => hI.2 b (Relation.TransGen.single h)

end Aux_AOS_feas

open AndOrSched Aux_AOS_feas in
theorem Aux_AOS_L1.feas_main (I : AndOrSched.Instance) (hI : AndOrSched.Acyclic I)
    (hint : ∀ j, ∃ n : ℕ, I.p j = n)
    (hp : ∀ j, I.p j ≤ 1) (hred : ∀ b, AndOrSched.nonRedPred I b = AndOrSched.orPred I b)
    (x : I.N → ℕ → ℝ) (hx : AndOrSched.LP1Feasible I x) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (∃ σ, AndOrSched.Compat I (AndOrSched.key I x β) σ) ∧
    ∀ σ, AndOrSched.Compat I (AndOrSched.key I x β) σ →
      AndOrSched.IsFeasible I (AndOrSched.listC I σ) := by
  set K := key I x β with hK
  -- the score
  set n := Fintype.card I.N with hn
  let e : I.N → ℕ := fun j => (Fintype.equivFin I.N j).val
  have he : ∀ j, e j < n := fun j => (Fintype.equivFin I.N j).isLt
  let prim : I.N → ℕ := fun j => (K j * 2 + kind I j) * (n + 1) + ht I j
  let code : I.N → ℕ := fun j => prim j * n + e j
  have hkind : ∀ j, kind I j ≤ 1 := by intro j; cases j <;> simp [kind]
  have F1 : ∀ i j, K i < K j → prim i < prim j := by
    intro i j h
    show (K i * 2 + kind I i) * (n + 1) + ht I i < (K j * 2 + kind I j) * (n + 1) + ht I j
    have := hkind i
    exact lex_lt _ _ _ _ _ (ht_lt I i) (by omega)
  have F2 : ∀ i j, K i = K j → kind I i < kind I j → prim i < prim j := by
    intro i j h1 h2
    show (K i * 2 + kind I i) * (n + 1) + ht I i < (K j * 2 + kind I j) * (n + 1) + ht I j
    exact lex_lt _ _ _ _ _ (ht_lt I i) (by omega)
  have F3 : ∀ i j, K i = K j → kind I i = kind I j → ht I i < ht I j → prim i < prim j := by
    intro i j h1 h2 h3
    show (K i * 2 + kind I i) * (n + 1) + ht I i < (K j * 2 + kind I j) * (n + 1) + ht I j
    rw [h1, h2]
    omega
  have F4 : ∀ i j, prim i < prim j → code i < code j := by
    intro i j h
    show prim i * n + e i < prim j * n + e j
    exact lex_lt _ _ _ _ _ (he i) h
  have hcode_inj : Function.Injective code := by
    intro i j h
    have h1 : code i % n = e i := by
      show (prim i * n + e i) % n = e i
      exact Nat.mul_add_mod_of_lt (he i)
    have h2 : code j % n = e j := by
      show (prim j * n + e j) % n = e j
      exact Nat.mul_add_mod_of_lt (he j)
    have : e i = e j := by rw [← h1, ← h2, h]
    exact (Fintype.equivFin I.N).injective (Fin.ext this)
  have hcode_lt : ∀ i j, code i < code j → K i ≤ K j := by
    intro i j h
    by_contra hc
    push_neg at hc
    exact absurd (F4 _ _ (F1 _ _ hc)) (not_lt.mpr h.le)
  -- compatibility facts shared by both parts
  have hcompat_lt : ∀ σ : I.N ≃ Fin (Fintype.card I.N), Compat I K σ → ∀ i j, i ≠ j →
      K i ≤ K j → (K i = K j → σ i < σ j) → σ i < σ j := by
    intro σ hσ i j hij hle htie
    have hσ' := hσ
    unfold Compat at hσ'
    rcases lt_trichotomy (σ i) (σ j) with h | h | h
    · exact h
    · exact absurd (σ.injective h) hij
    · have := hσ'.1 j i h
      exact htie (le_antisymm hle this)
  refine ⟨?_, ?_⟩
  · -- existence of a compatible order
    obtain ⟨σ, hσ⟩ := sigma_of_injective code hcode_inj
    refine ⟨σ, ?_⟩
    unfold Compat
    refine ⟨?_, ?_, ?_⟩
    · intro i j h
      exact hcode_lt i j ((hσ i j).mp h)
    · intro b a _ hab
      rw [hσ]
      exact F4 _ _ (F2 _ _ hab (by simp [kind]))
    · intro i j hij hk
      rw [hσ]
      apply F4
      cases i with
      | inl a =>
        cases j with
        | inl a' => exact F3 _ _ hk rfl (ht_A I hI a a' hij)
        | inr b' => exact absurd hij (by simp [andRel])
      | inr b =>
        cases j with
        | inl a' => exact absurd hij (by simp [andRel])
        | inr b' => exact F3 _ _ hk rfl (ht_B I hI b b' hij)
  · -- every compatible order gives a feasible schedule
    intro σ hσ
    have hσ' := hσ
    unfold Compat at hσ'
    set T := horizon I with hT
    have hx' := hx
    unfold LP1Feasible at hx'
    obtain ⟨hcumT, hcap, hor, hand, hnn⟩ := hx'
    have hcum0 : ∀ j, cum x j 0 = 0 := by intro j; simp [cum]
    have hmono : ∀ j t t', t ≤ t' → t' ≤ T → cum x j t ≤ cum x j t' := by
      intro j t t' h1 h2
      unfold cum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro s hs
        rw [Finset.mem_Icc] at hs ⊢
        omega
      · intro s hs _
        rw [Finset.mem_Icc] at hs
        exact hnn j s (Finset.mem_Icc.mpr ⟨hs.1, by omega⟩)
    have hpN : ∀ j, pN I j ≤ 1 := by
      intro j
      unfold pN
      calc ⌊I.p j⌋₊ ≤ ⌊(1 : ℚ≥0)⌋₊ := Nat.floor_le_floor (hp j)
        _ = 1 := Nat.floor_one
    -- alpha points
    have ap_le : ∀ (θ : ℝ) j t, θ ≤ cum x j t → alphaPoint x j θ ≤ t := by
      intro θ j t h
      exact Nat.sInf_le h
    have ap_mem : ∀ (θ : ℝ), θ ≤ 1 → ∀ j, θ ≤ cum x j (alphaPoint x j θ) := by
      intro θ hθ j
      have hne : ({t : ℕ | θ ≤ cum x j t} : Set ℕ).Nonempty := ⟨T, by
        show θ ≤ cum x j T
        rw [hcumT j]; exact hθ⟩
      exact Nat.sInf_mem hne
    have ap_T : ∀ (θ : ℝ), θ ≤ 1 → ∀ j, alphaPoint x j θ ≤ T := by
      intro θ hθ j
      apply ap_le
      rw [hcumT j]; exact hθ
    have ap_pos : ∀ (θ : ℝ), 0 < θ → θ ≤ 1 → ∀ j, 1 ≤ alphaPoint x j θ := by
      intro θ hθ0 hθ1 j
      by_contra h
      push_neg at h
      have h0 : alphaPoint x j θ = 0 := by omega
      have := ap_mem θ hθ1 j
      rw [h0, hcum0] at this
      linarith
    -- the threshold for A-jobs
    have hδ1 : (1 : ℝ) ≤ (delta I : ℝ) := by
      have : 1 ≤ delta I := le_max_left _ _
      exact_mod_cast this
    have hδpos : (0 : ℝ) < (delta I : ℝ) := by linarith
    have hθA0 : 0 < β / (delta I : ℝ) := div_pos hβ0 hδpos
    have hθA1 : β / (delta I : ℝ) ≤ 1 := by
      rw [div_le_one hδpos]; linarith
    have hKA : ∀ a, K (Sum.inl a) = alphaPoint x (Sum.inl a) (β / (delta I : ℝ)) := fun a => rfl
    have hKB : ∀ b, K (Sum.inr b) = alphaPoint x (Sum.inr b) β := fun b => rfl
    -- a reusable step: if cum of j reaches θ at k, find t ≤ k usable in constraints
    have step : ∀ (θ : ℝ) (j : I.N), 0 < θ → θ ≤ 1 →
        (T ≤ 1 ∨ ∃ t, 1 ≤ t ∧ t ≤ T - pN I j ∧ t ≤ alphaPoint x j θ ∧
          θ ≤ cum x j (t + pN I j)) := by
      intro θ j hθ0 hθ1
      have hk1 := ap_pos θ hθ0 hθ1 j
      have hkT := ap_T θ hθ1 j
      have hkm := ap_mem θ hθ1 j
      have hp1 := hpN j
      by_cases hc : 1 ≤ alphaPoint x j θ - pN I j
      · right
        refine ⟨alphaPoint x j θ - pN I j, hc, by omega, by omega, ?_⟩
        rw [show alphaPoint x j θ - pN I j + pN I j = alphaPoint x j θ by omega]
        exact hkm
      · by_cases hT2 : 2 ≤ T
        · right
          have hk : alphaPoint x j θ = 1 := by omega
          have hpj : pN I j = 1 := by omega
          refine ⟨1, le_rfl, by omega, by omega, ?_⟩
          rw [hpj]
          show θ ≤ cum x j 2
          have := hmono j (alphaPoint x j θ) 2 (by omega) hT2
          linarith
        · left; omega
    -- AND precedence gives key order
    have hand_key : ∀ i j, andRel I i j → K i ≤ K j := by
      intro i j hij
      cases i with
      | inl a =>
        cases j with
        | inr b' => exact absurd hij (by simp [andRel])
        | inl a' =>
          rw [hKA, hKA]
          rcases step _ (Sum.inl a') hθA0 hθA1 with hT1 | ⟨t, ht1, ht2, ht3, ht4⟩
          · have := ap_T _ hθA1 (Sum.inl a)
            have := ap_pos _ hθA0 hθA1 (Sum.inl a')
            omega
          · have h1 := hand (Sum.inl a) (Sum.inl a') hij t (Finset.mem_Icc.mpr ⟨ht1, ht2⟩)
            have h2 : β / (delta I : ℝ) ≤ cum x (Sum.inl a) t := by linarith
            exact le_trans (ap_le _ _ _ h2) ht3
      | inr b =>
        cases j with
        | inl a' => exact absurd hij (by simp [andRel])
        | inr b' =>
          rw [hKB, hKB]
          rcases step _ (Sum.inr b') hβ0 hβ1 with hT1 | ⟨t, ht1, ht2, ht3, ht4⟩
          · have := ap_T _ hβ1 (Sum.inr b)
            have := ap_pos _ hβ0 hβ1 (Sum.inr b')
            omega
          · have h1 := hand (Sum.inr b) (Sum.inr b') hij t (Finset.mem_Icc.mpr ⟨ht1, ht2⟩)
            have h2 : β ≤ cum x (Sum.inr b) t := by linarith
            exact le_trans (ap_le _ _ _ h2) ht3
    -- OR precedence gives a predecessor with smaller key
    have hor_key : ∀ b, (orPred I b).Nonempty → ∃ a ∈ orPred I b, K (Sum.inl a) ≤ K (Sum.inr b) := by
      intro b hne
      rw [hKB]
      have hcardP : ((orPred I b).card : ℝ) ≤ (delta I : ℝ) := by
        have h1 : (orPred I b).card ≤ delta I := by
          rw [← hred b]
          exact le_trans (Finset.le_sup (f := fun b => (nonRedPred I b).card) (Finset.mem_univ b))
            (le_max_right _ _)
        exact_mod_cast h1
      have hcpos : (0 : ℝ) < (orPred I b).card := by
        have := Finset.card_pos.mpr hne
        exact_mod_cast this
      rcases step _ (Sum.inr b) hβ0 hβ1 with hT1 | ⟨t, ht1, ht2, ht3, ht4⟩
      · obtain ⟨a, ha⟩ := hne
        refine ⟨a, ha, ?_⟩
        rw [hKA]
        have := ap_T _ hθA1 (Sum.inl a)
        have := ap_pos _ hβ0 hβ1 (Sum.inr b)
        omega
      · have h1 := hor b hne t (Finset.mem_Icc.mpr ⟨ht1, ht2⟩)
        have h2 : β ≤ ∑ a ∈ orPred I b, cum x (Sum.inl a) t := by linarith
        by_contra hno
        push_neg at hno
        have hlt : ∀ a ∈ orPred I b, cum x (Sum.inl a) t < β / (orPred I b).card := by
          intro a ha
          by_contra hge
          push_neg at hge
          have h3 : β / (delta I : ℝ) ≤ β / (orPred I b).card :=
            div_le_div_of_nonneg_left hβ0.le hcpos hcardP
          have := ap_le _ _ _ (le_trans h3 hge)
          have := hno a ha
          rw [hKA] at this
          omega
        have h4 : ∑ a ∈ orPred I b, cum x (Sum.inl a) t <
            ∑ a ∈ orPred I b, β / (orPred I b).card := Finset.sum_lt_sum_of_nonempty hne hlt
        have e : ((orPred I b).card : ℝ) * (β / (orPred I b).card) = β := by field_simp
        rw [Finset.sum_const, nsmul_eq_mul, e] at h4
        linarith
    -- the list schedule
    have hC : ∀ i j, σ i < σ j → listC I σ i + (I.p j : ℝ) ≤ listC I σ j := by
      intro i j hij
      unfold listC
      have hsub : insert j (Finset.univ.filter (fun k => σ k ≤ σ i)) ⊆
          Finset.univ.filter (fun k => σ k ≤ σ j) := by
        intro k hk
        rw [Finset.mem_insert] at hk
        rw [Finset.mem_filter]
        rcases hk with rfl | hk
        · exact ⟨Finset.mem_univ _, le_rfl⟩
        · rw [Finset.mem_filter] at hk
          exact ⟨Finset.mem_univ _, le_trans hk.2 hij.le⟩
      have hnot : j ∉ Finset.univ.filter (fun k => σ k ≤ σ i) := by
        rw [Finset.mem_filter]; intro h; exact absurd h.2 (not_le.mpr hij)
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => ((I.p k : ℚ≥0) : ℝ)) hsub
        (fun k _ _ => by positivity)
      rw [Finset.sum_insert hnot] at this
      linarith
    unfold IsFeasible
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      unfold listC
      exact Finset.single_le_sum (f := fun i => ((I.p i : ℚ≥0) : ℝ)) (fun i _ => by positivity)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, le_rfl⟩)
    · intro i j hij
      rcases lt_or_gt_of_ne (fun h => hij (σ.injective h)) with h | h
      · left; have := hC i j h; linarith
      · right; have := hC j i h; linarith
    · intro i j hij
      have hne : i ≠ j := by
        intro h; subst h; exact andRel_irrefl I hI i hij
      have := hcompat_lt σ hσ i j hne (hand_key i j hij) (hσ'.2.2 i j hij)
      exact hC i j this
    · intro b hne
      obtain ⟨a, ha, hle⟩ := hor_key b hne
      refine ⟨a, ha, hC _ _ ?_⟩
      exact hcompat_lt σ hσ _ _ (by simp) hle (hσ'.2.1 b a ha)



open AndOrSched in
theorem Aux_AOS_L1.eq3 (I : Instance) (hint : ∀ j, ∃ n : ℕ, I.p j = n) (hp : ∀ j, I.p j ≤ 1)
    (x : I.N → ℕ → ℝ) (hx : LP1Feasible I x) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (σ : I.N ≃ Fin (Fintype.card I.N)) (hσ : Compat I (key I x β) σ) (b : I.B) :
    β / (delta I : ℝ) * listC I σ (Sum.inr b) ≤ (alphaPoint x (Sum.inr b) β : ℝ) := by
  obtain ⟨H, hH⟩ : ∃ H, H = horizon I := ⟨_, rfl⟩
  have hcH : ∀ j, cum x j H = 1 := fun j => by rw [hH]; exact hx.1 j
  have hnn : ∀ j s, 1 ≤ s → s ≤ H → 0 ≤ x j s := fun j s h1 h2 =>
    hx.2.2.2.2 j s (by rw [Finset.mem_Icc, ← hH]; exact ⟨h1, h2⟩)
  have hmono : ∀ j (a c : ℕ), a ≤ c → c ≤ H → cum x j a ≤ cum x j c := by
    intro j a c hac hcH'
    unfold cum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      simp only [Finset.mem_Icc] at hs ⊢
      omega
    · intro s hs _
      simp only [Finset.mem_Icc] at hs
      exact hnn j s hs.1 (by omega)
  have hc0 : ∀ j, cum x j 0 = 0 := fun j => by simp [cum]
  have hcnn : ∀ j (c : ℕ), c ≤ H → 0 ≤ cum x j c := fun j c hc => by
    rw [← hc0 j]; exact hmono j 0 c (Nat.zero_le _) hc
  have halpha_le : ∀ j (γ : ℝ), γ ≤ 1 → alphaPoint x j γ ≤ H := by
    intro j γ hγ
    unfold alphaPoint
    apply Nat.sInf_le
    show γ ≤ cum x j H
    rw [hcH j]; exact hγ
  have halpha_mem : ∀ j (γ : ℝ), γ ≤ 1 → γ ≤ cum x j (alphaPoint x j γ) := by
    intro j γ hγ
    unfold alphaPoint
    have hne : ({t : ℕ | γ ≤ cum x j t} : Set ℕ).Nonempty := ⟨H, by
      show γ ≤ cum x j H
      rw [hcH j]; exact hγ⟩
    exact Nat.sInf_mem hne
  have hδ : (1 : ℝ) ≤ (delta I : ℝ) := by
    have : 1 ≤ delta I := by unfold delta; exact le_max_left _ _
    exact_mod_cast this
  have hδpos : (0 : ℝ) < (delta I : ℝ) := by linarith
  obtain ⟨α, hα⟩ : ∃ α, α = β / (delta I : ℝ) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; exact div_pos hβ0 hδpos
  have hαβ : α ≤ β := by
    rw [hα, div_le_iff₀ hδpos]
    nlinarith
  rw [← hα]
  obtain ⟨t, ht⟩ : ∃ t, t = alphaPoint x (Sum.inr b) β := ⟨_, rfl⟩
  rw [← ht]
  have htH : t ≤ H := by rw [ht]; exact halpha_le _ _ hβ1
  -- every job with key ≤ t has cum ≥ α at t
  have hclaim : ∀ i, key I x β i ≤ t → α ≤ cum x i t := by
    intro i hi
    cases i with
    | inl a =>
      have hk : key I x β (Sum.inl a) = alphaPoint x (Sum.inl a) (β / (delta I : ℝ)) := rfl
      rw [hk, ← hα] at hi
      have h1 := halpha_mem (Sum.inl a) α (by linarith)
      have h2 := hmono (Sum.inl a) _ t hi htH
      linarith
    | inr b' =>
      have hk : key I x β (Sum.inr b') = alphaPoint x (Sum.inr b') β := rfl
      rw [hk] at hi
      have h1 := halpha_mem (Sum.inr b') β hβ1
      have h2 := hmono (Sum.inr b') _ t hi htH
      linarith
  have hkey : ∀ i, σ i ≤ σ (Sum.inr b) → key I x β i ≤ t := by
    intro i hi
    rcases lt_or_eq_of_le hi with h | h
    · have := hσ.1 i (Sum.inr b) h
      have hk : key I x β (Sum.inr b) = alphaPoint x (Sum.inr b) β := rfl
      rw [hk, ← ht] at this
      exact this
    · have : i = Sum.inr b := σ.injective h
      subst this
      have hk : key I x β (Sum.inr b) = alphaPoint x (Sum.inr b) β := rfl
      rw [hk, ← ht]
  -- processing times
  have hpv : ∀ i, (I.p i : ℝ) = (pN I i : ℝ) ∧ pN I i ≤ 1 := by
    intro i
    obtain ⟨n, hn⟩ := hint i
    have hpN : pN I i = n := by
      unfold pN
      rw [hn, Nat.floor_natCast]
    refine ⟨?_, ?_⟩
    · rw [hpN, hn, NNRat.cast_natCast]
    · rw [hpN]
      have := hp i
      rw [hn] at this
      exact_mod_cast this
  -- capacity per slot
  have hcap : ∀ s ∈ Finset.Icc 1 t, ∑ i, (pN I i : ℝ) * x i s ≤ 1 := by
    intro s hs
    have hs' : s ∈ Finset.Icc 1 (horizon I) := by
      rw [← hH]; simp only [Finset.mem_Icc] at hs ⊢; omega
    have h := hx.2.1 s hs'
    have heq : ∀ i, ∑ u ∈ Finset.Ioc (s - pN I i) s, x i u = (pN I i : ℝ) * x i s := by
      intro i
      have h1 := (hpv i).2
      simp only [Finset.mem_Icc] at hs
      rcases Nat.lt_or_ge (pN I i) 1 with h0 | h0
      · have hz : pN I i = 0 := by omega
        rw [hz]
        simp
      · have hz : pN I i = 1 := by omega
        rw [hz]
        have hI : Finset.Ioc (s - 1) s = {s} := by
          ext u
          simp only [Finset.mem_Ioc, Finset.mem_singleton]
          omega
        rw [hI]
        simp
    rw [Finset.sum_congr rfl (fun i _ => heq i)] at h
    exact h
  have hsumcap : ∑ i, (pN I i : ℝ) * cum x i t ≤ (t : ℝ) := by
    unfold cum
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc ∑ s ∈ Finset.Icc 1 t, ∑ i, (pN I i : ℝ) * x i s
        ≤ ∑ s ∈ Finset.Icc 1 t, (1 : ℝ) := Finset.sum_le_sum hcap
      _ = (t : ℝ) := by simp
  unfold listC
  rw [Finset.mul_sum]
  calc ∑ i ∈ Finset.univ.filter (fun i => σ i ≤ σ (Sum.inr b)), α * (I.p i : ℝ)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => σ i ≤ σ (Sum.inr b)), (pN I i : ℝ) * cum x i t := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_filter] at hi
        have h1 := hclaim i (hkey i hi.2)
        rw [(hpv i).1]
        have h2 : (0 : ℝ) ≤ (pN I i : ℝ) := Nat.cast_nonneg _
        nlinarith
    _ ≤ ∑ i, (pN I i : ℝ) * cum x i t := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        exact mul_nonneg (Nat.cast_nonneg _) (hcnn i t htH)
    _ ≤ (t : ℝ) := hsumcap


namespace Aux_AOS_L1

open AndOrSched

theorem meas_sInf (c : ℕ → ℝ) : Measurable (fun α : ℝ => sInf {t : ℕ | α ≤ c t}) := by
  apply measurable_to_countable'
  intro n
  have hset : (fun α : ℝ => sInf {t : ℕ | α ≤ c t}) ⁻¹' {n} =
      ({α : ℝ | α ≤ c n} ∩ ⋂ m : ℕ, ⋂ (_ : m < n), {α : ℝ | c m < α}) ∪
        ({α : ℝ | n = 0} ∩ ⋂ m : ℕ, {α : ℝ | c m < α}) := by
    ext α
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hα
      by_cases hne : ({t : ℕ | α ≤ c t} : Set ℕ).Nonempty
      · left
        have hmem := Nat.sInf_mem hne
        rw [hα] at hmem
        refine ⟨hmem, fun m hm => ?_⟩
        have h2 := Nat.notMem_of_lt_sInf (s := {t : ℕ | α ≤ c t}) (by rw [hα]; exact hm)
        simp only [Set.mem_setOf_eq, not_le] at h2
        exact h2
      · right
        rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne, Nat.sInf_empty] at hα
        refine ⟨hα.symm, fun m => ?_⟩
        have h2 : m ∉ ({t : ℕ | α ≤ c t} : Set ℕ) := by rw [hne]; exact Set.notMem_empty m
        simp only [Set.mem_setOf_eq, not_le] at h2
        exact h2
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · apply le_antisymm
        · exact Nat.sInf_le h1
        · by_contra hlt
          push_neg at hlt
          have hmem := Nat.sInf_mem (⟨n, h1⟩ : ({t : ℕ | α ≤ c t} : Set ℕ).Nonempty)
          have h3 := h2 _ hlt
          simp only [Set.mem_setOf_eq] at hmem
          linarith
      · have hemp : ({t : ℕ | α ≤ c t} : Set ℕ) = ∅ := by
          ext m
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
          exact h2 m
        rw [hemp, Nat.sInf_empty, h1]
  rw [hset]
  apply MeasurableSet.union
  · apply MeasurableSet.inter (measurableSet_le measurable_id measurable_const)
    exact MeasurableSet.iInter (fun m => MeasurableSet.iInter
      (fun _ => measurableSet_lt measurable_const measurable_id))
  · apply MeasurableSet.inter (MeasurableSet.const _)
    exact MeasurableSet.iInter (fun m => measurableSet_lt measurable_const measurable_id)

theorem key_meas (I : Instance) (x : I.N → ℕ → ℝ) : Measurable (fun β : ℝ => key I x β) := by
  apply measurable_pi_lambda
  intro j
  cases j with
  | inl a =>
    show Measurable (fun β : ℝ => alphaPoint x (Sum.inl a) (β / (delta I : ℝ)))
    exact (meas_sInf (cum x (Sum.inl a))).comp (measurable_id.div_const _)
  | inr b =>
    show Measurable (fun β : ℝ => alphaPoint x (Sum.inr b) β)
    exact meas_sInf (cum x (Sum.inr b))

theorem cost_listC_bounds (I : Instance) (σ : I.N ≃ Fin (Fintype.card I.N)) :
    0 ≤ cost I (listC I σ) ∧ cost I (listC I σ) ≤ ∑ j, (I.w j : ℝ) * ∑ i, ((I.p i : ℚ≥0) : ℝ) := by
  have hl0 : ∀ j, 0 ≤ listC I σ j := fun j => Finset.sum_nonneg (fun i _ => by positivity)
  have hl1 : ∀ j, listC I σ j ≤ ∑ i, ((I.p i : ℚ≥0) : ℝ) := fun j =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => by positivity)
  unfold cost
  constructor
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (hl0 j))
  · exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hl1 j) (by positivity))

theorem wc_bounds (I : Instance) (K : I.N → ℕ) :
    0 ≤ worstCost I K ∧ worstCost I K ≤ ∑ j, (I.w j : ℝ) * ∑ i, ((I.p i : ℚ≥0) : ℝ) := by
  have hB0 : 0 ≤ ∑ j, (I.w j : ℝ) * ∑ i, ((I.p i : ℚ≥0) : ℝ) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun i _ => by positivity)))
  unfold worstCost
  exact ⟨Real.iSup_nonneg (fun σ => (cost_listC_bounds I σ.1).1),
    Real.iSup_le (fun σ => (cost_listC_bounds I σ.1).2) hB0⟩

theorem wc_pointwise (I : Instance) (hN : IsNormalized I) (hp : ∀ j, I.p j ≤ 1)
    (x : I.N → ℕ → ℝ) (hx : LP1Feasible I x) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    2 * β * worstCost I (key I x β) ≤
      2 * (delta I : ℝ) * ∑ b, (I.w (Sum.inr b) : ℝ) * (alphaPoint x (Sum.inr b) β : ℝ) := by
  have hΔ1 : 1 ≤ delta I := le_max_left _ _
  have hΔ : (1 : ℝ) ≤ delta I := by exact_mod_cast hΔ1
  obtain ⟨R, hR⟩ : ∃ R, R = ∑ b, (I.w (Sum.inr b) : ℝ) * (alphaPoint x (Sum.inr b) β : ℝ) :=
    ⟨_, rfl⟩
  rw [← hR]
  have hR0 : 0 ≤ R := by
    rw [hR]; exact Finset.sum_nonneg (fun b _ => mul_nonneg (by positivity) (Nat.cast_nonneg _))
  have hwc : worstCost I (key I x β) ≤ (delta I : ℝ) / β * R := by
    unfold worstCost
    apply Real.iSup_le _ (by positivity)
    intro σ
    unfold cost
    rw [Fintype.sum_sum_type]
    have hA : ∑ a : I.A, (I.w (Sum.inl a) : ℝ) * listC I σ.1 (Sum.inl a) = 0 :=
      Finset.sum_eq_zero (fun a _ => by rw [hN.1 a]; simp)
    rw [hA, zero_add, hR, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    have h3 := eq3 I hN.2.1 hp x hx β hβ0 hβ1 σ.1 σ.2 b
    have hl : listC I σ.1 (Sum.inr b) ≤ (delta I : ℝ) / β * (alphaPoint x (Sum.inr b) β : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hβ0]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)] at h3
      linarith
    have hw : (0 : ℝ) ≤ (I.w (Sum.inr b) : ℝ) := by positivity
    calc (I.w (Sum.inr b) : ℝ) * listC I σ.1 (Sum.inr b)
        ≤ (I.w (Sum.inr b) : ℝ) * ((delta I : ℝ) / β * (alphaPoint x (Sum.inr b) β : ℝ)) :=
          mul_le_mul_of_nonneg_left hl hw
      _ = (delta I : ℝ) / β * ((I.w (Sum.inr b) : ℝ) * (alphaPoint x (Sum.inr b) β : ℝ)) := by
          ring
  have hfin : 2 * β * ((delta I : ℝ) / β * R) = 2 * (delta I : ℝ) * R := by
    have hc : β * ((delta I : ℝ) / β) = delta I := by field_simp
    calc 2 * β * ((delta I : ℝ) / β * R) = 2 * (β * ((delta I : ℝ) / β)) * R := by ring
      _ = 2 * (delta I : ℝ) * R := by rw [hc]
  calc 2 * β * worstCost I (key I x β) ≤ 2 * β * ((delta I : ℝ) / β * R) :=
        mul_le_mul_of_nonneg_left hwc (by positivity)
    _ = 2 * (delta I : ℝ) * R := hfin

theorem sum_Icc_eq_range (g : ℕ → ℝ) (n : ℕ) :
    ∑ l ∈ Finset.Icc 1 n, g l = ∑ k ∈ Finset.range n, g (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

theorem alpha_int (I : Instance) (x : I.N → ℕ → ℝ) (hx : LP1Feasible I x) (j : I.N) :
    MeasureTheory.IntegrableOn (fun γ : ℝ => (alphaPoint x j γ : ℝ)) (Set.Ioc 0 1) ∧
    ∫ γ in Set.Ioc (0 : ℝ) 1, (alphaPoint x j γ : ℝ) =
      ∑ t ∈ Finset.Icc 1 (horizon I), (t : ℝ) * x j t := by
  obtain ⟨L, hL⟩ : ∃ L, L = horizon I := ⟨_, rfl⟩
  have hcL : cum x j L = 1 := by rw [hL]; exact hx.1 j
  have hnn : ∀ s, 1 ≤ s → s ≤ L → 0 ≤ x j s := fun s h1 h2 =>
    hx.2.2.2.2 j s (by rw [Finset.mem_Icc, ← hL]; exact ⟨h1, h2⟩)
  have hc0 : cum x j 0 = 0 := by simp [cum]
  have hmono : ∀ a b : ℕ, a ≤ b → b ≤ L → cum x j a ≤ cum x j b := by
    intro a b hab hbL
    unfold cum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      simp only [Finset.mem_Icc] at hs ⊢
      omega
    · intro s hs _
      simp only [Finset.mem_Icc] at hs
      exact hnn s hs.1 (by omega)
  have hge0 : ∀ k, k ≤ L → 0 ≤ cum x j k := fun k hk => by
    rw [← hc0]; exact hmono 0 k (Nat.zero_le _) hk
  have hle1 : ∀ k, k ≤ L → cum x j k ≤ 1 := fun k hk => by
    rw [← hcL]; exact hmono k L hk le_rfl
  have hstep : ∀ k, cum x j (k + 1) = cum x j k + x j (k + 1) := by
    intro k
    unfold cum
    rw [Finset.sum_Icc_succ_top (by omega)]
  have hα : ∀ k, k < L → ∀ γ : ℝ, cum x j k < γ → γ ≤ cum x j (k + 1) →
      alphaPoint x j γ = k + 1 := by
    intro k hk γ h1 h2
    unfold alphaPoint
    apply le_antisymm
    · exact Nat.sInf_le h2
    · by_contra hcon
      push_neg at hcon
      have hmem : γ ≤ cum x j (sInf {t : ℕ | γ ≤ cum x j t}) :=
        Nat.sInf_mem (s := {t : ℕ | γ ≤ cum x j t}) ⟨k + 1, h2⟩
      have := hmono (sInf {t : ℕ | γ ≤ cum x j t}) k (by omega) (by omega)
      linarith
  have hαmono : ∀ γ₁ γ₂ : ℝ, γ₁ ≤ γ₂ → γ₂ ≤ 1 → alphaPoint x j γ₁ ≤ alphaPoint x j γ₂ := by
    intro γ₁ γ₂ h12 h2
    unfold alphaPoint
    have hne : ({t : ℕ | γ₂ ≤ cum x j t} : Set ℕ).Nonempty := ⟨L, by
      show γ₂ ≤ cum x j L
      rw [hcL]; exact h2⟩
    have hmem := Nat.sInf_mem hne
    apply Nat.sInf_le
    show γ₁ ≤ cum x j _
    exact le_trans h12 hmem
  have hfmono : MonotoneOn (fun γ : ℝ => (alphaPoint x j γ : ℝ)) (Set.Icc 0 1) := by
    intro γ₁ _ γ₂ hγ₂ h12
    have := hαmono γ₁ γ₂ h12 hγ₂.2
    show (alphaPoint x j γ₁ : ℝ) ≤ (alphaPoint x j γ₂ : ℝ)
    exact_mod_cast this
  have hII : IntervalIntegrable (fun γ : ℝ => (alphaPoint x j γ : ℝ))
      MeasureTheory.volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hfmono
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hII, ?_⟩
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hint : ∀ k < L, IntervalIntegrable (fun γ : ℝ => (alphaPoint x j γ : ℝ))
      MeasureTheory.volume (cum x j k) (cum x j (k + 1)) := by
    intro k hk
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le (hmono k (k + 1) (by omega) (by omega))]
    exact hfmono.mono (Set.Icc_subset_Icc (hge0 k (by omega)) (hle1 (k + 1) (by omega)))
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun k => cum x j k)
    (n := L) (μ := MeasureTheory.volume) hint
  simp only [hc0, hcL] at hsum
  rw [← hsum]
  have hpiece : ∀ k ∈ Finset.range L,
      (∫ γ in cum x j k..cum x j (k + 1), (alphaPoint x j γ : ℝ)) =
        ((k : ℝ) + 1) * x j (k + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hle := hmono k (k + 1) (by omega) (by omega)
    have hcongr : (∫ γ in cum x j k..cum x j (k + 1), (alphaPoint x j γ : ℝ)) =
        ∫ γ in cum x j k..cum x j (k + 1), ((k : ℝ) + 1) := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall (fun γ hγ => ?_)
      rw [Set.uIoc_of_le hle] at hγ
      rw [hα k hk γ hγ.1 hγ.2]
      simp
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, hstep k]
    ring
  rw [Finset.sum_congr rfl hpiece, ← hL, sum_Icc_eq_range (fun t => (t : ℝ) * x j t) L]
  apply Finset.sum_congr rfl
  intro k _
  simp

end Aux_AOS_L1

set_option maxHeartbeats 1600000 in
open AndOrSched Aux_AOS_L1 in
theorem solution (I : Instance) (hI : Acyclic I) (hN : IsNormalized I) (hp : ∀ j, I.p j ≤ 1)
    (x : I.N → ℕ → ℝ) (hx : LP1Optimal I x) :
    (∀ β : ℝ, 0 < β → β ≤ 1 →
      (∃ σ, Compat I (key I x β) σ) ∧ ∀ σ, Compat I (key I x β) σ → IsFeasible I (listC I σ)) ∧
    MeasureTheory.IntegrableOn (fun β : ℝ => 2 * β * worstCost I (key I x β)) (Set.Ioc 0 1) ∧
    ∀ C : I.N → ℝ, IsFeasible I C →
      ∫ β in Set.Ioc (0 : ℝ) 1, 2 * β * worstCost I (key I x β) ≤
        2 * (delta I : ℝ) * cost I C := by
  have hxF : LP1Feasible I x := hx.1
  have hpart1 : ∀ β : ℝ, 0 < β → β ≤ 1 →
      (∃ σ, Compat I (key I x β) σ) ∧ ∀ σ, Compat I (key I x β) σ → IsFeasible I (listC I σ) :=
    fun β h0 h1 => feas_main I hI hN.2.1 hp hN.2.2.2 x hxF β h0 h1
  have hmeas : Measurable (fun β : ℝ => 2 * β * worstCost I (key I x β)) :=
    (measurable_const.mul measurable_id).mul
      ((measurable_of_countable (fun K : I.N → ℕ => worstCost I K)).comp (key_meas I x))
  have hB0 : 0 ≤ ∑ j, (I.w j : ℝ) * ∑ i, ((I.p i : ℚ≥0) : ℝ) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun i _ => by positivity)))
  have hint : MeasureTheory.IntegrableOn (fun β : ℝ => 2 * β * worstCost I (key I x β))
      (Set.Ioc 0 1) := by
    refine MeasureTheory.Measure.integrableOn_of_bounded
      (M := 2 * ∑ j, (I.w j : ℝ) * ∑ i, ((I.p i : ℚ≥0) : ℝ)) (by simp)
      hmeas.aestronglyMeasurable ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun β hβ => ?_)
    obtain ⟨h0, h1⟩ := wc_bounds I (key I x β)
    have hβ0 : 0 ≤ 2 * β := by linarith [hβ.1]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hβ0 h0)]
    have h2 := mul_le_mul_of_nonneg_left h1 hβ0
    have h3 : 2 * β * ∑ j, (I.w j : ℝ) * ∑ i, ((I.p i : ℚ≥0) : ℝ) ≤
        2 * ∑ j, (I.w j : ℝ) * ∑ i, ((I.p i : ℚ≥0) : ℝ) := by
      have := mul_le_mul_of_nonneg_right hβ.2 hB0
      linarith
    linarith
  refine ⟨hpart1, hint, ?_⟩
  intro C hC
  have hal := fun b : I.B => alpha_int I x hxF (Sum.inr b)
  have hterm : ∀ b ∈ (Finset.univ : Finset I.B), MeasureTheory.Integrable
      (fun β : ℝ => (I.w (Sum.inr b) : ℝ) * (alphaPoint x (Sum.inr b) β : ℝ))
      (MeasureTheory.volume.restrict (Set.Ioc 0 1)) :=
    fun b _ => MeasureTheory.Integrable.const_mul (hal b).1 _
  have hsumI : MeasureTheory.Integrable
      (fun β : ℝ => ∑ b, (I.w (Sum.inr b) : ℝ) * (alphaPoint x (Sum.inr b) β : ℝ))
      (MeasureTheory.volume.restrict (Set.Ioc 0 1)) :=
    MeasureTheory.integrable_finset_sum _ hterm
  have hRint : MeasureTheory.IntegrableOn (fun β : ℝ => 2 * (delta I : ℝ) *
      ∑ b, (I.w (Sum.inr b) : ℝ) * (alphaPoint x (Sum.inr b) β : ℝ)) (Set.Ioc 0 1) :=
    MeasureTheory.Integrable.const_mul hsumI _
  have hmono := MeasureTheory.setIntegral_mono_on hint hRint measurableSet_Ioc
    (fun β hβ => wc_pointwise I hN hp x hxF β hβ.1 hβ.2)
  have hRval : ∫ β in Set.Ioc (0 : ℝ) 1, 2 * (delta I : ℝ) *
      ∑ b, (I.w (Sum.inr b) : ℝ) * (alphaPoint x (Sum.inr b) β : ℝ) =
      2 * (delta I : ℝ) * LP1Obj I x := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finset_sum _ hterm]
    congr 1
    unfold LP1Obj
    apply Finset.sum_congr rfl
    intro b _
    rw [MeasureTheory.integral_const_mul, (hal b).2]
  have hlp := lp_le_cost I hI hN hp x hx C hC
  have hΔ0 : (0 : ℝ) ≤ 2 * (delta I : ℝ) := by positivity
  calc ∫ β in Set.Ioc (0 : ℝ) 1, 2 * β * worstCost I (key I x β)
      ≤ ∫ β in Set.Ioc (0 : ℝ) 1, 2 * (delta I : ℝ) *
          ∑ b, (I.w (Sum.inr b) : ℝ) * (alphaPoint x (Sum.inr b) β : ℝ) := hmono
    _ = 2 * (delta I : ℝ) * LP1Obj I x := hRval
    _ ≤ 2 * (delta I : ℝ) * cost I C := mul_le_mul_of_nonneg_left hlp hΔ0
