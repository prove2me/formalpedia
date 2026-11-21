-- Prove2me | solution 1 for AndOrSched.section_2_lp1_relaxation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:28:44.333203+00:00
-- url     : https://prove2.me/submissions/bef66126-accf-4b0c-b2c6-ae5b544a4c8b

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_cost
import Definitions.Def_AndOrSched_IsNormalized
import Definitions.Def_AndOrSched_LP1Obj
import Definitions.Def_AndOrSched_LP1Optimal
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
theorem solution (I : AndOrSched.Instance) (hI : AndOrSched.Acyclic I)
    (hN : AndOrSched.IsNormalized I)
    (hp : ∀ j, I.p j ≤ 1) :
    (∃ x, AndOrSched.LP1Optimal I x) ∧
    ∀ x, AndOrSched.LP1Optimal I x → ∀ C : I.N → ℝ, AndOrSched.IsFeasible I C →
      AndOrSched.LP1Obj I x ≤ AndOrSched.cost I C := by
  -- a feasible order without any schedule: kinds first, then heights
  obtain ⟨σ0, hσ0⟩ := sigma_lin (sec I) (sec_inj I)
  have hAND0 : ∀ i j, andRel I i j → σ0 i < σ0 j := fun i j h => (hσ0 i j).mpr (and_sec I hI i j h)
  have hOR0 : ∀ b, (orPred I b).Nonempty → ∃ a ∈ orPred I b, σ0 (Sum.inl a) < σ0 (Sum.inr b) := by
    intro b hb
    obtain ⟨a, ha⟩ := hb
    exact ⟨a, ha, (hσ0 _ _).mpr (sec_lt_kind I _ _ (by simp [kind]))⟩
  obtain ⟨hfeas0, _⟩ := lp_of_order I hN hp σ0 hAND0 hOR0
  -- compactness
  set T := horizon I with hT
  let K : Set (I.N → ℕ → ℝ) :=
    {y | LP1Feasible I y} ∩ {y | ∀ j t, t ∉ Finset.Icc 1 T → y j t = 0}
  have hKclosed : IsClosed K := by
    apply IsClosed.inter (feasible_closed I)
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply t).comp (continuous_apply j)) continuous_const
  have hKsub : K ⊆ Set.pi Set.univ (fun _ : I.N => Set.pi Set.univ (fun _ : ℕ => Set.Icc (0 : ℝ) 1)) := by
    intro y hy
    obtain ⟨hyF, hy0⟩ := hy
    have hyF' := hyF
    unfold LP1Feasible at hyF'
    obtain ⟨h1, _, _, _, h5⟩ := hyF'
    rw [Set.mem_univ_pi]
    intro j
    rw [Set.mem_univ_pi]
    intro t
    by_cases ht : t ∈ Finset.Icc 1 T
    · refine ⟨h5 j t ht, ?_⟩
      have := Finset.single_le_sum (f := fun s => y j s) (fun s hs => h5 j s hs) ht
      have h1j := h1 j
      unfold cum at h1j
      linarith
    · rw [hy0 j t ht]; exact ⟨le_rfl, zero_le_one⟩
  have hcomp : IsCompact (Set.pi Set.univ (fun _ : I.N => Set.pi Set.univ (fun _ : ℕ => Set.Icc (0 : ℝ) 1))) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  have hKcomp : IsCompact K := hcomp.of_isClosed_subset hKclosed hKsub
  have hx0K : trunc I (xOf I σ0) ∈ K := by
    refine Set.mem_inter (trunc_feasible I _ hfeas0) ?_
    show ∀ j t, t ∉ Finset.Icc 1 T → trunc I (xOf I σ0) j t = 0
    intro j t ht
    show (if t ∈ Finset.Icc 1 (horizon I) then xOf I σ0 j t else 0) = 0
    rw [if_neg ht]
  obtain ⟨xs, hxsK, hmin⟩ := hKcomp.exists_isMinOn ⟨_, hx0K⟩ (obj_cont I).continuousOn
  have hopt : LP1Optimal I xs := by
    unfold LP1Optimal
    refine ⟨hxsK.1, fun y hy => ?_⟩
    have hyK : trunc I y ∈ K := by
      refine Set.mem_inter (trunc_feasible I y hy) ?_
      show ∀ j t, t ∉ Finset.Icc 1 T → trunc I y j t = 0
      intro j t ht
      show (if t ∈ Finset.Icc 1 (horizon I) then y j t else 0) = 0
      rw [if_neg ht]
    have := isMinOn_iff.mp hmin _ hyK
    rw [obj_trunc] at this
    exact this
  refine ⟨⟨xs, hopt⟩, ?_⟩
  intro x hx C hC
  obtain ⟨σ, hAND, hOR, hcnt⟩ := order_of_sched I hI hN hp C hC
  obtain ⟨hfeas, hobj⟩ := lp_of_order I hN hp σ hAND hOR
  have hx' := hx
  unfold LP1Optimal at hx'
  have h1 := hx'.2 _ hfeas
  rw [hobj] at h1
  exact le_trans h1 (cost_ge I hN C (cnt I σ) hcnt)
