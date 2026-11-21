-- Prove2me | solution 1 for AndOrSched.section_2_lp5_relaxation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:36:48.83003+00:00
-- url     : https://prove2.me/submissions/2fccfbe3-83f2-423d-b9c1-a36671a284f2

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_cost
import Definitions.Def_AndOrSched_IsNormalized
import Definitions.Def_AndOrSched_LP5Obj
import Definitions.Def_AndOrSched_LP5Optimal
open scoped Classical NNReal

namespace Aux_AOS_lp5

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


theorem pval5 (I : Instance) (hN : IsNormalized I) (j : I.N) :
    ((I.p j : ℚ≥0) : ℝ) = (pN I j : ℝ) := by
  have hN' := hN
  unfold IsNormalized at hN'
  obtain ⟨n, hn⟩ := hN'.2.1 j
  have hpN : pN I j = n := by unfold pN; rw [hn, Nat.floor_natCast]
  rw [hpN, hn]
  simp

theorem tau_one_le (ε' : ℝ) (hε : 0 < ε') (l : ℕ) : 1 ≤ tau ε' l := by
  unfold tau
  split_ifs
  · exact le_rfl
  · exact one_le_pow₀ (by linarith)

theorem tau_mono (ε' : ℝ) (hε : 0 < ε') (l l' : ℕ) (h : l ≤ l') : tau ε' l ≤ tau ε' l' := by
  by_cases h0 : l = 0
  · rw [h0]
    have e : tau ε' 0 = 1 := by simp [tau]
    rw [e]
    exact tau_one_le ε' hε l'
  · have h0' : l' ≠ 0 := by omega
    unfold tau
    rw [if_neg h0, if_neg h0']
    exact pow_le_pow_right₀ (by linarith) (by omega)

theorem numInt_spec (I : Instance) (ε' : ℝ) (hε : 0 < ε') :
    1 ≤ numIntervals I ε' ∧ (horizon I : ℝ) ≤ tau ε' (numIntervals I ε') := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (horizon I : ℝ) (show (1 : ℝ) < 1 + ε' by linarith)
  have hne : ({L : ℕ | 1 ≤ L ∧ (horizon I : ℝ) ≤ (1 + ε') ^ (L - 1)} : Set ℕ).Nonempty :=
    ⟨k + 1, by
      show 1 ≤ k + 1 ∧ (horizon I : ℝ) ≤ (1 + ε') ^ (k + 1 - 1)
      rw [Nat.add_sub_cancel]; exact ⟨by omega, hk.le⟩⟩
  have hmem := Nat.sInf_mem hne
  have h1 : 1 ≤ numIntervals I ε' := hmem.1
  refine ⟨h1, ?_⟩
  have h2 : (horizon I : ℝ) ≤ (1 + ε') ^ (numIntervals I ε' - 1) := hmem.2
  unfold tau
  rw [if_neg (by omega)]
  exact h2

/-- interval index of an integral completion time -/
noncomputable def iota (ε' : ℝ) (c : ℕ) : ℕ := sInf {l : ℕ | 1 ≤ l ∧ (c : ℝ) ≤ tau ε' l}

theorem iota_le_of (ε' : ℝ) (c l : ℕ) (hl : 1 ≤ l) (h : (c : ℝ) ≤ tau ε' l) : iota ε' c ≤ l :=
  Nat.sInf_le ⟨hl, h⟩

theorem iota_mem (ε' : ℝ) (c l : ℕ) (hl : 1 ≤ l) (h : (c : ℝ) ≤ tau ε' l) :
    1 ≤ iota ε' c ∧ (c : ℝ) ≤ tau ε' (iota ε' c) :=
  Nat.sInf_mem (s := {l : ℕ | 1 ≤ l ∧ (c : ℝ) ≤ tau ε' l}) ⟨l, hl, h⟩

theorem tau_pred_le (ε' : ℝ) (hε : 0 < ε') (c l : ℕ) (hl : 1 ≤ l) (h : (c : ℝ) ≤ tau ε' l)
    (hc : 1 ≤ c) : tau ε' (iota ε' c - 1) ≤ c := by
  have hm := iota_mem ε' c l hl h
  by_cases h1 : iota ε' c = 1
  · rw [h1]
    have e : tau ε' (1 - 1) = 1 := by simp [tau]
    rw [e]
    exact_mod_cast hc
  · by_contra hcon
    push_neg at hcon
    have := iota_le_of ε' c (iota ε' c - 1) (by omega) hcon.le
    omega

/-- integral completion time of a list schedule -/
noncomputable def tot (I : Instance) (σ : I.N ≃ Fin (Fintype.card I.N)) (j : I.N) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => σ i ≤ σ j), pN I i

theorem tot_mono (I : Instance) (σ : I.N ≃ Fin (Fintype.card I.N)) (i j : I.N) (h : σ i ≤ σ j) :
    tot I σ i ≤ tot I σ j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.zero_le _)
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact le_trans hk h

theorem tot_lt (I : Instance) (σ : I.N ≃ Fin (Fintype.card I.N)) (i j : I.N) (h : σ i < σ j) :
    tot I σ i + pN I j ≤ tot I σ j := by
  unfold tot
  have hsub : insert j (Finset.univ.filter (fun k => σ k ≤ σ i)) ⊆
      Finset.univ.filter (fun k => σ k ≤ σ j) := by
    intro k hk
    rw [Finset.mem_insert] at hk
    rw [Finset.mem_filter]
    rcases hk with rfl | hk
    · exact ⟨Finset.mem_univ _, le_rfl⟩
    · rw [Finset.mem_filter] at hk
      exact ⟨Finset.mem_univ _, le_trans hk.2 h.le⟩
  have hnot : j ∉ Finset.univ.filter (fun k => σ k ≤ σ i) := by
    rw [Finset.mem_filter]; intro h'; exact absurd h'.2 (not_le.mpr h)
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => pN I k) hsub
    (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_insert hnot] at this
  omega

theorem tot_self (I : Instance) (σ : I.N ≃ Fin (Fintype.card I.N)) (j : I.N) :
    pN I j ≤ tot I σ j :=
  Finset.single_le_sum (f := fun k => pN I k) (fun _ _ => Nat.zero_le _)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ j, le_rfl⟩)

theorem tot_le (I : Instance) (σ : I.N ≃ Fin (Fintype.card I.N)) (j : I.N) :
    tot I σ j ≤ horizon I := by
  unfold tot horizon
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => Nat.zero_le _)

theorem tot_pos (I : Instance) (hN : IsNormalized I)
    (σ : I.N ≃ Fin (Fintype.card I.N))
    (hAND : ∀ i j, andRel I i j → σ i < σ j)
    (hOR : ∀ b, (orPred I b).Nonempty → ∃ a ∈ orPred I b, σ (Sum.inl a) < σ (Sum.inr b)) :
    ∀ j, 1 ≤ tot I σ j := by
  have key : ∀ m, ∀ j, (σ j).val = m → 1 ≤ tot I σ j := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hj
      by_cases hpj : 1 ≤ pN I j
      · exact le_trans hpj (tot_self I σ j)
      · have hp0 : (I.p j : ℝ) = 0 := by
          rw [pval5 I hN j]
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
          exact le_trans this (tot_mono I σ i j hlt.le)
        · obtain ⟨a, _, hlt⟩ := hOR b hb
          have := ih (σ (Sum.inl a)).val (by rw [← hj]; exact hlt) (Sum.inl a) rfl
          exact le_trans this (tot_mono I σ _ _ hlt.le)
  exact fun j => key _ j rfl

/-- the integral LP (5) solution of an order -/
noncomputable def xOf5 (I : Instance) (ε' : ℝ) (σ : I.N ≃ Fin (Fintype.card I.N)) :
    I.N → ℕ → ℝ :=
  fun j l => if l = iota ε' (tot I σ j) then 1 else 0

theorem lp5_of_order (I : Instance) (hN : IsNormalized I) (ε' : ℝ) (hε : 0 < ε')
    (σ : I.N ≃ Fin (Fintype.card I.N))
    (hAND : ∀ i j, andRel I i j → σ i < σ j)
    (hOR : ∀ b, (orPred I b).Nonempty → ∃ a ∈ orPred I b, σ (Sum.inl a) < σ (Sum.inr b)) :
    LP5Feasible I ε' (xOf5 I ε' σ) ∧
      LP5Obj I ε' (xOf5 I ε' σ) ≤ ∑ b, (I.w (Sum.inr b) : ℝ) * (tot I σ (Sum.inr b) : ℝ) := by
  obtain ⟨hL1, hLT⟩ := numInt_spec I ε' hε
  set L := numIntervals I ε' with hL
  have hpos := tot_pos I hN σ hAND hOR
  have hTL : ∀ j, (tot I σ j : ℝ) ≤ tau ε' L := fun j =>
    le_trans (by exact_mod_cast tot_le I σ j) hLT
  have hiota : ∀ j, 1 ≤ iota ε' (tot I σ j) ∧ (tot I σ j : ℝ) ≤ tau ε' (iota ε' (tot I σ j)) :=
    fun j => iota_mem ε' _ L hL1 (hTL j)
  have hiotaL : ∀ j, iota ε' (tot I σ j) ≤ L := fun j => iota_le_of ε' _ L hL1 (hTL j)
  have hiota_mono : ∀ i j, σ i ≤ σ j → iota ε' (tot I σ i) ≤ iota ε' (tot I σ j) := by
    intro i j h
    apply iota_le_of ε' _ _ (hiota j).1
    have : (tot I σ i : ℝ) ≤ tot I σ j := by exact_mod_cast tot_mono I σ i j h
    linarith [(hiota j).2]
  have hcum : ∀ j l, cum (xOf5 I ε' σ) j l = if iota ε' (tot I σ j) ≤ l then 1 else 0 := by
    intro j l
    unfold cum xOf5
    rw [Finset.sum_ite_eq']
    by_cases h : iota ε' (tot I σ j) ≤ l
    · rw [if_pos (Finset.mem_Icc.mpr ⟨(hiota j).1, h⟩), if_pos h]
    · rw [if_neg (fun hm => h (Finset.mem_Icc.mp hm).2), if_neg h]
  have hcnn : ∀ j l, 0 ≤ cum (xOf5 I ε' σ) j l := by
    intro j l; rw [hcum]; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · unfold LP5Feasible
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j; rw [hcum, if_pos (hiotaL j)]
    · intro l hl
      rw [Finset.mem_Icc] at hl
      have hinner : ∀ j, ∑ k ∈ Finset.Icc 1 l, (pN I j : ℝ) * xOf5 I ε' σ j k =
          if iota ε' (tot I σ j) ≤ l then (pN I j : ℝ) else 0 := by
        intro j
        rw [← Finset.mul_sum]
        have := hcum j l
        unfold cum at this
        rw [this]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl (fun j _ => hinner j), ← Finset.sum_filter]
      set S := Finset.univ.filter (fun j => iota ε' (tot I σ j) ≤ l) with hS
      rcases S.eq_empty_or_nonempty with he | hne
      · rw [he, Finset.sum_empty]; linarith [tau_one_le ε' hε l]
      · obtain ⟨j0, hj0, hmax⟩ := S.exists_max_image σ hne
        have hsub : S ⊆ Finset.univ.filter (fun i => σ i ≤ σ j0) := by
          intro i hi
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hmax i hi⟩
        have h1 : ∑ j ∈ S, (pN I j : ℝ) ≤ (tot I σ j0 : ℝ) := by
          unfold tot
          push_cast
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
        have h2 : iota ε' (tot I σ j0) ≤ l := by
          rw [hS, Finset.mem_filter] at hj0; exact hj0.2
        have h3 := tau_mono ε' hε _ _ h2
        linarith [(hiota j0).2]
    · intro b hb l hl
      rw [Finset.mem_Icc] at hl
      obtain ⟨a, ha, hlt⟩ := hOR b hb
      rw [hcum]
      by_cases hc : iota ε' (tot I σ (Sum.inr b)) ≤ l
      · rw [if_pos hc]
        have ha' : iota ε' (tot I σ (Sum.inl a)) ≤ l := le_trans (hiota_mono _ _ hlt.le) hc
        have h3 : cum (xOf5 I ε' σ) (Sum.inl a) l = 1 := by rw [hcum, if_pos ha']
        have h2 : (1 : ℝ) ≤ ∑ a ∈ orPred I b, cum (xOf5 I ε' σ) (Sum.inl a) l := by
          calc (1 : ℝ) = cum (xOf5 I ε' σ) (Sum.inl a) l := h3.symm
            _ ≤ _ := Finset.single_le_sum (f := fun a => cum (xOf5 I ε' σ) (Sum.inl a) l)
              (fun a _ => hcnn _ _) ha
        linarith
      · rw [if_neg hc]
        have : 0 ≤ ∑ a ∈ orPred I b, cum (xOf5 I ε' σ) (Sum.inl a) l :=
          Finset.sum_nonneg (fun a _ => hcnn _ _)
        linarith
    · intro i j hij l hl
      have hm := hiota_mono _ _ (hAND i j hij).le
      rw [hcum, hcum]
      by_cases hc : iota ε' (tot I σ j) ≤ l
      · rw [if_pos hc, if_pos (le_trans hm hc)]; norm_num
      · rw [if_neg hc]; split_ifs <;> norm_num
    · intro j l _
      refine ⟨by unfold xOf5; split_ifs <;> norm_num, fun hlt => ?_⟩
      unfold xOf5
      rw [if_neg]
      intro he
      rw [he] at hlt
      have h1 : (pN I j : ℝ) ≤ tot I σ j := by exact_mod_cast tot_self I σ j
      linarith [(hiota j).2]
  · unfold LP5Obj
    apply Finset.sum_le_sum
    intro b _
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    unfold xOf5
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_Icc.mpr ⟨(hiota _).1, hiotaL _⟩)]
    exact tau_pred_le ε' hε _ L hL1 (hTL _) (hpos _)

theorem dsum {ι : Type} [DecidableEq ι] (C p : ι → ℝ) : ∀ n (S : Finset ι), S.card = n →
    (∀ i ∈ S, 0 ≤ p i) → (∀ i ∈ S, p i ≤ C i) →
    (∀ i ∈ S, ∀ k ∈ S, i ≠ k → C i ≤ C k - p k ∨ C k ≤ C i - p i) →
    ∀ M, 0 ≤ M → (∀ i ∈ S, C i ≤ M) → ∑ i ∈ S, p i ≤ M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS h0 hpC hd M hM0 hM
    rcases S.eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty]; exact hM0
    obtain ⟨m, hm, hmax⟩ := S.exists_max_image C hne
    set S1 := (S.erase m).filter (fun i => C i ≤ C m - p m) with hS1
    have hrest : ∑ i ∈ (S.erase m).filter (fun i => ¬ C i ≤ C m - p m), p i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_filter, Finset.mem_erase] at hi
      obtain ⟨⟨hne', hiS⟩, hnot⟩ := hi
      rcases hd i hiS m hm hne' with h | h
      · exact absurd h hnot
      · have := hmax i hiS
        have := h0 i hiS
        linarith
    have hsplit : ∑ i ∈ S.erase m, p i = ∑ i ∈ S1, p i := by
      rw [hS1, ← Finset.sum_filter_add_sum_filter_not (S.erase m) (fun i => C i ≤ C m - p m),
        hrest, add_zero]
    have hcard : S1.card < n := by
      have h1 : S1.card ≤ (S.erase m).card := Finset.card_filter_le _ _
      have h2 : (S.erase m).card = S.card - 1 := Finset.card_erase_of_mem hm
      have h3 : 0 < S.card := Finset.card_pos.mpr hne
      omega
    have hsub : S1 ⊆ S := fun i hi => Finset.mem_of_mem_erase (Finset.mem_filter.mp hi).1
    have hIH := ih S1.card hcard S1 rfl (fun i hi => h0 i (hsub hi)) (fun i hi => hpC i (hsub hi))
      (fun i hi k hk hik => hd i (hsub hi) k (hsub hk) hik) (C m - p m)
      (by linarith [hpC m hm]) (fun i hi => (Finset.mem_filter.mp hi).2)
    rw [← Finset.add_sum_erase S p hm, hsplit]
    linarith [hM m hm]

theorem order_of_sched5 (I : Instance) (hI : Acyclic I) (hN : IsNormalized I)
    (C : I.N → ℝ) (hC : IsFeasible I C) :
    ∃ σ : I.N ≃ Fin (Fintype.card I.N), (∀ i j, andRel I i j → σ i < σ j) ∧
      (∀ b, (orPred I b).Nonempty → ∃ a ∈ orPred I b, σ (Sum.inl a) < σ (Sum.inr b)) ∧
      ∀ j, (tot I σ j : ℝ) ≤ C j := by
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
  have hCj0 : 0 ≤ C j := le_trans (hpnn j) (hC1 j)
  unfold tot
  push_cast
  set S := Finset.univ.filter (fun i => σ i ≤ σ j) with hS
  have hp' : ∀ i, (pN I i : ℝ) = ((I.p i : ℚ≥0) : ℝ) := fun i => (pval5 I hN i).symm
  apply dsum C (fun i => (pN I i : ℝ)) S.card S rfl (fun i _ => Nat.cast_nonneg _)
    (fun i _ => by show (pN I i : ℝ) ≤ C i; rw [hp']; exact hC1 i)
    (fun i _ k _ hik => by
      show C i ≤ C k - (pN I k : ℝ) ∨ C k ≤ C i - (pN I i : ℝ)
      rw [hp', hp']; exact hC2 i k hik) (C j) hCj0
  intro i hi
  rw [hS, Finset.mem_filter] at hi
  by_contra hcon
  push_neg at hcon
  have : f j < f i := (hlt j i).mpr (Or.inl hcon)
  have := (hσ j i).mpr this
  exact absurd hi.2 (not_le.mpr this)

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

/-- truncation outside the interval range -/
noncomputable def trunc5 (I : Instance) (ε' : ℝ) (y : I.N → ℕ → ℝ) : I.N → ℕ → ℝ :=
  fun j t => if t ∈ Finset.Icc 1 (numIntervals I ε') then y j t else 0

theorem cum_trunc5 (I : Instance) (ε' : ℝ) (y : I.N → ℕ → ℝ) (j : I.N) (t : ℕ)
    (ht : t ≤ numIntervals I ε') : cum (trunc5 I ε' y) j t = cum y j t := by
  unfold cum trunc5
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_Icc] at hs
  rw [if_pos (Finset.mem_Icc.mpr ⟨hs.1, by omega⟩)]

theorem trunc5_feasible (I : Instance) (ε' : ℝ) (y : I.N → ℕ → ℝ) (hy : LP5Feasible I ε' y) :
    LP5Feasible I ε' (trunc5 I ε' y) := by
  unfold LP5Feasible at hy ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hy
  refine ⟨fun j => by rw [cum_trunc5 I ε' y j _ le_rfl]; exact h1 j, ?_, ?_, ?_, ?_⟩
  · intro l hl
    have := h2 l hl
    rw [Finset.mem_Icc] at hl
    have e : ∀ j, ∑ k ∈ Finset.Icc 1 l, (pN I j : ℝ) * trunc5 I ε' y j k =
        ∑ k ∈ Finset.Icc 1 l, (pN I j : ℝ) * y j k := by
      intro j
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      unfold trunc5
      rw [if_pos (Finset.mem_Icc.mpr ⟨hk.1, by omega⟩)]
    rw [Finset.sum_congr rfl (fun j _ => e j)]
    exact this
  · intro b hb l hl
    have := h3 b hb l hl
    rw [Finset.mem_Icc] at hl
    rw [cum_trunc5 I ε' y (Sum.inr b) l hl.2]
    rw [Finset.sum_congr rfl (fun a _ => cum_trunc5 I ε' y (Sum.inl a) l hl.2)]
    exact this
  · intro i j hij l hl
    have := h4 i j hij l hl
    rw [Finset.mem_Icc] at hl
    rw [cum_trunc5 I ε' y j l hl.2, cum_trunc5 I ε' y i l hl.2]
    exact this
  · intro j l hl
    unfold trunc5
    rw [if_pos hl]
    exact h5 j l hl

theorem obj5_trunc (I : Instance) (ε' : ℝ) (y : I.N → ℕ → ℝ) :
    LP5Obj I ε' (trunc5 I ε' y) = LP5Obj I ε' y := by
  unfold LP5Obj
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  unfold trunc5
  rw [if_pos ht]

theorem obj5_cont (I : Instance) (ε' : ℝ) : Continuous (LP5Obj I ε') := by
  unfold LP5Obj
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

theorem feasible5_closed (I : Instance) (ε' : ℝ) :
    IsClosed {y : I.N → ℕ → ℝ | LP5Feasible I ε' y} := by
  unfold LP5Feasible
  simp only [Set.setOf_and, Set.setOf_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))
  · exact isClosed_iInter fun j => isClosed_eq (cum_cont I j _) continuous_const
  · refine isClosed_iInter fun t => isClosed_iInter fun _ => isClosed_le ?_ continuous_const
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro s _
    exact continuous_const.mul ((continuous_apply s).comp (continuous_apply j))
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
      IsClosed.inter (isClosed_le continuous_const ?_) (isClosed_iInter fun _ =>
        isClosed_eq ?_ continuous_const)
    · exact (continuous_apply t).comp (continuous_apply j)
    · exact (continuous_apply t).comp (continuous_apply j)

end Aux_AOS_lp5

open AndOrSched Aux_AOS_lp5 in
theorem solution (I : AndOrSched.Instance) (hI : AndOrSched.Acyclic I)
    (hN : AndOrSched.IsNormalized I)
    (ε' : ℝ) (hε' : 0 < ε') :
    (∃ x, AndOrSched.LP5Optimal I ε' x) ∧
    ∀ x, AndOrSched.LP5Optimal I ε' x → ∀ C : I.N → ℝ, AndOrSched.IsFeasible I C →
      AndOrSched.LP5Obj I ε' x ≤ AndOrSched.cost I C := by
  obtain ⟨σ0, hσ0⟩ := sigma_lin (sec I) (sec_inj I)
  have hAND0 : ∀ i j, andRel I i j → σ0 i < σ0 j := fun i j h => (hσ0 i j).mpr (and_sec I hI i j h)
  have hOR0 : ∀ b, (orPred I b).Nonempty → ∃ a ∈ orPred I b, σ0 (Sum.inl a) < σ0 (Sum.inr b) := by
    intro b hb
    obtain ⟨a, ha⟩ := hb
    exact ⟨a, ha, (hσ0 _ _).mpr (sec_lt_kind I _ _ (by simp [kind]))⟩
  obtain ⟨hfeas0, _⟩ := lp5_of_order I hN ε' hε' σ0 hAND0 hOR0
  set L := numIntervals I ε' with hL
  let K : Set (I.N → ℕ → ℝ) :=
    {y | LP5Feasible I ε' y} ∩ {y | ∀ j t, t ∉ Finset.Icc 1 L → y j t = 0}
  have hKclosed : IsClosed K := by
    apply IsClosed.inter (feasible5_closed I ε')
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply t).comp (continuous_apply j)) continuous_const
  have hKsub : K ⊆ Set.pi Set.univ
      (fun _ : I.N => Set.pi Set.univ (fun _ : ℕ => Set.Icc (0 : ℝ) 1)) := by
    intro y hy
    obtain ⟨hyF, hy0⟩ := hy
    have hyF' := hyF
    unfold LP5Feasible at hyF'
    obtain ⟨h1, _, _, _, h5⟩ := hyF'
    rw [Set.mem_univ_pi]
    intro j
    rw [Set.mem_univ_pi]
    intro t
    by_cases ht : t ∈ Finset.Icc 1 L
    · refine ⟨(h5 j t ht).1, ?_⟩
      have := Finset.single_le_sum (f := fun s => y j s) (fun s hs => (h5 j s hs).1) ht
      have h1j := h1 j
      unfold cum at h1j
      linarith
    · rw [hy0 j t ht]; exact ⟨le_rfl, zero_le_one⟩
  have hcomp : IsCompact (Set.pi Set.univ
      (fun _ : I.N => Set.pi Set.univ (fun _ : ℕ => Set.Icc (0 : ℝ) 1))) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  have hKcomp : IsCompact K := hcomp.of_isClosed_subset hKclosed hKsub
  have hx0K : trunc5 I ε' (xOf5 I ε' σ0) ∈ K := by
    refine Set.mem_inter (trunc5_feasible I ε' _ hfeas0) ?_
    show ∀ j t, t ∉ Finset.Icc 1 L → trunc5 I ε' (xOf5 I ε' σ0) j t = 0
    intro j t ht
    show (if t ∈ Finset.Icc 1 (numIntervals I ε') then xOf5 I ε' σ0 j t else 0) = 0
    rw [if_neg ht]
  obtain ⟨xs, hxsK, hmin⟩ := hKcomp.exists_isMinOn ⟨_, hx0K⟩ (obj5_cont I ε').continuousOn
  have hopt : LP5Optimal I ε' xs := by
    unfold LP5Optimal
    refine ⟨hxsK.1, fun y hy => ?_⟩
    have hyK : trunc5 I ε' y ∈ K := by
      refine Set.mem_inter (trunc5_feasible I ε' y hy) ?_
      show ∀ j t, t ∉ Finset.Icc 1 L → trunc5 I ε' y j t = 0
      intro j t ht
      show (if t ∈ Finset.Icc 1 (numIntervals I ε') then y j t else 0) = 0
      rw [if_neg ht]
    have := isMinOn_iff.mp hmin _ hyK
    rw [obj5_trunc] at this
    exact this
  refine ⟨⟨xs, hopt⟩, ?_⟩
  intro x hx C hC
  obtain ⟨σ, hAND, hOR, htot⟩ := order_of_sched5 I hI hN C hC
  obtain ⟨hfeas, hobj⟩ := lp5_of_order I hN ε' hε' σ hAND hOR
  have hx' := hx
  unfold LP5Optimal at hx'
  have h1 := hx'.2 _ hfeas
  exact le_trans h1 (le_trans hobj (cost_ge I hN C (tot I σ) htot))
