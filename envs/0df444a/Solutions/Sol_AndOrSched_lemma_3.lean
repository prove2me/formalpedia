-- Prove2me | solution 1 for AndOrSched.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:18:53.177183+00:00
-- url     : https://prove2.me/submissions/94ad111e-cc9f-407f-8da5-a721d19ae7dc

import Mathlib
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_Compat
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_IsNormalized
import Definitions.Def_AndOrSched_LP1Feasible
import Definitions.Def_AndOrSched_LP5Feasible
import Definitions.Def_AndOrSched_LP5Obj
import Definitions.Def_AndOrSched_LP5Optimal
import Definitions.Def_AndOrSched_alphaPoint
import Definitions.Def_AndOrSched_cost
import Definitions.Def_AndOrSched_delta
import Definitions.Def_AndOrSched_fracC5
import Definitions.Def_AndOrSched_key
import Definitions.Def_AndOrSched_listC
import Definitions.Def_AndOrSched_nonRedPred
import Definitions.Def_AndOrSched_numIntervals
import Definitions.Def_AndOrSched_orPred
import Definitions.Def_AndOrSched_tau
import Definitions.Def_AndOrSched_worstCost
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
theorem Aux_AOS_L3.lp5_le_cost (I : AndOrSched.Instance) (hI : AndOrSched.Acyclic I)
    (hN : AndOrSched.IsNormalized I) (ε' : ℝ) (hε' : 0 < ε') (x : I.N → ℕ → ℝ)
    (hx : AndOrSched.LP5Optimal I ε' x) (C : I.N → ℝ) (hC : AndOrSched.IsFeasible I C) :
    AndOrSched.LP5Obj I ε' x ≤ AndOrSched.cost I C := by
  obtain ⟨σ, hAND, hOR, htot⟩ := order_of_sched5 I hI hN C hC
  obtain ⟨hfeas, hobj⟩ := lp5_of_order I hN ε' hε' σ hAND hOR
  have hx' := hx
  unfold LP5Optimal at hx'
  have h1 := hx'.2 _ hfeas
  exact le_trans h1 (le_trans hobj (cost_ge I hN C (tot I σ) htot))



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
theorem Aux_AOS_L3.feas5_main (I : AndOrSched.Instance) (hI : AndOrSched.Acyclic I)
    (hint : ∀ j, ∃ n : ℕ, I.p j = n)
    (hred : ∀ b, AndOrSched.nonRedPred I b = AndOrSched.orPred I b) (ε' : ℝ) (hε' : 0 < ε')
    (x : I.N → ℕ → ℝ) (hx : AndOrSched.LP5Feasible I ε' x) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
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
    set T := numIntervals I ε' with hT
    have hx' := hx
    unfold LP5Feasible at hx'
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
        exact (hnn j s (Finset.mem_Icc.mpr ⟨hs.1, by omega⟩)).1
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
    -- AND precedence gives key order
    have hand_key : ∀ i j, andRel I i j → K i ≤ K j := by
      intro i j hij
      cases i with
      | inl a =>
        cases j with
        | inr b' => exact absurd hij (by simp [andRel])
        | inl a' =>
          rw [hKA, hKA]
          have hl1 := ap_pos _ hθA0 hθA1 (Sum.inl a')
          have hl2 := ap_T _ hθA1 (Sum.inl a')
          have h1 := hand (Sum.inl a) (Sum.inl a') hij (alphaPoint x (Sum.inl a') (β / (delta I : ℝ)))
            (Finset.mem_Icc.mpr ⟨hl1, hl2⟩)
          have h2 := ap_mem _ hθA1 (Sum.inl a')
          exact ap_le _ _ _ (by linarith)
      | inr b =>
        cases j with
        | inl a' => exact absurd hij (by simp [andRel])
        | inr b' =>
          rw [hKB, hKB]
          have hl1 := ap_pos _ hβ0 hβ1 (Sum.inr b')
          have hl2 := ap_T _ hβ1 (Sum.inr b')
          have h1 := hand (Sum.inr b) (Sum.inr b') hij (alphaPoint x (Sum.inr b') β)
            (Finset.mem_Icc.mpr ⟨hl1, hl2⟩)
          have h2 := ap_mem _ hβ1 (Sum.inr b')
          exact ap_le _ _ _ (by linarith)
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
      set t := alphaPoint x (Sum.inr b) β with ht_def
      have hl1 : 1 ≤ t := ap_pos _ hβ0 hβ1 (Sum.inr b)
      have hl2 : t ≤ T := ap_T _ hβ1 (Sum.inr b)
      have ht4 : β ≤ cum x (Sum.inr b) t := ap_mem _ hβ1 (Sum.inr b)
      have h1 := hor b hne t (Finset.mem_Icc.mpr ⟨hl1, hl2⟩)
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



namespace Aux_AndOrSched_eq_27

theorem sum_Icc_eq_range (g : ℕ → ℝ) (n : ℕ) :
    ∑ l ∈ Finset.Icc 1 n, g l = ∑ k ∈ Finset.range n, g (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

theorem tau_mono (ε' : ℝ) (hε' : 0 < ε') : Monotone (AndOrSched.tau ε') := by
  intro m n hmn
  unfold AndOrSched.tau
  by_cases hm : m = 0
  · by_cases hn : n = 0
    · simp [hm, hn]
    · simp only [hm, hn, if_true, if_false]
      exact one_le_pow₀ (by linarith)
  · have hn : n ≠ 0 := by omega
    simp only [hm, hn, if_false]
    exact pow_le_pow_right₀ (by linarith) (by omega)

end Aux_AndOrSched_eq_27

open AndOrSched in
theorem Aux_AOS_L3.eq27 (I : Instance) (ε' : ℝ) (hε' : 0 < ε') (x : I.N → ℕ → ℝ) (hx : LP5Feasible I ε' x)
    (j : I.N) :
    MeasureTheory.IntegrableOn (fun γ : ℝ => tau ε' (alphaPoint x j γ - 1)) (Set.Ioc 0 1) ∧
    ∫ γ in Set.Ioc (0 : ℝ) 1, tau ε' (alphaPoint x j γ - 1) ≤ fracC5 I ε' x j := by
  obtain ⟨L, hL⟩ : ∃ L, L = numIntervals I ε' := ⟨_, rfl⟩
  have hcL : cum x j L = 1 := by rw [hL]; exact hx.1 j
  have hnn : ∀ s, 1 ≤ s → s ≤ L → 0 ≤ x j s := fun s h1 h2 =>
    (hx.2.2.2.2 j s (by rw [Finset.mem_Icc, ← hL]; exact ⟨h1, h2⟩)).1
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
  have hfmono : MonotoneOn (fun γ : ℝ => tau ε' (alphaPoint x j γ - 1)) (Set.Icc 0 1) := by
    intro γ₁ _ γ₂ hγ₂ h12
    have := hαmono γ₁ γ₂ h12 hγ₂.2
    show tau ε' _ ≤ tau ε' _
    exact Aux_AndOrSched_eq_27.tau_mono ε' hε' (by omega)
  have hII : IntervalIntegrable (fun γ : ℝ => tau ε' (alphaPoint x j γ - 1))
      MeasureTheory.volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hfmono
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hII, ?_⟩
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hint : ∀ k < L, IntervalIntegrable (fun γ : ℝ => tau ε' (alphaPoint x j γ - 1))
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
      (∫ γ in cum x j k..cum x j (k + 1), tau ε' (alphaPoint x j γ - 1)) =
        tau ε' k * x j (k + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hle := hmono k (k + 1) (by omega) (by omega)
    have hcongr : (∫ γ in cum x j k..cum x j (k + 1), tau ε' (alphaPoint x j γ - 1)) =
        ∫ γ in cum x j k..cum x j (k + 1), tau ε' k := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall (fun γ hγ => ?_)
      rw [Set.uIoc_of_le hle] at hγ
      rw [hα k hk γ hγ.1 hγ.2]
      simp
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, hstep k]
    ring
  rw [Finset.sum_congr rfl hpiece]
  apply le_of_eq
  unfold fracC5
  rw [← hL, Aux_AndOrSched_eq_27.sum_Icc_eq_range (fun l => tau ε' (l - 1) * x j l) L]
  apply Finset.sum_congr rfl
  intro k _
  simp



open AndOrSched in
theorem Aux_AOS_L3.eq28 (I : Instance) (hint : ∀ j, ∃ n : ℕ, I.p j = n) (ε' : ℝ) (hε' : 0 < ε')
    (x : I.N → ℕ → ℝ) (hx : LP5Feasible I ε' x) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (σ : I.N ≃ Fin (Fintype.card I.N)) (hσ : Compat I (key I x β) σ) (b : I.B) :
    β / (delta I : ℝ) * listC I σ (Sum.inr b) ≤ tau ε' (alphaPoint x (Sum.inr b) β) := by
  obtain ⟨H, hH⟩ : ∃ H, H = numIntervals I ε' := ⟨_, rfl⟩
  have hcH : ∀ j, cum x j H = 1 := fun j => by rw [hH]; exact hx.1 j
  have hnn : ∀ j s, 1 ≤ s → s ≤ H → 0 ≤ x j s := fun j s h1 h2 =>
    (hx.2.2.2.2 j s (by rw [Finset.mem_Icc, ← hH]; exact ⟨h1, h2⟩)).1
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
  have ht1 : 1 ≤ t := by
    by_contra h0
    have h0' : t = 0 := by omega
    have h1 := halpha_mem (Sum.inr b) β hβ1
    rw [← ht, h0', hc0] at h1
    linarith
  have hpv : ∀ i, (I.p i : ℝ) = (pN I i : ℝ) := by
    intro i
    obtain ⟨n, hn⟩ := hint i
    have hpN : pN I i = n := by
      unfold pN
      rw [hn, Nat.floor_natCast]
    rw [hpN, hn, NNRat.cast_natCast]
  have hsumcap : ∑ i, (pN I i : ℝ) * cum x i t ≤ tau ε' t := by
    have h := hx.2.1 t (by rw [Finset.mem_Icc, ← hH]; exact ⟨ht1, htH⟩)
    unfold cum
    simp_rw [Finset.mul_sum]
    exact h
  unfold listC
  rw [Finset.mul_sum]
  calc ∑ i ∈ Finset.univ.filter (fun i => σ i ≤ σ (Sum.inr b)), α * (I.p i : ℝ)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => σ i ≤ σ (Sum.inr b)), (pN I i : ℝ) * cum x i t := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_filter] at hi
        have h1 := hclaim i (hkey i hi.2)
        rw [hpv i]
        have h2 : (0 : ℝ) ≤ (pN I i : ℝ) := Nat.cast_nonneg _
        nlinarith
    _ ≤ ∑ i, (pN I i : ℝ) * cum x i t := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        exact mul_nonneg (Nat.cast_nonneg _) (hcnn i t htH)
    _ ≤ tau ε' t := hsumcap


namespace Aux_AOS_L3

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

theorem tau_succ_le (ε' : ℝ) (hε : 0 < ε') (n : ℕ) (hn : 1 ≤ n) :
    tau ε' n ≤ (1 + ε') * tau ε' (n - 1) := by
  unfold tau
  by_cases h1 : n = 1
  · subst h1
    norm_num
    linarith
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [if_neg (show m + 2 ≠ 0 by omega), if_neg (show m + 2 - 1 ≠ 0 by omega),
      show m + 2 - 1 - 1 = m by omega, show m + 2 - 1 = m + 1 by omega]
    exact le_of_eq (by ring)

theorem tau_int (I : Instance) (ε' : ℝ) (hε' : 0 < ε') (x : I.N → ℕ → ℝ)
    (hx : LP5Feasible I ε' x) (j : I.N) :
    MeasureTheory.IntegrableOn (fun γ : ℝ => tau ε' (alphaPoint x j γ)) (Set.Ioc 0 1) ∧
    ∫ γ in Set.Ioc (0 : ℝ) 1, tau ε' (alphaPoint x j γ) ≤ (1 + ε') * fracC5 I ε' x j := by
  obtain ⟨L, hL⟩ : ∃ L, L = numIntervals I ε' := ⟨_, rfl⟩
  have hcL : cum x j L = 1 := by rw [hL]; exact hx.1 j
  have hnn : ∀ s, 1 ≤ s → s ≤ L → 0 ≤ x j s := fun s h1 h2 =>
    (hx.2.2.2.2 j s (by rw [Finset.mem_Icc, ← hL]; exact ⟨h1, h2⟩)).1
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
  have hαpos : ∀ γ : ℝ, 0 < γ → γ ≤ 1 → 1 ≤ alphaPoint x j γ := by
    intro γ h0 h1
    by_contra hlt
    push_neg at hlt
    have hz : alphaPoint x j γ = 0 := by omega
    have hne : ({t : ℕ | γ ≤ cum x j t} : Set ℕ).Nonempty := ⟨L, by
      show γ ≤ cum x j L
      rw [hcL]; exact h1⟩
    have hmem : γ ≤ cum x j (alphaPoint x j γ) := Nat.sInf_mem hne
    rw [hz, hc0] at hmem
    linarith
  have hfmono : MonotoneOn (fun γ : ℝ => tau ε' (alphaPoint x j γ)) (Set.Icc 0 1) := by
    intro γ₁ _ γ₂ hγ₂ h12
    have := hαmono γ₁ γ₂ h12 hγ₂.2
    show tau ε' _ ≤ tau ε' _
    exact Aux_AOS_lp5.tau_mono ε' hε' _ _ this
  have hII : IntervalIntegrable (fun γ : ℝ => tau ε' (alphaPoint x j γ))
      MeasureTheory.volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hfmono
  have hI1 : MeasureTheory.IntegrableOn (fun γ : ℝ => tau ε' (alphaPoint x j γ)) (Set.Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hII
  refine ⟨hI1, ?_⟩
  obtain ⟨h27i, h27⟩ := Aux_AOS_L3.eq27 I ε' hε' x hx j
  have hI2 : MeasureTheory.IntegrableOn (fun γ : ℝ => (1 + ε') * tau ε' (alphaPoint x j γ - 1))
      (Set.Ioc 0 1) := MeasureTheory.Integrable.const_mul h27i _
  have hle := MeasureTheory.setIntegral_mono_on hI1 hI2 measurableSet_Ioc (fun γ hγ =>
    tau_succ_le ε' hε' _ (hαpos γ hγ.1 hγ.2))
  rw [MeasureTheory.integral_const_mul] at hle
  have := mul_le_mul_of_nonneg_left h27 (by linarith : (0 : ℝ) ≤ 1 + ε')
  linarith

theorem wc_pointwise5 (I : Instance) (hN : IsNormalized I) (ε' : ℝ) (hε' : 0 < ε')
    (x : I.N → ℕ → ℝ) (hx : LP5Feasible I ε' x) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    2 * β * worstCost I (key I x β) ≤
      2 * (delta I : ℝ) * ∑ b, (I.w (Sum.inr b) : ℝ) * tau ε' (alphaPoint x (Sum.inr b) β) := by
  have hΔ1 : 1 ≤ delta I := le_max_left _ _
  have hΔ : (1 : ℝ) ≤ delta I := by exact_mod_cast hΔ1
  obtain ⟨R, hR⟩ : ∃ R, R = ∑ b, (I.w (Sum.inr b) : ℝ) * tau ε' (alphaPoint x (Sum.inr b) β) :=
    ⟨_, rfl⟩
  rw [← hR]
  have hR0 : 0 ≤ R := by
    rw [hR]
    exact Finset.sum_nonneg (fun b _ => mul_nonneg (by positivity)
      (le_trans zero_le_one (Aux_AOS_lp5.tau_one_le ε' hε' _)))
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
    have h3 := eq28 I hN.2.1 ε' hε' x hx β hβ0 hβ1 σ.1 σ.2 b
    have hl : listC I σ.1 (Sum.inr b) ≤
        (delta I : ℝ) / β * tau ε' (alphaPoint x (Sum.inr b) β) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hβ0]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)] at h3
      linarith
    have hw : (0 : ℝ) ≤ (I.w (Sum.inr b) : ℝ) := by positivity
    calc (I.w (Sum.inr b) : ℝ) * listC I σ.1 (Sum.inr b)
        ≤ (I.w (Sum.inr b) : ℝ) * ((delta I : ℝ) / β * tau ε' (alphaPoint x (Sum.inr b) β)) :=
          mul_le_mul_of_nonneg_left hl hw
      _ = (delta I : ℝ) / β * ((I.w (Sum.inr b) : ℝ) * tau ε' (alphaPoint x (Sum.inr b) β)) := by
          ring
  have hfin : 2 * β * ((delta I : ℝ) / β * R) = 2 * (delta I : ℝ) * R := by
    have hc : β * ((delta I : ℝ) / β) = delta I := by field_simp
    calc 2 * β * ((delta I : ℝ) / β * R) = 2 * (β * ((delta I : ℝ) / β)) * R := by ring
      _ = 2 * (delta I : ℝ) * R := by rw [hc]
  calc 2 * β * worstCost I (key I x β) ≤ 2 * β * ((delta I : ℝ) / β * R) :=
        mul_le_mul_of_nonneg_left hwc (by positivity)
    _ = 2 * (delta I : ℝ) * R := hfin

end Aux_AOS_L3

set_option maxHeartbeats 1600000 in
open AndOrSched Aux_AOS_L3 in
theorem solution (I : Instance) (hI : Acyclic I) (hN : IsNormalized I) (ε : ℝ) (hε : 0 < ε)
    (x : I.N → ℕ → ℝ) (hx : LP5Optimal I (ε / (2 * (delta I : ℝ))) x) :
    (∀ β : ℝ, 0 < β → β ≤ 1 →
      (∃ σ, Compat I (key I x β) σ) ∧ ∀ σ, Compat I (key I x β) σ → IsFeasible I (listC I σ)) ∧
    MeasureTheory.IntegrableOn (fun β : ℝ => 2 * β * worstCost I (key I x β)) (Set.Ioc 0 1) ∧
    ∀ C : I.N → ℝ, IsFeasible I C →
      ∫ β in Set.Ioc (0 : ℝ) 1, 2 * β * worstCost I (key I x β) ≤
        (2 * (delta I : ℝ) + ε) * cost I C := by
  have hΔ1 : 1 ≤ delta I := le_max_left _ _
  have hΔ : (1 : ℝ) ≤ delta I := by exact_mod_cast hΔ1
  obtain ⟨ε', hε'def⟩ : ∃ ε', ε' = ε / (2 * (delta I : ℝ)) := ⟨_, rfl⟩
  rw [← hε'def] at hx
  have hε' : 0 < ε' := by rw [hε'def]; exact div_pos hε (by linarith)
  have hxF : LP5Feasible I ε' x := hx.1
  have hpart1 : ∀ β : ℝ, 0 < β → β ≤ 1 →
      (∃ σ, Compat I (key I x β) σ) ∧ ∀ σ, Compat I (key I x β) σ → IsFeasible I (listC I σ) :=
    fun β h0 h1 => feas5_main I hI hN.2.1 hN.2.2.2 ε' hε' x hxF β h0 h1
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
  have hal := fun b : I.B => tau_int I ε' hε' x hxF (Sum.inr b)
  have hterm : ∀ b ∈ (Finset.univ : Finset I.B), MeasureTheory.Integrable
      (fun β : ℝ => (I.w (Sum.inr b) : ℝ) * tau ε' (alphaPoint x (Sum.inr b) β))
      (MeasureTheory.volume.restrict (Set.Ioc 0 1)) :=
    fun b _ => MeasureTheory.Integrable.const_mul (hal b).1 _
  have hsumI : MeasureTheory.Integrable
      (fun β : ℝ => ∑ b, (I.w (Sum.inr b) : ℝ) * tau ε' (alphaPoint x (Sum.inr b) β))
      (MeasureTheory.volume.restrict (Set.Ioc 0 1)) :=
    MeasureTheory.integrable_finset_sum _ hterm
  have hRint : MeasureTheory.IntegrableOn (fun β : ℝ => 2 * (delta I : ℝ) *
      ∑ b, (I.w (Sum.inr b) : ℝ) * tau ε' (alphaPoint x (Sum.inr b) β)) (Set.Ioc 0 1) :=
    MeasureTheory.Integrable.const_mul hsumI _
  have hmono := MeasureTheory.setIntegral_mono_on hint hRint measurableSet_Ioc
    (fun β hβ => wc_pointwise5 I hN ε' hε' x hxF β hβ.1 hβ.2)
  have hRval : ∫ β in Set.Ioc (0 : ℝ) 1, 2 * (delta I : ℝ) *
      ∑ b, (I.w (Sum.inr b) : ℝ) * tau ε' (alphaPoint x (Sum.inr b) β) =
      2 * (delta I : ℝ) * ∑ b, (I.w (Sum.inr b) : ℝ) *
        ∫ β in Set.Ioc (0 : ℝ) 1, tau ε' (alphaPoint x (Sum.inr b) β) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finset_sum _ hterm]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    rw [MeasureTheory.integral_const_mul]
  have hRle : ∑ b, (I.w (Sum.inr b) : ℝ) *
        ∫ β in Set.Ioc (0 : ℝ) 1, tau ε' (alphaPoint x (Sum.inr b) β) ≤
      (1 + ε') * LP5Obj I ε' x := by
    unfold LP5Obj
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    have hw : (0 : ℝ) ≤ (I.w (Sum.inr b) : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left (hal b).2 hw
    have e : (I.w (Sum.inr b) : ℝ) * ((1 + ε') * fracC5 I ε' x (Sum.inr b)) =
        (1 + ε') * ((I.w (Sum.inr b) : ℝ) * ∑ l ∈ Finset.Icc 1 (numIntervals I ε'),
          tau ε' (l - 1) * x (Sum.inr b) l) := by
      unfold fracC5; ring
    linarith
  have hlp := lp5_le_cost I hI hN ε' hε' x hx C hC
  have hΔ0 : (0 : ℝ) ≤ 2 * (delta I : ℝ) := by positivity
  have hΔ2 : (2 * (delta I : ℝ)) ≠ 0 := ne_of_gt (by linarith)
  have hcoef : 2 * (delta I : ℝ) * (1 + ε') = 2 * (delta I : ℝ) + ε := by
    have h2 : 2 * (delta I : ℝ) * (ε / (2 * (delta I : ℝ))) = ε := by field_simp
    rw [hε'def, mul_add, mul_one, h2]
  have h1 := mul_le_mul_of_nonneg_left hRle hΔ0
  have h2 := mul_le_mul_of_nonneg_left hlp
    (show (0 : ℝ) ≤ 2 * (delta I : ℝ) * (1 + ε') by positivity)
  calc ∫ β in Set.Ioc (0 : ℝ) 1, 2 * β * worstCost I (key I x β)
      ≤ ∫ β in Set.Ioc (0 : ℝ) 1, 2 * (delta I : ℝ) *
          ∑ b, (I.w (Sum.inr b) : ℝ) * tau ε' (alphaPoint x (Sum.inr b) β) := hmono
    _ = 2 * (delta I : ℝ) * ∑ b, (I.w (Sum.inr b) : ℝ) *
          ∫ β in Set.Ioc (0 : ℝ) 1, tau ε' (alphaPoint x (Sum.inr b) β) := hRval
    _ ≤ 2 * (delta I : ℝ) * ((1 + ε') * LP5Obj I ε' x) := h1
    _ = 2 * (delta I : ℝ) * (1 + ε') * LP5Obj I ε' x := by ring
    _ ≤ 2 * (delta I : ℝ) * (1 + ε') * cost I C := h2
    _ = (2 * (delta I : ℝ) + ε) * cost I C := by rw [hcoef]
