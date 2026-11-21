-- Prove2me | solution 1 for AndOrSched.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:47:02.507771+00:00
-- url     : https://prove2.me/submissions/eb74f43b-d2fc-4d19-ab6f-7d13d0c7dd20

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_LP1Feasible
import Definitions.Def_AndOrSched_horizon
import Definitions.Def_AndOrSched_key
import Definitions.Def_AndOrSched_cand
open scoped Classical NNReal

namespace Aux_AndOrSched_lemma_2

theorem sInf_eq_of (S1 S2 : Set ℕ) (M : ℕ) (h1 : M ∈ S1) (h2 : M ∈ S2)
    (h : ∀ t ≤ M, t ∈ S1 ↔ t ∈ S2) : sInf S1 = sInf S2 := by
  have a1 : sInf S1 ∈ S1 := Nat.sInf_mem ⟨M, h1⟩
  have a2 : sInf S2 ∈ S2 := Nat.sInf_mem ⟨M, h2⟩
  have b1 : sInf S1 ≤ M := Nat.sInf_le h1
  have b2 : sInf S2 ≤ M := Nat.sInf_le h2
  apply le_antisymm
  · exact Nat.sInf_le ((h _ b2).mpr a2)
  · exact Nat.sInf_le ((h _ b1).mp a1)

end Aux_AndOrSched_lemma_2

open AndOrSched Aux_AndOrSched_lemma_2 in
theorem solution (I : AndOrSched.Instance) (hint : ∀ j, ∃ n : ℕ, I.p j = n) (hp : ∀ j, I.p j ≤ 1)
    (x : I.N → ℕ → ℝ) (hx : AndOrSched.LP1Feasible I x) :
    (∀ β ∈ AndOrSched.cand I x (AndOrSched.horizon I), 0 < β ∧ β ≤ 1) ∧
    AndOrSched.horizon I ≤ Fintype.card I.N ∧
    (AndOrSched.cand I x (AndOrSched.horizon I)).card ≤ Fintype.card I.N * AndOrSched.horizon I + 1 ∧
    ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ β' ∈ AndOrSched.cand I x (AndOrSched.horizon I),
      AndOrSched.key I x β' = AndOrSched.key I x β := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro β hβ
    unfold cand at hβ
    rcases Finset.mem_insert.mp hβ with h | h
    · rw [h]; norm_num
    · exact (Finset.mem_filter.mp h).2
  · unfold horizon
    have h1 : ∀ j ∈ (Finset.univ : Finset I.N), pN I j ≤ 1 := by
      intro j _
      unfold pN
      calc ⌊I.p j⌋₊ ≤ ⌊(1 : ℚ≥0)⌋₊ := Nat.floor_le_floor (hp j)
        _ = 1 := Nat.floor_one
    calc ∑ j, pN I j ≤ ∑ _j : I.N, 1 := Finset.sum_le_sum h1
      _ = Fintype.card I.N := by simp
  · unfold cand
    set M := horizon I
    have e1 : (Finset.univ ×ˢ Finset.Icc 1 M : Finset (I.A × ℕ)).card = Fintype.card I.A * M := by
      rw [Finset.card_product, Finset.card_univ, Nat.card_Icc, Nat.add_sub_cancel]
    have e2 : (Finset.univ ×ˢ Finset.Icc 1 M : Finset (I.B × ℕ)).card = Fintype.card I.B * M := by
      rw [Finset.card_product, Finset.card_univ, Nat.card_Icc, Nat.add_sub_cancel]
    refine le_trans (Finset.card_insert_le _ _) ?_
    refine le_trans (Nat.add_le_add_right (le_trans (Finset.card_filter_le _ _)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add (le_trans Finset.card_image_le (le_of_eq e1))
        (le_trans Finset.card_image_le (le_of_eq e2))))) 1) (le_of_eq ?_)
    show Fintype.card I.A * M + Fintype.card I.B * M + 1 = Fintype.card (I.A ⊕ I.B) * M + 1
    rw [Fintype.card_sum]
    ring
  · intro β hβ0 hβ1
    set M := horizon I
    set C := cand I x M with hC
    have h1C : (1 : ℝ) ∈ C := by rw [hC]; unfold cand; exact Finset.mem_insert_self _ _
    have hS : (C.filter (fun c => β ≤ c)).Nonempty := ⟨1, Finset.mem_filter.mpr ⟨h1C, hβ1⟩⟩
    have hmem := (C.filter (fun c => β ≤ c)).min'_mem hS
    refine ⟨(C.filter (fun c => β ≤ c)).min' hS, (Finset.mem_filter.mp hmem).1, ?_⟩
    set β' := (C.filter (fun c => β ≤ c)).min' hS with hβ'
    have hββ' : β ≤ β' := (Finset.mem_filter.mp hmem).2
    have hβ'1 : β' ≤ 1 := Finset.min'_le _ 1 (Finset.mem_filter.mpr ⟨h1C, hβ1⟩)
    have hmin : ∀ c ∈ C, β ≤ c → β' ≤ c := fun c hc hbc =>
      Finset.min'_le _ c (Finset.mem_filter.mpr ⟨hc, hbc⟩)
    have hcum0 : ∀ j, cum x j 0 = 0 := by intro j; simp [cum]
    have hx' := hx
    unfold LP1Feasible at hx'
    have hcumM : ∀ j, cum x j M = 1 := hx'.1
    have hδ : (1 : ℝ) ≤ (delta I : ℝ) := by
      have : 1 ≤ delta I := le_max_left _ _
      exact_mod_cast this
    have hδpos : (0 : ℝ) < (delta I : ℝ) := by linarith
    -- membership of candidate values
    have hcandA : ∀ a t, 1 ≤ t → t ≤ M → 0 < (delta I : ℝ) * cum x (Sum.inl a) t →
        (delta I : ℝ) * cum x (Sum.inl a) t ≤ 1 → (delta I : ℝ) * cum x (Sum.inl a) t ∈ C := by
      intro a t ht1 ht2 hv0 hv1
      rw [hC]; unfold cand
      apply Finset.mem_insert_of_mem
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(a, t), ?_, rfl⟩), hv0, hv1⟩
      rw [Finset.mem_product, Finset.mem_Icc]
      exact ⟨Finset.mem_univ _, ht1, ht2⟩
    have hcandB : ∀ b t, 1 ≤ t → t ≤ M → 0 < cum x (Sum.inr b) t →
        cum x (Sum.inr b) t ≤ 1 → cum x (Sum.inr b) t ∈ C := by
      intro b t ht1 ht2 hv0 hv1
      rw [hC]; unfold cand
      apply Finset.mem_insert_of_mem
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(b, t), ?_, rfl⟩), hv0, hv1⟩
      rw [Finset.mem_product, Finset.mem_Icc]
      exact ⟨Finset.mem_univ _, ht1, ht2⟩
    funext j
    cases j with
    | inl a =>
      show alphaPoint x (Sum.inl a) (β' / (delta I : ℝ)) = alphaPoint x (Sum.inl a) (β / (delta I : ℝ))
      unfold alphaPoint
      apply sInf_eq_of _ _ M
      · show β' / (delta I : ℝ) ≤ cum x (Sum.inl a) M
        rw [hcumM, div_le_one hδpos]; linarith
      · show β / (delta I : ℝ) ≤ cum x (Sum.inl a) M
        rw [hcumM, div_le_one hδpos]; linarith
      · intro t ht
        show β' / (delta I : ℝ) ≤ cum x (Sum.inl a) t ↔ β / (delta I : ℝ) ≤ cum x (Sum.inl a) t
        rw [div_le_iff₀ hδpos, div_le_iff₀ hδpos]
        constructor
        · intro h; linarith
        · intro h
          have hc : (delta I : ℝ) * cum x (Sum.inl a) t = cum x (Sum.inl a) t * (delta I : ℝ) :=
            mul_comm _ _
          rcases Nat.eq_zero_or_pos t with ht0 | ht0
          · rw [ht0, hcum0] at h; linarith
          · by_cases hv : (delta I : ℝ) * cum x (Sum.inl a) t ≤ 1
            · have := hmin _ (hcandA a t ht0 ht (by linarith) hv) (by linarith)
              linarith
            · push_neg at hv; linarith
    | inr b =>
      show alphaPoint x (Sum.inr b) β' = alphaPoint x (Sum.inr b) β
      unfold alphaPoint
      apply sInf_eq_of _ _ M
      · show β' ≤ cum x (Sum.inr b) M
        rw [hcumM]; linarith
      · show β ≤ cum x (Sum.inr b) M
        rw [hcumM]; linarith
      · intro t ht
        show β' ≤ cum x (Sum.inr b) t ↔ β ≤ cum x (Sum.inr b) t
        constructor
        · intro h; linarith
        · intro h
          rcases Nat.eq_zero_or_pos t with ht0 | ht0
          · rw [ht0, hcum0] at h; linarith
          · by_cases hv : cum x (Sum.inr b) t ≤ 1
            · exact hmin _ (hcandB b t ht0 ht (by linarith) hv) h
            · push_neg at hv; linarith
