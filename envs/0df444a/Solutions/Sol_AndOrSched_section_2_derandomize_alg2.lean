-- Prove2me | solution 1 for AndOrSched.section_2_derandomize_alg2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:52:07.144854+00:00
-- url     : https://prove2.me/submissions/fe23bf44-2175-4dcf-bd66-2076f77c02c5

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_LP5Feasible
import Definitions.Def_AndOrSched_horizon
import Definitions.Def_AndOrSched_numIntervals
import Definitions.Def_AndOrSched_key
import Definitions.Def_AndOrSched_cand
open scoped Classical NNReal

open AndOrSched in
theorem solution (I : Instance) (ε' : ℝ) (hε' : 0 < ε')
    (x : I.N → ℕ → ℝ) (hx : LP5Feasible I ε' x) :
    (∀ β ∈ cand I x (numIntervals I ε'), 0 < β ∧ β ≤ 1) ∧
    (cand I x (numIntervals I ε')).card ≤ Fintype.card I.N * numIntervals I ε' + 1 ∧
    (1 ≤ horizon I →
      (numIntervals I ε' : ℝ) ≤ 2 + (1 + ε') * Real.log (horizon I) / ε') ∧
    ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ β' ∈ cand I x (numIntervals I ε'), key I x β' = key I x β := by
  obtain ⟨L, hL⟩ : ∃ L, L = numIntervals I ε' := ⟨_, rfl⟩
  have hcL : ∀ j, cum x j L = 1 := fun j => by rw [hL]; exact hx.1 j
  have hnn : ∀ j s, 1 ≤ s → s ≤ L → 0 ≤ x j s := fun j s h1 h2 =>
    (hx.2.2.2.2 j s (by rw [Finset.mem_Icc, ← hL]; exact ⟨h1, h2⟩)).1
  have hmono : ∀ j (a c : ℕ), a ≤ c → c ≤ L → cum x j a ≤ cum x j c := by
    intro j a c hac hcL'
    unfold cum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      simp only [Finset.mem_Icc] at hs ⊢
      omega
    · intro s hs _
      simp only [Finset.mem_Icc] at hs
      exact hnn j s hs.1 (by omega)
  have hc0 : ∀ j, cum x j 0 = 0 := fun j => by simp [cum]
  have halpha_le : ∀ j (γ : ℝ), γ ≤ 1 → alphaPoint x j γ ≤ L := by
    intro j γ hγ
    unfold alphaPoint
    apply Nat.sInf_le
    show γ ≤ cum x j L
    rw [hcL j]; exact hγ
  have halpha_mem : ∀ j (γ : ℝ), γ ≤ 1 → γ ≤ cum x j (alphaPoint x j γ) := by
    intro j γ hγ
    unfold alphaPoint
    have hne : ({t : ℕ | γ ≤ cum x j t} : Set ℕ).Nonempty := ⟨L, by
      show γ ≤ cum x j L
      rw [hcL j]; exact hγ⟩
    exact Nat.sInf_mem hne
  have halpha_pos : ∀ j (γ : ℝ), 0 < γ → γ ≤ 1 → 1 ≤ alphaPoint x j γ := by
    intro j γ h0 h1
    by_contra hcon
    have hz : alphaPoint x j γ = 0 := by omega
    have := halpha_mem j γ h1
    rw [hz, hc0] at this
    linarith
  -- equality of alpha points
  have halpha_eq : ∀ j (γ₁ γ₂ : ℝ), γ₁ ≤ γ₂ → γ₂ ≤ 1 →
      γ₂ ≤ cum x j (alphaPoint x j γ₁) → alphaPoint x j γ₂ = alphaPoint x j γ₁ := by
    intro j γ₁ γ₂ h12 h2 h
    apply le_antisymm
    · unfold alphaPoint at h ⊢
      exact Nat.sInf_le h
    · have hm := halpha_mem j γ₂ h2
      unfold alphaPoint at hm ⊢
      apply Nat.sInf_le
      show γ₁ ≤ cum x j _
      exact le_trans h12 hm
  have hδ : (1 : ℝ) ≤ (delta I : ℝ) := by
    have : 1 ≤ delta I := by unfold delta; exact le_max_left _ _
    exact_mod_cast this
  have hδpos : (0 : ℝ) < (delta I : ℝ) := by linarith
  rw [← hL]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- part 1
    intro β hβ
    unfold cand at hβ
    rw [Finset.mem_insert] at hβ
    rcases hβ with h | h
    · rw [h]; exact ⟨one_pos, le_rfl⟩
    · exact (Finset.mem_filter.mp h).2
  · -- part 2
    unfold cand
    refine (Finset.card_insert_le _ _).trans ?_
    apply Nat.add_le_add_right
    refine (Finset.card_filter_le _ _).trans ?_
    refine (Finset.card_union_le _ _).trans ?_
    have hA := Finset.card_image_le (s := (Finset.univ : Finset I.A) ×ˢ Finset.Icc 1 L)
      (f := fun q : I.A × ℕ => (delta I : ℝ) * cum x (Sum.inl q.1) q.2)
    have hB := Finset.card_image_le (s := (Finset.univ : Finset I.B) ×ˢ Finset.Icc 1 L)
      (f := fun q : I.B × ℕ => cum x (Sum.inr q.1) q.2)
    rw [Finset.card_product, Finset.card_univ, Nat.card_Icc, Nat.add_sub_cancel] at hA hB
    have hN : Fintype.card I.N = Fintype.card I.A + Fintype.card I.B := by
      first
        | exact Fintype.card_sum
        | simp [Instance.N, Fintype.card_sum]
    rw [hN, add_mul]
    linarith
  · -- part 3
    intro hT1
    have hT : (1 : ℝ) ≤ (horizon I : ℝ) := by exact_mod_cast hT1
    have hlogT : 0 ≤ Real.log (horizon I : ℝ) := Real.log_nonneg hT
    have hl1 : ε' / (1 + ε') ≤ Real.log (1 + ε') := by
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + ε' by linarith)
      have e : ε' / (1 + ε') = 1 - (1 + ε')⁻¹ := by
        rw [div_eq_iff (by linarith), sub_mul, inv_mul_cancel₀ (by linarith)]
        ring
      rw [e]; exact h
    have hlpos : 0 < Real.log (1 + ε') := Real.log_pos (by linarith)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈Real.log (horizon I : ℝ) / Real.log (1 + ε')⌉₊ := ⟨_, rfl⟩
    have hn1 : Real.log (horizon I : ℝ) / Real.log (1 + ε') ≤ n := by
      rw [hn]; exact Nat.le_ceil _
    have hn2 : (n : ℝ) < Real.log (horizon I : ℝ) / Real.log (1 + ε') + 1 := by
      rw [hn]; exact Nat.ceil_lt_add_one (div_nonneg hlogT hlpos.le)
    have hmem : (horizon I : ℝ) ≤ (1 + ε') ^ n := by
      rw [← Real.log_le_log_iff (show (0 : ℝ) < (horizon I : ℝ) by linarith)
        (pow_pos (show (0 : ℝ) < 1 + ε' by linarith) n), Real.log_pow]
      rwa [div_le_iff₀ hlpos] at hn1
    have hLle : L ≤ n + 1 := by
      rw [hL]
      unfold numIntervals
      apply Nat.sInf_le
      show 1 ≤ n + 1 ∧ (horizon I : ℝ) ≤ (1 + ε') ^ (n + 1 - 1)
      refine ⟨by omega, ?_⟩
      rw [Nat.add_sub_cancel]
      exact hmem
    have hdiv : Real.log (horizon I : ℝ) / Real.log (1 + ε') ≤
        (1 + ε') * Real.log (horizon I : ℝ) / ε' := by
      calc Real.log (horizon I : ℝ) / Real.log (1 + ε')
          ≤ Real.log (horizon I : ℝ) / (ε' / (1 + ε')) :=
            div_le_div_of_nonneg_left hlogT (div_pos hε' (by linarith)) hl1
        _ = (1 + ε') * Real.log (horizon I : ℝ) / ε' := by
            rw [div_div_eq_mul_div]; ring
    have hLr : (L : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hLle
    linarith
  · -- part 4
    intro β hβ0 hβ1
    have hne : ((cand I x L).filter (fun c => β ≤ c)).Nonempty := by
      refine ⟨1, Finset.mem_filter.mpr ⟨?_, hβ1⟩⟩
      unfold cand
      exact Finset.mem_insert_self _ _
    obtain ⟨β', hβ'⟩ : ∃ β', β' = ((cand I x L).filter (fun c => β ≤ c)).min' hne := ⟨_, rfl⟩
    have hβ'mem : β' ∈ (cand I x L).filter (fun c => β ≤ c) := by
      rw [hβ']; exact Finset.min'_mem _ _
    rw [Finset.mem_filter] at hβ'mem
    have hβ'min : ∀ c ∈ cand I x L, β ≤ c → β' ≤ c := by
      intro c hc hβc
      rw [hβ']
      exact Finset.min'_le _ c (Finset.mem_filter.mpr ⟨hc, hβc⟩)
    have hβ'1 : β' ≤ 1 := by
      refine hβ'min 1 ?_ hβ1
      unfold cand
      exact Finset.mem_insert_self _ _
    have hββ' : β ≤ β' := hβ'mem.2
    refine ⟨β', hβ'mem.1, ?_⟩
    funext j
    cases j with
    | inl a =>
      show alphaPoint x (Sum.inl a) (β' / (delta I : ℝ)) =
        alphaPoint x (Sum.inl a) (β / (delta I : ℝ))
      have hb1 : β / (delta I : ℝ) ≤ 1 := by
        rw [div_le_iff₀ hδpos]; nlinarith
      have hb'1 : β' / (delta I : ℝ) ≤ 1 := by
        rw [div_le_iff₀ hδpos]; nlinarith
      have hb0 : 0 < β / (delta I : ℝ) := div_pos hβ0 hδpos
      obtain ⟨t, ht⟩ : ∃ t, t = alphaPoint x (Sum.inl a) (β / (delta I : ℝ)) := ⟨_, rfl⟩
      have htL : t ≤ L := by rw [ht]; exact halpha_le _ _ hb1
      have ht1 : 1 ≤ t := by rw [ht]; exact halpha_pos _ _ hb0 hb1
      have htm : β / (delta I : ℝ) ≤ cum x (Sum.inl a) t := by
        rw [ht]; exact halpha_mem _ _ hb1
      apply halpha_eq _ _ _ (div_le_div_of_nonneg_right hββ' hδpos.le) hb'1
      rw [← ht]
      -- c := δ * cum
      have hcβ : β ≤ (delta I : ℝ) * cum x (Sum.inl a) t := by
        rw [div_le_iff₀ hδpos] at htm; linarith
      have hc : β' ≤ (delta I : ℝ) * cum x (Sum.inl a) t := by
        by_cases hc1 : (delta I : ℝ) * cum x (Sum.inl a) t ≤ 1
        · refine hβ'min _ ?_ hcβ
          unfold cand
          apply Finset.mem_insert_of_mem
          rw [Finset.mem_filter]
          refine ⟨?_, by linarith, hc1⟩
          apply Finset.mem_union_left
          rw [Finset.mem_image]
          refine ⟨(a, t), ?_, rfl⟩
          simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
          exact ⟨ht1, htL⟩
        · push_neg at hc1; linarith
      rw [div_le_iff₀ hδpos]; linarith
    | inr b =>
      show alphaPoint x (Sum.inr b) β' = alphaPoint x (Sum.inr b) β
      obtain ⟨t, ht⟩ : ∃ t, t = alphaPoint x (Sum.inr b) β := ⟨_, rfl⟩
      have htL : t ≤ L := by rw [ht]; exact halpha_le _ _ hβ1
      have ht1 : 1 ≤ t := by rw [ht]; exact halpha_pos _ _ hβ0 hβ1
      have htm : β ≤ cum x (Sum.inr b) t := by
        rw [ht]; exact halpha_mem _ _ hβ1
      have hc1 : cum x (Sum.inr b) t ≤ 1 := by
        rw [← hcL (Sum.inr b)]; exact hmono _ _ _ htL le_rfl
      apply halpha_eq _ _ _ hββ' hβ'1
      rw [← ht]
      refine hβ'min _ ?_ htm
      unfold cand
      apply Finset.mem_insert_of_mem
      rw [Finset.mem_filter]
      refine ⟨?_, by linarith, hc1⟩
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨(b, t), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
      exact ⟨ht1, htL⟩
