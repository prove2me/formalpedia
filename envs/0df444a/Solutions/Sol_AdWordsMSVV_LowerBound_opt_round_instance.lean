-- Prove2me | solution 1 for AdWordsMSVV.LowerBound.opt_round_instance
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:33:28.519505+00:00
-- url     : https://prove2.me/submissions/d0992fd8-39f7-4e0d-af12-dc876ff703d3

import Mathlib
import Definitions.Def_AdWordsMSVV_LowerBound_Setting
set_option autoImplicit false
open AdWordsMSVV.LowerBound Finset

theorem solution (N B : ℕ) (π : Equiv.Perm (Fin N)) :
    offlineRevenue B (roundInstance N B π) (roundAllocation N B π) = N * B ∧
    ∀ τ : Fin (N * B) → Option (Fin N), offlineRevenue B (roundInstance N B π) τ ≤ N * B := by
  classical
  constructor
  · rcases Nat.eq_zero_or_pos B with hB | hB
    · subst hB
      simp [offlineRevenue]
    · -- every bidder wins exactly the queries of its own round
      have hcard : ∀ r : Fin N,
          (univ.filter (fun t : Fin (N * B) =>
              roundAllocation N B π t = some r ∧ r ∈ roundInstance N B π t)).card = B := by
        intro r
        set i := (π.symm r).val with hi
        have hiN : i < N := (π.symm r).isLt
        have hS : (univ.filter (fun t : Fin (N * B) =>
              roundAllocation N B π t = some r ∧ r ∈ roundInstance N B π t)).map Fin.valEmbedding
            = Finset.Ico (i * B) (i * B + B) := by
          ext x
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
            Finset.mem_Ico]
          constructor
          · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
            have htN : t.val / B < N := by
              rw [Nat.div_lt_iff_lt_mul hB]; simpa [mul_comm] using t.isLt
            have h1' : π ⟨t.val / B, htN⟩ = r := by
              unfold roundAllocation at h1
              rw [dif_pos htN] at h1
              exact Option.some.inj h1
            have h3 : t.val / B = i := by
              have : (⟨t.val / B, htN⟩ : Fin N) = π.symm r := by
                rw [← h1']; simp
              rw [hi, ← this]
            have := Nat.div_add_mod t.val B
            have h4 := Nat.mod_lt t.val hB
            constructor
            · calc i * B = t.val / B * B := by rw [h3]
                _ ≤ t.val := Nat.div_mul_le_self _ _
            · calc t.val = B * (t.val / B) + t.val % B := this.symm
                _ < B * i + B := by rw [h3]; omega
                _ = i * B + B := by ring
          · rintro ⟨hlo, hhi⟩
            have hxN : x < N * B := by
              calc x < i * B + B := hhi
                _ = (i + 1) * B := by ring
                _ ≤ N * B := Nat.mul_le_mul_right _ hiN
            have hdiv : x / B = i := Nat.div_eq_of_lt_le hlo (by rw [add_mul, one_mul]; exact hhi)
            refine ⟨⟨x, hxN⟩, ⟨?_, ?_⟩, rfl⟩
            · unfold roundAllocation
              have hxi : x / B < N := by rw [hdiv]; exact hiN
              rw [dif_pos hxi]
              congr 1
              have : (⟨x / B, hxi⟩ : Fin N) = π.symm r := Fin.ext (hdiv.trans hi)
              rw [this]; simp
            · unfold roundInstance
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              show x / B ≤ (π.symm r).val
              rw [hdiv]
        have := congrArg Finset.card hS
        rw [Finset.card_map, Nat.card_Ico] at this
        simpa using this
      simp only [offlineRevenue, hcard, min_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul]
  · intro τ
    unfold offlineRevenue
    calc ∑ r, min B (univ.filter (fun t => τ t = some r ∧ r ∈ roundInstance N B π t)).card
        ≤ ∑ r, (univ.filter (fun t => τ t = some r ∧ r ∈ roundInstance N B π t)).card :=
          Finset.sum_le_sum fun r _ => min_le_right _ _
      _ = (univ.biUnion fun r => univ.filter (fun t => τ t = some r ∧ r ∈ roundInstance N B π t)).card := by
          rw [Finset.card_biUnion]
          intro r _ r' _ hrr
          show Disjoint _ _
          rw [Finset.disjoint_left]
          intro t h1 h2
          simp only [Finset.mem_filter] at h1 h2
          exact hrr (Option.some.inj (h1.2.1.symm.trans h2.2.1))
      _ ≤ N * B := by
          calc _ ≤ (univ : Finset (Fin (N * B))).card := Finset.card_le_univ _
            _ = N * B := by simp
