-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_113
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:48.756999+00:00
-- url     : https://prove2.me/submissions/1e11c13b-c51a-4fc6-abdb-95c7f9becc13

import Mathlib


theorem solution (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 := by
  set R : ℕ → ℕ := fun k => Nat.ofDigits 10 (List.replicate k 1) with hR
  have Rpos : ∀ k, 0 < k → 0 < R k := by
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [hR, List.replicate_succ, Nat.ofDigits_cons]
    omega
  have Radd : ∀ a b, R (a + b) = R a + 10 ^ a * R b := by
    intro a b
    simp only [hR]
    rw [← List.replicate_append_replicate, Nat.ofDigits_append, List.length_replicate]
  have Rdig : ∀ k, Nat.digits 10 (R k) = List.replicate k 1 := by
    intro k
    simp only [hR]
    apply Nat.digits_ofDigits 10 (by norm_num)
    · intro l hl
      rw [List.eq_of_mem_replicate hl]; norm_num
    · intro h
      rw [List.eq_of_mem_replicate (List.getLast_mem h)]; norm_num
  have key : ∀ i j, i < j → R j % n = R i % n →
      ∃ m : ℕ, 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 := by
    intro i j hlt heq
    refine ⟨10 ^ i * R (j - i), ?_, ?_, ?_⟩
    · exact Nat.mul_pos (by positivity) (Rpos _ (by omega))
    · have h1 : R j = R i + 10 ^ i * R (j - i) := by
        rw [← Radd]; congr 1; omega
      have h2 : (R j - R i) % n = 0 := Nat.sub_mod_eq_zero_of_mod_eq heq
      rw [h1, Nat.add_sub_cancel_left] at h2
      exact Nat.dvd_of_mod_eq_zero h2
    · rw [Nat.digits_base_pow_mul (by norm_num) (Rpos _ (by omega)), Rdig]
      intro d hd
      rw [List.mem_append] at hd
      rcases hd with hd | hd
      · left; exact List.eq_of_mem_replicate hd
      · right; exact List.eq_of_mem_replicate hd
  have hmaps : ∀ k ∈ Finset.range (n + 1), (fun k => R k % n) k ∈ Finset.range n :=
    fun k _ => Finset.mem_range.2 (Nat.mod_lt _ hn)
  have hc : (Finset.range n).card < (Finset.range (n + 1)).card := by simp
  obtain ⟨i, _, j, _, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (f := fun k => R k % n) hc hmaps
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact key i j h heq.symm
  · exact key j i h heq
