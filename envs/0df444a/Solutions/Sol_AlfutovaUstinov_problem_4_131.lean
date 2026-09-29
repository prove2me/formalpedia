-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_131
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:36.283327+00:00
-- url     : https://prove2.me/submissions/79ea6037-27ae-4e31-8eaf-7939297e5ef2

import Mathlib


theorem solution :
    (∀ p : ℕ, p.Prime → 5 < p →
        (∃ x : ℤ, x ^ 4 + x ^ 3 + x ^ 2 + x + 1 ≡ 0 [ZMOD p]) → p ≡ 1 [MOD 5]) ∧
      {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = 5 * n + 1}.Infinite := by
  constructor
  · rintro p hp hp5 ⟨x, hx⟩
    have := Fact.mk hp
    have hy : (x : ZMod p) ^ 4 + (x : ZMod p) ^ 3 + (x : ZMod p) ^ 2 + (x : ZMod p) + 1 = 0 := by
      have h := (ZMod.intCast_eq_intCast_iff _ _ p).2 hx
      push_cast at h
      exact h
    set y : ZMod p := (x : ZMod p) with hydef
    have hy5 : y ^ 5 = 1 := by linear_combination (y - 1) * hy
    have hy1 : y ≠ 1 := by
      intro h1
      rw [h1] at hy
      have h5 : ((5 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hy
      rw [ZMod.natCast_eq_zero_iff] at h5
      have := Nat.le_of_dvd (by norm_num) h5
      omega
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0] at hy5
      norm_num at hy5
    have hord : orderOf y = 5 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 (orderOf_dvd_of_pow_eq_one hy5) with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hy1
      · exact h
    have h5dvd : 5 ∣ p - 1 := by
      rw [← hord]; exact ZMod.orderOf_dvd_card_sub_one hy0
    unfold Nat.ModEq
    omega
  · refine (Nat.infinite_setOfPred_prime_modEq_one (by norm_num : (5 : ℕ) ≠ 0)).mono ?_
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨hpp, hm⟩ := hp
    refine ⟨hpp, p / 5, ?_⟩
    unfold Nat.ModEq at hm
    omega
