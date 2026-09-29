-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_130
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:33.369988+00:00
-- url     : https://prove2.me/submissions/40ac96cd-7bda-448f-9b7d-7822b2e5050e

import Mathlib


theorem solution :
    (∀ p : ℕ, p.Prime → 3 < p → (∃ x : ℤ, x ^ 2 + x + 1 ≡ 0 [ZMOD p]) → p ≡ 1 [MOD 6]) ∧
      {p : ℕ | p.Prime ∧ ∃ k : ℕ, p = 6 * k + 1}.Infinite := by
  constructor
  · rintro p hp hp3 ⟨x, hx⟩
    have := Fact.mk hp
    have hy : (x : ZMod p) ^ 2 + (x : ZMod p) + 1 = 0 := by
      have h := (ZMod.intCast_eq_intCast_iff _ _ p).2 hx
      push_cast at h
      exact h
    set y : ZMod p := (x : ZMod p) with hydef
    have hy3 : y ^ 3 = 1 := by linear_combination (y - 1) * hy
    have hy1 : y ≠ 1 := by
      intro h1
      rw [h1] at hy
      have h3 : ((3 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hy
      rw [ZMod.natCast_eq_zero_iff] at h3
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0] at hy3
      norm_num at hy3
    have hord : orderOf y = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hy3) with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hy1
      · exact h
    have h3dvd : 3 ∣ p - 1 := by
      rw [← hord]; exact ZMod.orderOf_dvd_card_sub_one hy0
    have h2 : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two (by omega))
    unfold Nat.ModEq
    omega
  · refine (Nat.infinite_setOfPred_prime_modEq_one (by norm_num : (6 : ℕ) ≠ 0)).mono ?_
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨hpp, hm⟩ := hp
    refine ⟨hpp, p / 6, ?_⟩
    unfold Nat.ModEq at hm
    omega
