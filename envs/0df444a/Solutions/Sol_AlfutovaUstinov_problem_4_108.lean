-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_108
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:44:54.182225+00:00
-- url     : https://prove2.me/submissions/8939fc93-8112-465f-9b21-37e2c90a2acd

import Mathlib


theorem solution (n : ℕ) :
    (7 ∣ 10 ^ n - 1 ↔ 6 ∣ n) ∧ (13 ∣ 10 ^ n - 1 ↔ 6 ∣ n) ∧
      (91 ∣ 10 ^ n - 1 ↔ 6 ∣ n) ∧ (819 ∣ 10 ^ n - 1 ↔ 6 ∣ n) := by
  have hpow : 1 ≤ 10 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hred : ∀ d : ℕ, 10 ^ 6 ≡ 1 [MOD d] → 10 ^ n ≡ 10 ^ (n % 6) [MOD d] := by
    intro d hd
    have h := (hd.pow (n / 6)).mul_right (10 ^ (n % 6))
    rw [one_pow, one_mul, ← pow_mul, ← pow_add, Nat.div_add_mod] at h
    exact h
  have main : ∀ d : ℕ, 10 ^ 6 ≡ 1 [MOD d] → (∀ r < 6, (1 ≡ 10 ^ r [MOD d] ↔ r = 0)) →
      (d ∣ 10 ^ n - 1 ↔ 6 ∣ n) := by
    intro d hd hr
    have hlt : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
    rw [← Nat.modEq_iff_dvd' hpow]
    constructor
    · intro h
      exact Nat.dvd_of_mod_eq_zero ((hr _ hlt).1 (h.trans (hred d hd)))
    · intro h
      exact ((hr _ hlt).2 (Nat.mod_eq_zero_of_dvd h)).trans (hred d hd).symm
  refine ⟨main 7 (by decide) ?_, main 13 (by decide) ?_, main 91 (by decide) ?_,
    main 819 (by decide) ?_⟩ <;> intro r hr <;> interval_cases r <;> decide
