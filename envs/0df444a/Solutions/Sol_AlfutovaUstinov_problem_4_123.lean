-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_123
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:22.114983+00:00
-- url     : https://prove2.me/submissions/89be063f-d0e2-476f-9ecf-871ed7765749

import Mathlib


theorem solution (n : ℕ) (hn : ¬ 17 ∣ n) : 17 ∣ n ^ 8 + 1 ∨ 17 ∣ n ^ 8 - 1 := by
  have h := Nat.pow_mod n 8 17
  have hr : n % 17 ≠ 0 := fun h0 => hn (Nat.dvd_of_mod_eq_zero h0)
  have hlt : n % 17 < 17 := Nat.mod_lt _ (by norm_num)
  have key : n ^ 8 % 17 = 1 ∨ n ^ 8 % 17 = 16 := by
    rw [h]
    generalize n % 17 = r at hr hlt ⊢
    interval_cases r <;> first | omega | decide
  rcases key with h1 | h16
  · right; omega
  · left; omega
