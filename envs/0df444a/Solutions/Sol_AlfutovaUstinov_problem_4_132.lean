-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_132
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:39.059921+00:00
-- url     : https://prove2.me/submissions/c37cca73-9665-47fe-8579-48fc3aadab46

import Mathlib


theorem solution (p : ℕ) (hp : p.Prime) (α : ℕ) (hα : 0 < α) :
    Nat.totient 17 = 16 ∧ Nat.totient p = p - 1 ∧ Nat.totient (p ^ 2) = p * (p - 1) ∧
      Nat.totient (p ^ α) = p ^ (α - 1) * (p - 1) := by
  refine ⟨?_, Nat.totient_prime hp, ?_, Nat.totient_prime_pow hp hα⟩
  · rw [Nat.totient_prime (by norm_num : Nat.Prime 17)]
  · rw [Nat.totient_prime_pow hp (by norm_num : 0 < 2)]
    simp
