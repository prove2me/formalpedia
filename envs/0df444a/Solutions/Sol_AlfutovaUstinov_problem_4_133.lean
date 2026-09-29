-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_133
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:41.852727+00:00
-- url     : https://prove2.me/submissions/c0ad3ff7-d413-4869-a0fb-20650b150977

import Mathlib


theorem solution (p : ℕ) (hp : p.Prime) (α : ℕ) :
    ∑ i ∈ Finset.range (α + 1), Nat.totient (p ^ i) = p ^ α := by
  conv_rhs => rw [← Nat.sum_totient (p ^ α)]
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  rfl
