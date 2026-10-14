-- Prove2me | solution 1 for ActuarialAnnuities.increasing_decreasing_balance
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:00:00.996827+00:00
-- url     : https://prove2.me/submissions/4da1cf66-03be-413a-8bc2-9be4fccffe7f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bIncreasing
import Definitions.Def_actuarial_bDecreasing
open ActuarialAnnuities

theorem solution(a n j : ℕ) (ha : a ≤ j) (hj : j < a+n) : bIncreasing a j+bDecreasing a n j = (n+1 : ℕ) := by
  unfold bIncreasing bDecreasing
  have e : j - a + 1 + (n - (j - a)) = n + 1 := by omega
  rw [<- Nat.cast_add, e]
