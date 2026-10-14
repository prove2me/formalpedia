-- Prove2me | solution 1 for ActuarialValuation.siIndependentVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T16:21:48.461697+00:00
-- url     : https://prove2.me/submissions/0bfb0c01-7338-4005-a396-c8bb2380f2eb

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siIndependentVariance
open ActuarialValuation

theorem solution(m s : ℝ) (hm : 0 ≤ m) (hs : m^2 ≤ s) (n : ℕ) : 0 ≤ siIndependentVariance m s n := by
  unfold siIndependentVariance
  rw [← pow_mul, mul_comm n 2, pow_mul]
  have h0 : 0 ≤ m ^ 2 := sq_nonneg m
  have := pow_le_pow_left₀ h0 hs n
  linarith
