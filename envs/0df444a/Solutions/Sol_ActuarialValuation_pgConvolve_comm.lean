-- Prove2me | solution 1 for ActuarialValuation.pgConvolve_comm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:36:15.306235+00:00
-- url     : https://prove2.me/submissions/27ce4c0d-f86b-48e0-9a74-aa44e405c61c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgConvolve
open ActuarialValuation

theorem solution(f g : ℕ → ℝ) (k : ℕ) : pgConvolve f g k=pgConvolve g f k := by
  unfold pgConvolve
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have e : k + 1 - 1 - j = k - j := by omega
  rw [e, Nat.sub_sub_self (by omega), mul_comm]
