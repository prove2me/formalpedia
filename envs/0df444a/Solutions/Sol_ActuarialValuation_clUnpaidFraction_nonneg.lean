-- Prove2me | solution 1 for ActuarialValuation.clUnpaidFraction_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:51:19.419219+00:00
-- url     : https://prove2.me/submissions/42133868-5e65-4f3d-bbf0-eabf62dfa3d3

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clUnpaidFraction
open ActuarialValuation

theorem solution(f : ℝ) (h : 1 ≤ f) : 0 ≤ clUnpaidFraction f := by
  unfold clUnpaidFraction clPaidFraction
  rw [sub_nonneg, div_le_one (by linarith)]
  exact h
