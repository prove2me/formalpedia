-- Prove2me | solution 1 for ActuarialValuation.pen9DCFund_zero_rate
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:37:07.32598+00:00
-- url     : https://prove2.me/submissions/2777cbc1-6ea3-4827-92ff-99190c472db1

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9DCFund
open ActuarialValuation

theorem solution(s : ℕ → ℝ) (j : ℝ) (n : ℕ) : pen9DCFund 0 s j n = 0 := by
  simp [pen9DCFund]
