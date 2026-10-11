-- Prove2me | solution 1 for ActuarialValuation.scrPortfolioTotal_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:09:36.893984+00:00
-- url     : https://prove2.me/submissions/1e9cac3a-855a-431a-aaf1-1fee8c836223

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPortfolioTotal
open ActuarialValuation

theorem solution(c : ℕ → ℝ) : scrPortfolioTotal c 0 = 0 := by
  simp [scrPortfolioTotal]
