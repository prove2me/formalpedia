-- Prove2me | solution 1 for ActuarialValuation.scrPortfolioDiagonal_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:39:58.97634+00:00
-- url     : https://prove2.me/submissions/d81c5e57-41a5-4289-b9f4-82f2f50e310b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPortfolioDiagonal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (n : ℕ) : scrPortfolioDiagonal c (n+1) = scrPortfolioDiagonal c n + (c n)^2 := by
  simp only [scrPortfolioDiagonal, Finset.sum_range_succ]
