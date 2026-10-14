-- Prove2me | solution 1 for ActuarialValuation.pvPortfolioMean_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:57:17.701312+00:00
-- url     : https://prove2.me/submissions/4dc76f86-c930-40a1-b631-d485896eb586

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvPortfolioMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (means : ℕ → ℝ) (n : ℕ) : pvPortfolioMean means (n+1) = pvPortfolioMean means n + means n := by
  simp only [pvPortfolioMean, Finset.sum_range_succ]
