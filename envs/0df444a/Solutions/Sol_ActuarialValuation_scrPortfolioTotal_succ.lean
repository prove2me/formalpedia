-- Prove2me | solution 1 for ActuarialValuation.scrPortfolioTotal_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:40:12.773773+00:00
-- url     : https://prove2.me/submissions/2b6bfaf4-6bcf-43bf-8e12-5e546ae51c1a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPortfolioTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (n : ℕ) : scrPortfolioTotal c (n+1) = scrPortfolioTotal c n + c n := by
  simp only [scrPortfolioTotal, Finset.sum_range_succ]
