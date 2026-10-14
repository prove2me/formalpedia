-- Prove2me | solution 1 for ActuarialValuation.scrPortfolioQuadratic_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:39:44.271586+00:00
-- url     : https://prove2.me/submissions/bbc3a8f9-e4b6-4bd4-97c1-0fe1f4cd97d9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPortfolioQuadratic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (rho : ℕ → ℕ → ℝ) : scrPortfolioQuadratic c rho 0 = 0 := by
  simp [scrPortfolioQuadratic]
