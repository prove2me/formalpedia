-- Prove2me | solution 1 for ActuarialValuation.pvPortfolioMean_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:57:06.702288+00:00
-- url     : https://prove2.me/submissions/27592e42-9365-4282-b41d-bfa6833afdf7

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvPortfolioMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (means : ℕ → ℝ) : pvPortfolioMean means 0 = 0 := by
  simp [pvPortfolioMean]
