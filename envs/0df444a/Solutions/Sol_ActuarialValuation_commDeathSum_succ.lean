-- Prove2me | solution 1 for ActuarialValuation.commDeathSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:12:25.451517+00:00
-- url     : https://prove2.me/submissions/08821a2a-c813-457d-9de1-2d673793a26c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedDeaths
import Definitions.Def_actuarial_commDeathSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : commDeathSum l v x (n+1) = commDeathSum l v x n + commDiscountedDeaths l v (x+n) := by
  simp only [commDeathSum, Finset.sum_range_succ]
