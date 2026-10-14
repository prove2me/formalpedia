-- Prove2me | solution 1 for ActuarialValuation.pen9Salary_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:58:05.873981+00:00
-- url     : https://prove2.me/submissions/f9bfba60-cb60-4a28-b32d-17ae9d080756

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9Salary

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s growth : ℝ) (n : ℕ) (hs : 0 ≤ s) (hg : 0 ≤ 1+growth) : 0 ≤ pen9Salary s growth n := by
  unfold pen9Salary
  exact mul_nonneg hs (pow_nonneg hg n)
