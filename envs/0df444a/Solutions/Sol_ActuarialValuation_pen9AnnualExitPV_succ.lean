-- Prove2me | solution 1 for ActuarialValuation.pen9AnnualExitPV_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:07:03.717208+00:00
-- url     : https://prove2.me/submissions/2b1fc564-6270-4573-9c36-6ab2d38af41f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9AnnualExitPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p v b : ℕ → ℝ) (n : ℕ) : pen9AnnualExitPV p v b (n+1) = pen9AnnualExitPV p v b n + p n*v n*b n := by
  simp only [pen9AnnualExitPV, Finset.sum_range_succ]
