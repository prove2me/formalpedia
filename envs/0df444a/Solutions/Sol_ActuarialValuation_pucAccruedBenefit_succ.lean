-- Prove2me | solution 1 for ActuarialValuation.pucAccruedBenefit_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:05:33.739702+00:00
-- url     : https://prove2.me/submissions/d3fb4344-5457-4700-9612-99b1411748b1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucAccruedBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u : ℕ → ℝ) (n : ℕ) : pucAccruedBenefit u (n+1) = pucAccruedBenefit u n + u n := by
  simp only [pucAccruedBenefit, Finset.sum_range_succ]
