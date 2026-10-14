-- Prove2me | solution 1 for ActuarialValuation.pucFutureBenefit_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:07:02.534876+00:00
-- url     : https://prove2.me/submissions/65be7ee2-0114-4f55-974e-9f04121d275f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucFutureBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u : ℕ → ℝ) (n m : ℕ) : pucFutureBenefit u n (m+1) = pucFutureBenefit u n m + u (n+m) := by
  simp only [pucFutureBenefit, Finset.sum_range_succ]
