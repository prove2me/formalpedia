-- Prove2me | solution 1 for ActuarialValuation.cm1DCFund_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:03:31.922149+00:00
-- url     : https://prove2.me/submissions/ce9aae2d-19ac-46ff-b421-5dde3dc79b40

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AccumulatedSalaryBase
import Definitions.Def_actuarial_cm1DCFund

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary growth : ℕ → ℝ) (n : ℕ) (c : ℝ)
    (hc : 0 ≤ c) (hF : 0 ≤ cm1AccumulatedSalaryBase salary growth n) :
    0 ≤ cm1DCFund salary growth n c := by
  simp only [cm1DCFund]
  exact mul_nonneg hc hF
