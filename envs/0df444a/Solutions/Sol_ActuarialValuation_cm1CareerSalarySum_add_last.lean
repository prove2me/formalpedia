-- Prove2me | solution 1 for ActuarialValuation.cm1CareerSalarySum_add_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:32:56.838477+00:00
-- url     : https://prove2.me/submissions/0262d16c-d799-43ce-945d-4f6d97c2c730

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CareerSalarySum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary : ℕ → ℝ) (n : ℕ) :
    cm1CareerSalarySum salary (n+1) =
      cm1CareerSalarySum salary n + salary n := by
  simp only [cm1CareerSalarySum, Finset.sum_range_succ]
