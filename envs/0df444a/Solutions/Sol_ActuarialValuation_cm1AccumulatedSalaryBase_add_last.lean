-- Prove2me | solution 1 for ActuarialValuation.cm1AccumulatedSalaryBase_add_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:47:37.668389+00:00
-- url     : https://prove2.me/submissions/5010c5aa-53f6-4197-bb60-fe9015bc76cc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AccumulatedSalaryBase

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary growth : ℕ → ℝ) (n : ℕ) :
    cm1AccumulatedSalaryBase salary growth (n+1) =
      cm1AccumulatedSalaryBase salary growth n + salary n * growth n := by
  simp only [cm1AccumulatedSalaryBase, Finset.sum_range_succ]
