-- Prove2me | solution 1 for ActuarialValuation.cm1AccruedCARE_unit_revaluation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:19:49.884448+00:00
-- url     : https://prove2.me/submissions/7dbd8c3f-80ba-4b6f-ba58-907aaf2cd0a3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CareerSalarySum
import Definitions.Def_actuarial_cm1AccruedCARE

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary : ℕ → ℝ) (n : ℕ) (a : ℝ) :
    cm1AccruedCARE salary (fun _ => 1) n a =
      a * cm1CareerSalarySum salary n := by
  simp [cm1AccruedCARE, cm1CareerSalarySum]
