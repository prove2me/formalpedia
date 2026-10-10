-- Prove2me | solution 1 for ActuarialValuation.cm1FinalSalaryPension_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:44:24.967422+00:00
-- url     : https://prove2.me/submissions/0327d304-887b-41c7-99fc-c2ae89b67577

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1FinalSalaryPension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary : ℕ → ℝ) (n : ℕ) (accrual : ℝ)
    (ha : 0 ≤ accrual) (hs : 0 ≤ salary n) :
    0 ≤ cm1FinalSalaryPension salary n accrual := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  simp only [cm1FinalSalaryPension]
  exact mul_nonneg (mul_nonneg hn ha) hs
