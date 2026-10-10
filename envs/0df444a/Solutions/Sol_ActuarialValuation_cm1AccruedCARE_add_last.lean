-- Prove2me | solution 1 for ActuarialValuation.cm1AccruedCARE_add_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:08:50.114978+00:00
-- url     : https://prove2.me/submissions/72a1ac8a-030d-46d1-8a3b-7d51a64fbf22

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AccruedCARE

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary revalue : ℕ → ℝ) (n : ℕ) (a : ℝ) :
    cm1AccruedCARE salary revalue (n + 1) a =
      cm1AccruedCARE salary revalue n a + a * salary n * revalue n := by
  simp only [cm1AccruedCARE, Finset.sum_range_succ]
  rw [mul_add, mul_assoc]
