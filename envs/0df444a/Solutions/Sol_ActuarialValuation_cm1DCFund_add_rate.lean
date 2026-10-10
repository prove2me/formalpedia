-- Prove2me | solution 1 for ActuarialValuation.cm1DCFund_add_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:39:09.250542+00:00
-- url     : https://prove2.me/submissions/7bc29e9e-76f3-42b5-8bc2-1b2577dcbddb

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1DCFund

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary growth : ℕ → ℝ) (n : ℕ) (a b : ℝ) :
    cm1DCFund salary growth n (a+b) =
      cm1DCFund salary growth n a + cm1DCFund salary growth n b := by
  simp [cm1DCFund, add_mul]
