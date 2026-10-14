-- Prove2me | solution 1 for ActuarialValuation.ruPremiumTotal_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:18:50.79324+00:00
-- url     : https://prove2.me/submissions/f47b7352-8ccd-48fc-9674-2fb04ab8fdb8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPremiumTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rate : ℝ) (n : ℕ) :
    ruPremiumTotal rate (n+1) = ruPremiumTotal rate n + rate := by
  simp [ruPremiumTotal, Nat.cast_add, mul_add, add_mul]
