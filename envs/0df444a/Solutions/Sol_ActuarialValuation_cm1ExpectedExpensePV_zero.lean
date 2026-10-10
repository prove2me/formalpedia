-- Prove2me | solution 1 for ActuarialValuation.cm1ExpectedExpensePV_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:16:57.747499+00:00
-- url     : https://prove2.me/submissions/1d717cf8-5adc-4b44-876d-dd6b620f29f1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ExpectedExpensePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (e d p : ℕ → ℝ) : cm1ExpectedExpensePV e d p 0 = 0 := by
  simp [cm1ExpectedExpensePV]
