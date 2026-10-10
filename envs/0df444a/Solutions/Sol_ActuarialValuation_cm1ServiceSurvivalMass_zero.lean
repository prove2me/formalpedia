-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceSurvivalMass_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:29:16.484233+00:00
-- url     : https://prove2.me/submissions/5cb445f3-f6cb-40d1-b9bc-b6e0bd71fb72

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceSurvivalMass
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (h : l 0 ≠ 0) : cm1ServiceSurvivalMass l 0 = 1 := by
  change l 0 / l 0 = 1
  exact div_self h
