-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceSurvivalMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:29:24.046135+00:00
-- url     : https://prove2.me/submissions/e950cd02-fda6-4214-ba87-224b45b06cc5

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

theorem solution (l : ℕ → ℝ) (t : ℕ) (h0 : 0 < l 0) (ht : 0 ≤ l t) : 0 ≤ cm1ServiceSurvivalMass l t := by
  change 0 ≤ l t / l 0
  exact div_nonneg ht (le_of_lt h0)
