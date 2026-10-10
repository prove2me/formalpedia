-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceCohortCause_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:22:12.024624+00:00
-- url     : https://prove2.me/submissions/40ac37b3-add8-4e68-a518-ddbbea0040aa

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceCohortCause
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (d : ℕ → ℕ → ℝ) (t j : ℕ) (h0 : 0 < l 0) (hd : 0 ≤ d t j) : 0 ≤ cm1ServiceCohortCause l d t j := by
  unfold cm1ServiceCohortCause
  exact div_nonneg hd (le_of_lt h0)
