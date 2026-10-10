-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceAnnualExit_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:27.773102+00:00
-- url     : https://prove2.me/submissions/265caa76-b102-4537-ba64-65a0a91739cd

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceAnnualExit
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (d : ℕ → ℕ → ℝ) (t : ℕ) : cm1ServiceAnnualExit d t 0 = 0 := by
  simp [cm1ServiceAnnualExit]
