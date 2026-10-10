-- Prove2me | solution 1 for ActuarialValuation.cm1Accum_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:11:31.08107+00:00
-- url     : https://prove2.me/submissions/96bd6c06-d553-4e74-b038-77cd9be3558d

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1Accum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) : cm1Accum i 1 = 1 + i := by
  simp [cm1Accum]
