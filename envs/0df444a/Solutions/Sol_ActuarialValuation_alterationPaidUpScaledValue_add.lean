-- Prove2me | solution 1 for ActuarialValuation.alterationPaidUpScaledValue_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:17:18.113663+00:00
-- url     : https://prove2.me/submissions/104a5cd5-b3b1-4e32-a3d5-1f5e14b77842

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationPaidUpScaledValue

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f g B : ℝ) : alterationPaidUpScaledValue (f+g) B = alterationPaidUpScaledValue f B + alterationPaidUpScaledValue g B := by
  unfold alterationPaidUpScaledValue
  ring
