-- Prove2me | solution 1 for ActuarialValuation.ratIndicatedBase_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:41:54.040434+00:00
-- url     : https://prove2.me/submissions/2f6fb4b1-9c1c-4c23-8df8-4be7592ff498

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratIndicatedBase

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (target w b : ℝ) (hw : w ≠ 0) (h : b * w = target) : b = ratIndicatedBase target w := by
  change b = target / w
  apply mul_right_cancel₀ hw
  calc
    b * w = target := h
    _ = (target / w) * w := (div_mul_cancel₀ target hw).symm
