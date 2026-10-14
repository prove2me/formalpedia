-- Prove2me | solution 1 for ActuarialValuation.ratIndicatedBase_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:53.518994+00:00
-- url     : https://prove2.me/submissions/26e0c47f-ade5-4878-a256-933499d5aab9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratIndicatedBase

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (target w : ℝ) (hw : w ≠ 0) : ratIndicatedBase target w * w = target := by
  unfold ratIndicatedBase
  exact div_mul_cancel₀ target hw
