-- Prove2me | solution 1 for ActuarialValuation.ratIndicatedBase_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:12:46.404976+00:00
-- url     : https://prove2.me/submissions/6c21a2a7-3aa7-46be-8430-626be66517d0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratIndicatedBase

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (target w : ℝ) (ht : 0 ≤ target) (hw : 0 < w) : 0 ≤ ratIndicatedBase target w := by
  unfold ratIndicatedBase
  exact div_nonneg ht (le_of_lt hw)
