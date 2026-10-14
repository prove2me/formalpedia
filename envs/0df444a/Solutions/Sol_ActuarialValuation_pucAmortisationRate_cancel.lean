-- Prove2me | solution 1 for ActuarialValuation.pucAmortisationRate_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:25:44.436404+00:00
-- url     : https://prove2.me/submissions/586d7432-ae3b-44d6-b17c-361448bd6ffc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Definitions.Def_actuarial_pucAmortisationRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u base : ℝ) (hb : base ≠ 0) : pucAmortisationRate u base * base = u := by
  unfold pucAmortisationRate
  field_simp [hb]
