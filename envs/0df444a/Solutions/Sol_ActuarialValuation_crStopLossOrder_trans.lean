-- Prove2me | solution 1 for ActuarialValuation.crStopLossOrder_trans
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:57:52.005225+00:00
-- url     : https://prove2.me/submissions/74b838ae-50fc-4c48-a4e5-727f4d27dbfb

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLossOrdered

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p X Y Z : Fin n→ℝ) (hXY : crStopLossOrdered p X Y) (hYZ : crStopLossOrdered p Y Z) : crStopLossOrdered p X Z := by
  unfold crStopLossOrdered at *
  intro d
  exact (hXY d).trans (hYZ d)
