-- Prove2me | solution 1 for ActuarialValuation.alterationSurrenderValue_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:06:15.650777+00:00
-- url     : https://prove2.me/submissions/f1ca8fb9-7962-45fc-8553-3c1323b13a64

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationSurrenderValue
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (V c : ℝ) (hc : c ≤ V) : 0 ≤ alterationSurrenderValue V c := by
  unfold alterationSurrenderValue
  linarith
