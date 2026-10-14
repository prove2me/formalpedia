-- Prove2me | solution 1 for ActuarialValuation.alterationSurrenderValue_le_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:18:29.677329+00:00
-- url     : https://prove2.me/submissions/2ef55b47-99a3-4871-b7b1-7ea959044b36

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationSurrenderValue

import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (V c : ℝ) (hc : 0 ≤ c) : alterationSurrenderValue V c ≤ V := by
  unfold alterationSurrenderValue
  linarith
