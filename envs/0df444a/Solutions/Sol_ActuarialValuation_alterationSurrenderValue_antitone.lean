-- Prove2me | solution 1 for ActuarialValuation.alterationSurrenderValue_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:11:55.503022+00:00
-- url     : https://prove2.me/submissions/66e058af-15c5-4a80-8dcb-754a68b2339d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationSurrenderValue

import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (V c1 c2 : ℝ) (h : c1 ≤ c2) : alterationSurrenderValue V c2 ≤ alterationSurrenderValue V c1 := by
  unfold alterationSurrenderValue
  linarith
