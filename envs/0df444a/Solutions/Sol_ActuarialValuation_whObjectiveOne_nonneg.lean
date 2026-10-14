-- Prove2me | solution 1 for ActuarialValuation.whObjectiveOne_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:46:39.592811+00:00
-- url     : https://prove2.me/submissions/7c26e126-ba95-43d8-97d3-7aa424b6578e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_whObjectiveOne

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (fit smooth lambda : ℝ) (hf : 0 ≤ fit) (hs : 0 ≤ smooth) (hl : 0 ≤ lambda) : 0 ≤ whObjectiveOne fit smooth lambda := by
  have hmul : 0 ≤ lambda * smooth := mul_nonneg hl hs
  unfold whObjectiveOne
  nlinarith
