-- Prove2me | solution 1 for ActuarialValuation.whFirstRoughness_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:36:49.013885+00:00
-- url     : https://prove2.me/submissions/ea5460d3-b10d-4c70-b151-9dce2c0a010c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFirstRoughness
import Definitions.Def_actuarial_whShiftedCurve
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g : ℕ → ℝ) (n : ℕ) (s : ℝ) : whFirstRoughness (fun i => whShiftedCurve g s i) n = whFirstRoughness g n := by
  unfold whFirstRoughness
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [whFirstDifference, whShiftedCurve]
  ring
