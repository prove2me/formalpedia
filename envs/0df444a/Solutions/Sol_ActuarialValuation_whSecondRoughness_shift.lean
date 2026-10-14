-- Prove2me | solution 1 for ActuarialValuation.whSecondRoughness_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T07:00:11.968701+00:00
-- url     : https://prove2.me/submissions/9576703d-09e4-4eb0-80b3-98da45e2eef0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_whSecondRoughness
import Definitions.Def_actuarial_whShiftedCurve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g : ℕ → ℝ) (n : ℕ) (s : ℝ) : whSecondRoughness (fun i => whShiftedCurve g s i) n = whSecondRoughness g n := by
  unfold whSecondRoughness
  apply Finset.sum_congr rfl
  intro i hi
  have hdiff : whSecondDifference (fun j => whShiftedCurve g s j) i =
      whSecondDifference g i := by
    unfold whSecondDifference whFirstDifference whShiftedCurve
    ring
  rw [hdiff]
