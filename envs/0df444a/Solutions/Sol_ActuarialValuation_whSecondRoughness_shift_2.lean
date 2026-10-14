-- Prove2me | solution 2 for ActuarialValuation.whSecondRoughness_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T07:00:29.958815+00:00
-- url     : https://prove2.me/submissions/89784150-8feb-4962-8bdf-19ae8ed557da

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSecondRoughness
import Definitions.Def_actuarial_whShiftedCurve
import Mathlib.Tactic.Ring

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
    dsimp [whSecondDifference, whFirstDifference, whShiftedCurve]
    ring
  rw [hdiff]
