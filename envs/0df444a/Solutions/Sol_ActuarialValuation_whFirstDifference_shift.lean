-- Prove2me | solution 1 for ActuarialValuation.whFirstDifference_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:23:07.250849+00:00
-- url     : https://prove2.me/submissions/07c9da50-e0a4-4eb8-9c1c-40aa09209500

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFirstDifference
import Definitions.Def_actuarial_whShiftedCurve
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g : ℕ → ℝ) (i : ℕ) (s : ℝ) : whFirstDifference (fun j => whShiftedCurve g s j) i = whFirstDifference g i := by
  simp only [whFirstDifference, whShiftedCurve]
  ring
