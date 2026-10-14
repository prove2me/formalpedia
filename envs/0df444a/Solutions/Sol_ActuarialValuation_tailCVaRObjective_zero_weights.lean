-- Prove2me | solution 1 for ActuarialValuation.tailCVaRObjective_zero_weights
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:36:38.237932+00:00
-- url     : https://prove2.me/submissions/90570c6f-aff6-405c-a5a9-a667fd035bbe

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailCVaRObjective

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (n : ℕ) (a t : ℝ) :
    tailCVaRObjective (fun _ => (0 : ℝ)) n a t = t := by
  first
  | (unfold tailCVaRObjective tailStopLoss; simp)
  | (simp [tailCVaRObjective, tailStopLoss])
