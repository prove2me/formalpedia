-- Prove2me | solution 1 for ActuarialValuation.tailShiftObjective_translation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:41:23.775549+00:00
-- url     : https://prove2.me/submissions/408cbfb6-0f46-4ca7-b356-0e9323b9cd0e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Definitions.Def_actuarial_tailCVaRObjective
import Definitions.Def_actuarial_tailShiftObjective

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n : ℕ) (a t s : ℝ) :
    tailShiftObjective p n a t s = tailCVaRObjective p n a t + s := by
  have hsum : (∑ k ∈ Finset.range (n+1), tailShiftExcess (k : ℝ) s t * p k)
      = ∑ k ∈ Finset.range (n+1), tailExcess (k : ℝ) t * p k := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    unfold tailShiftExcess tailExcess
    congr 1
    ring
  unfold tailShiftObjective tailCVaRObjective tailStopLoss
  rw [hsum]
  ring
