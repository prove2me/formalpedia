-- Prove2me | solution 1 for ActuarialValuation.retentionExcessPositive_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:56:40.819562+00:00
-- url     : https://prove2.me/submissions/e7c19b6c-7a90-46c0-a4af-52d161eb2d6a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionExcessPositive
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (x a b : ℝ) (h : a ≤ b) :
  retentionExcessPositive x a ≤
    retentionExcessPositive x b + (b - a) := by
  unfold retentionExcessPositive
  apply max_le
  · have hleft := le_max_left (x - b) (0 : ℝ)
    linarith
  · have hright := le_max_right (x - b) (0 : ℝ)
    linarith
