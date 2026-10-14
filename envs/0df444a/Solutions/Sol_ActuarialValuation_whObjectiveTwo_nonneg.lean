-- Prove2me | solution 1 for ActuarialValuation.whObjectiveTwo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:52:34.90812+00:00
-- url     : https://prove2.me/submissions/467476f9-68f3-45a2-aa4d-e5a0fb6692c4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whObjectiveTwo

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (fit smooth lambda : ℝ) (hf : 0 ≤ fit) (hs : 0 ≤ smooth) (hl : 0 ≤ lambda) : 0 ≤ whObjectiveTwo fit smooth lambda := by
  dsimp [whObjectiveTwo]
  exact add_nonneg hf (mul_nonneg hl hs)
