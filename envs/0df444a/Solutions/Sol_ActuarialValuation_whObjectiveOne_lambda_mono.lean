-- Prove2me | solution 1 for ActuarialValuation.whObjectiveOne_lambda_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:45:32.45667+00:00
-- url     : https://prove2.me/submissions/924caebb-7c5f-48cb-b05f-010a0507a163

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_whObjectiveOne

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (fit smooth l1 l2 : ℝ) (hs : 0 ≤ smooth) (h : l1 ≤ l2) : whObjectiveOne fit smooth l1 ≤ whObjectiveOne fit smooth l2 := by
  have hmul : 0 ≤ smooth * (l2 - l1) :=
    mul_nonneg hs (sub_nonneg.mpr h)
  unfold whObjectiveOne
  nlinarith
