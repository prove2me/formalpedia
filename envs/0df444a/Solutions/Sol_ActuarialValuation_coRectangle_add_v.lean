-- Prove2me | solution 1 for ActuarialValuation.coRectangle_add_v
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:27:11.802996+00:00
-- url     : https://prove2.me/submissions/05d1cea2-8dac-476f-8a58-0697769e6ec3

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coRectangle

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (C : ℝ → ℝ → ℝ) (u1 u2 v1 v2 v3 : ℝ) : coRectangle C u1 u2 v1 v3=coRectangle C u1 u2 v1 v2+coRectangle C u1 u2 v2 v3 := by
  unfold coRectangle
  ring
