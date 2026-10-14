-- Prove2me | solution 1 for ActuarialValuation.coRectangle_add_u
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:27:00.119989+00:00
-- url     : https://prove2.me/submissions/fab45826-9ca0-4a56-bc2d-507f5fef5713

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coRectangle

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (C : ℝ → ℝ → ℝ) (u1 u2 u3 v1 v2 : ℝ) : coRectangle C u1 u3 v1 v2=coRectangle C u1 u2 v1 v2+coRectangle C u2 u3 v1 v2 := by
  unfold coRectangle
  ring
