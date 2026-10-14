-- Prove2me | solution 1 for ActuarialValuation.coRectangle_blend
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:27:23.634123+00:00
-- url     : https://prove2.me/submissions/10f49e09-5893-47c1-b563-f36e7fdb8e80

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coBlend
import Definitions.Def_actuarial_coRectangle

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (alpha : ℝ) (C D : ℝ → ℝ → ℝ) (u1 u2 v1 v2 : ℝ) : coRectangle (coBlend alpha C D) u1 u2 v1 v2=alpha*coRectangle C u1 u2 v1 v2+(1-alpha)*coRectangle D u1 u2 v1 v2 := by
  unfold coRectangle coBlend
  ring
