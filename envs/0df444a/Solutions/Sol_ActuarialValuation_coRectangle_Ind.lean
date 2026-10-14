-- Prove2me | solution 1 for ActuarialValuation.coRectangle_Ind
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:26:35.269508+00:00
-- url     : https://prove2.me/submissions/58a9903b-084e-4960-9c3e-fd042348bfc6

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coInd
import Definitions.Def_actuarial_coRectangle

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u1 u2 v1 v2 : ℝ) : coRectangle coInd u1 u2 v1 v2=(u2-u1)*(v2-v1) := by
  unfold coRectangle coInd
  ring
