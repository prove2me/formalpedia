-- Prove2me | solution 1 for ActuarialValuation.coRectangle_Ind_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:26:47.57187+00:00
-- url     : https://prove2.me/submissions/63a8c5a2-8cba-4642-a305-2005099d9a42

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

theorem solution (u1 u2 v1 v2 : ℝ) (hu : u1≤u2) (hv : v1≤v2) : 0≤coRectangle coInd u1 u2 v1 v2 := by
  have h : coRectangle coInd u1 u2 v1 v2 = (u2-u1)*(v2-v1) := by
    unfold coRectangle coInd
    ring
  rw [h]
  exact mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)
