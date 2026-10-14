-- Prove2me | solution 1 for ActuarialValuation.coTailJoint_monotone_u
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:29:14.085984+00:00
-- url     : https://prove2.me/submissions/c320221f-d248-417d-8903-7bf2977a325c

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coIsCopula
import Definitions.Def_actuarial_coTailJoint

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (C : ℝ → ℝ → ℝ) (hc : coIsCopula C) (u1 u2 v : ℝ) (hu1 : 0≤u1) (hu : u1≤u2) (hu2 : u2≤1) (hv : 0≤v) (hV : v≤1) : coTailJoint C u2 v≤coTailJoint C u1 v := by
  rcases hc with ⟨hm, hr⟩
  have hc0 := (hm u1 hu1 (le_trans hu hu2)).2.2.1
  have hc1 := (hm u2 (le_trans hu1 hu) hu2).2.2.1
  have hrect := hr u1 u2 v 1 hu1 hu hu2 hv hV le_rfl
  unfold coRectangle at hrect
  rw [hc0, hc1] at hrect
  unfold coTailJoint
  linarith
