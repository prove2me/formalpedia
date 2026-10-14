-- Prove2me | solution 1 for ActuarialValuation.coUpper_tail_joint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:28:05.081526+00:00
-- url     : https://prove2.me/submissions/e6adb3b1-91c7-4af3-9f74-fd8ce780587c

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coUpper
import Definitions.Def_actuarial_coTailJoint

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u v : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (hv0 : 0≤v) (hv1 : v≤1) : coTailJoint coUpper u v=1-max u v := by
  unfold coTailJoint coUpper
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right h]
    ring
  · rw [min_eq_right h, max_eq_left h]
    ring
