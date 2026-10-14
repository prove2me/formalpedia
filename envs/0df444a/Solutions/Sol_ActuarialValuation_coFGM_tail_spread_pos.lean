-- Prove2me | solution 1 for ActuarialValuation.coFGM_tail_spread_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:27:51.067142+00:00
-- url     : https://prove2.me/submissions/bbc86427-021c-4f6a-a813-21684eea0f7c

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coFGM
import Definitions.Def_actuarial_coThresholdSpread

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (theta u v : ℝ) (ht : 0≤theta) (hu0 : 0≤u) (hu1 : u≤1) (hv0 : 0≤v) (hv1 : v≤1) : 0≤coThresholdSpread (coFGM theta) u v := by
  have h : coThresholdSpread (coFGM theta) u v =
      theta*u*v*(1-u)*(1-v) := by
    unfold coThresholdSpread coTailJoint coFGM coInd
    ring
  rw [h]
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg ht hu0
      · exact hv0
    · exact sub_nonneg.mpr hu1
  · exact sub_nonneg.mpr hv1
