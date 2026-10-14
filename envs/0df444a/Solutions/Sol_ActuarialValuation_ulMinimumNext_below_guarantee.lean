-- Prove2me | solution 1 for ActuarialValuation.ulMinimumNext_below_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:23:17.638566+00:00
-- url     : https://prove2.me/submissions/db63d1c7-0123-4342-8f2b-c5970af2588f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulMinimumNext
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (earned mortality floor : ℝ) (h : earned≤floor) (hm0 : 0≤mortality) (hm1 : mortality<1) : ulMinimumNext earned mortality floor ≤ floor := by
  change (if earned ≤ floor then
    (earned - mortality * floor) / (1 - mortality) else earned) ≤ floor
  rw [if_pos h]
  have hden : 0 < 1 - mortality := by linarith
  apply (div_le_iff₀ hden).2
  nlinarith [h]
