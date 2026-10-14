-- Prove2me | solution 1 for ActuarialValuation.ratRateChange_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:30:16.434979+00:00
-- url     : https://prove2.me/submissions/22b8612a-229a-48af-857f-b6a139a979fc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratRateChange

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (old new : ℝ) (h : old ≠ 0) : (1 + ratRateChange new old) * old = new := by
  unfold ratRateChange
  have hrate : 1 + (new / old - 1) = new / old := by
    rw [← add_sub_assoc]
    exact add_sub_cancel_left 1 (new / old)
  calc
    (1 + (new / old - 1)) * old = (new / old) * old := by rw [hrate]
    _ = new := div_mul_cancel₀ new h
