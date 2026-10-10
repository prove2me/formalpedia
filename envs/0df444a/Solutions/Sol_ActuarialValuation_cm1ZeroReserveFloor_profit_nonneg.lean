-- Prove2me | solution 1 for ActuarialValuation.cm1ZeroReserveFloor_profit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:21:41.292041+00:00
-- url     : https://prove2.me/submissions/19cf4069-5f31-4c09-a136-dcea0011e7d1

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ZeroReserveFloor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c s g R : ℝ) (hg : 0 < g) : 0 ≤ c + g * cm1ZeroReserveFloor c s g R - s*R := by
  unfold cm1ZeroReserveFloor
  have hfloor : (s * R - c) / g ≤ max 0 ((s * R - c) / g) :=
    le_max_right _ _
  have hscaled : s * R - c ≤ max 0 ((s * R - c) / g) * g :=
    (div_le_iff₀ hg).1 hfloor
  nlinarith
