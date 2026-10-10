-- Prove2me | solution 1 for ActuarialValuation.cm1ZeroReserveCondition_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:22:10.283905+00:00
-- url     : https://prove2.me/submissions/d40ddd7a-2731-421c-a20c-a1fe0c35ae9c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ZeroReserveFloor
import Definitions.Def_actuarial_cm1ZeroReserveCondition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c s g R : ℕ → ℝ) (N t : ℕ) (h : cm1ZeroReserveCondition c s g R N) (ht : t < N) : R t = cm1ZeroReserveFloor (c t) (s t) (g t) (R (t+1)) := by
  exact h.2 t (Finset.mem_range.mpr ht)
