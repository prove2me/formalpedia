-- Prove2me | solution 1 for ActuarialValuation.cm1ZeroReserveCondition_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:26:50.148242+00:00
-- url     : https://prove2.me/submissions/0c066d6f-6c15-4c04-969a-b6345a6f07cf

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ZeroReserveCondition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c s g R : ℕ → ℝ) (N t : ℕ) (h : cm1ZeroReserveCondition c s g R N) (ht : t ≤ N) : 0 ≤ R t := by
  by_cases hlt : t < N
  · rw [h.2 t (Finset.mem_range.mpr hlt)]
    unfold cm1ZeroReserveFloor
    exact le_max_left _ _
  · have heq : t = N := by omega
    rw [heq, h.1]
