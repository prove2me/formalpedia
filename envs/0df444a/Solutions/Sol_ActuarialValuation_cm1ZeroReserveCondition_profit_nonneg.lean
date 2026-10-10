-- Prove2me | solution 1 for ActuarialValuation.cm1ZeroReserveCondition_profit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:31:32.417006+00:00
-- url     : https://prove2.me/submissions/249d9eb3-a718-4151-8c82-eeedd1197bef

import Theorems.Thm_ActuarialValuation_cm1ZeroReserveFloor_profit_nonneg
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ReserveYearProfit
import Definitions.Def_actuarial_cm1ZeroReserveCondition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c s g R : ℕ → ℝ) (N t : ℕ) (h : cm1ZeroReserveCondition c s g R N) (hg : ∀ j ∈ Finset.range N, 0 < g j) (ht : t < N) : 0 ≤ cm1ReserveYearProfit c s g R t := by
  have hstep : R t = cm1ZeroReserveFloor (c t) (s t)
      (g t) (R (t + 1)) := h.2 t (Finset.mem_range.mpr ht)
  have hgt : 0 < g t := hg t (Finset.mem_range.mpr ht)
  unfold cm1ReserveYearProfit
  rw [hstep]
  exact ActuarialValuation.cm1ZeroReserveFloor_profit_nonneg
    (c t) (s t) (g t) (R (t + 1)) hgt
