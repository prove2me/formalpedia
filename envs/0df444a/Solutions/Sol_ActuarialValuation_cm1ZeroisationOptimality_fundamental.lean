-- Prove2me | solution 1 for ActuarialValuation.cm1ZeroisationOptimality_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:34:31.421267+00:00
-- url     : https://prove2.me/submissions/081af158-1680-4a0d-9e45-ca7746a685bf

import Theorems.Thm_ActuarialValuation_cm1ZeroReserveCondition_profit_nonneg
import Theorems.Thm_ActuarialValuation_cm1ZeroReserveCondition_minimal
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ReserveYearProfit
import Definitions.Def_actuarial_cm1ZeroReserveCondition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c s g R Q : ℕ → ℝ) (N : ℕ)
  (hR : cm1ZeroReserveCondition c s g R N)
  (hg : ∀ j ∈ Finset.range N, 0 < g j)
  (hs : ∀ j ∈ Finset.range N, 0 ≤ s j)
  (hQend : Q N = 0)
  (hQpos : ∀ j, j ≤ N → 0 ≤ Q j)
  (hQprof : ∀ j ∈ Finset.range N, 0 ≤ cm1ReserveYearProfit c s g Q j) :
  (∀ t ∈ Finset.range N, 0 ≤ cm1ReserveYearProfit c s g R t) ∧
  (∀ t, t ≤ N → R t ≤ Q t) := by
  constructor
  · intro t ht
    exact ActuarialValuation.cm1ZeroReserveCondition_profit_nonneg
      c s g R N t hR hg (Finset.mem_range.mp ht)
  · intro t ht
    exact ActuarialValuation.cm1ZeroReserveCondition_minimal
      c s g R Q N t hR hg hs hQend hQpos hQprof ht
