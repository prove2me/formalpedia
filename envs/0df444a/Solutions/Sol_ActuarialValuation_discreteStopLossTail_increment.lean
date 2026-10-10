-- Prove2me | solution 1 for ActuarialValuation.discreteStopLossTail_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:33:41.464984+00:00
-- url     : https://prove2.me/submissions/6879557a-c899-4ff6-800c-b72c3d46f35b

import Mathlib
import Definitions.Def_actuarial_discreteStopLossTail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound deductible : ℕ) :
  discreteStopLossTail w bound deductible =
    discreteStopLossTail w bound (deductible + 1) +
      (if deductible + 1 ≤ bound then w (deductible + 1) else 0) := by
  classical
  have hsplit (s : ℕ) :
      (if deductible < s then w s else 0) =
        (if deductible + 1 < s then w s else 0) +
          (if s = deductible + 1 then w s else 0) := by
    by_cases hs : s = deductible + 1
    · subst s
      simp
    · by_cases hgt : deductible + 1 < s
      · have hd : deductible < s := by omega
        simp [hs, hgt, hd]
      · have hd : ¬ deductible < s := by omega
        simp [hs, hgt, hd]
  have hsingle :
      (∑ s ∈ Finset.range (bound + 1),
        if s = deductible + 1 then w s else 0) =
      (if deductible + 1 ≤ bound then w (deductible + 1) else 0) := by
    simp [Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]
  unfold discreteStopLossTail
  calc
    (∑ s ∈ Finset.range (bound + 1),
      if deductible < s then w s else 0) =
      ∑ s ∈ Finset.range (bound + 1),
        ((if deductible + 1 < s then w s else 0) +
          (if s = deductible + 1 then w s else 0)) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hsplit s
    _ = (∑ s ∈ Finset.range (bound + 1),
        if deductible + 1 < s then w s else 0) +
          (∑ s ∈ Finset.range (bound + 1),
            if s = deductible + 1 then w s else 0) := by
      rw [Finset.sum_add_distrib]
    _ = _ := by rw [hsingle]
