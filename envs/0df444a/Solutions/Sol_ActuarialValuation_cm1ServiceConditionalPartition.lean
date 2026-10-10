-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceConditionalPartition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:59:06.627891+00:00
-- url     : https://prove2.me/submissions/69b02219-69ed-423b-b746-7bef79af179e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceValid
import Definitions.Def_actuarial_cm1ServiceConditionalCause
import Definitions.Def_actuarial_cm1ServiceOneYearSurvival
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (d : ℕ → ℕ → ℝ) (N m t : ℕ) (hv : cm1ServiceValid l d N m) (ht : t < N) (hl : l t ≠ 0) : cm1ServiceOneYearSurvival l t + (∑ j ∈ Finset.range m, cm1ServiceConditionalCause l d t j) = 1 := by
  have hs := hv t (Finset.mem_range.mpr ht)
  dsimp only [cm1ServiceAnnualExit] at hs
  dsimp only [cm1ServiceOneYearSurvival, cm1ServiceConditionalCause]
  calc
    l (t+1) / l t + (∑ j ∈ Finset.range m, d t j / l t) =
      (l (t+1) + ∑ j ∈ Finset.range m, d t j) / l t := by
        simp_rw [div_eq_mul_inv]
        rw [add_mul, Finset.sum_mul]
    _ = 1 := by rw [hs]; exact div_self hl
