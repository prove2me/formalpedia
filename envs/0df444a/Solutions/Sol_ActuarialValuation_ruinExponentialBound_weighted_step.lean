-- Prove2me | solution 1 for ActuarialValuation.ruinExponentialBound_weighted_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:50:35.558098+00:00
-- url     : https://prove2.me/submissions/35305510-e28a-4e42-9e08-8289bea0bcb6

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinExponentialBound
import Definitions.Def_actuarial_ruinNextSurplus
import Definitions.Def_actuarial_ruinAdjustmentMoment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (B c : ℕ) (R : ℝ) (u : ℤ) :
  (∑ k ∈ Finset.range (B + 1),
     w k * ruinExponentialBound R (ruinNextSurplus u c k)) =
    ruinExponentialBound R u *
      ruinAdjustmentMoment w B c R := by
  simp only [ruinExponentialBound, ruinAdjustmentMoment, ruinNextSurplus]
  push_cast
  calc
    (∑ k ∈ Finset.range (B + 1),
        w k * Real.exp (-(R * ((u : ℝ) + (c : ℝ) - (k : ℝ))))) =
      ∑ k ∈ Finset.range (B + 1),
        Real.exp (-(R * (u : ℝ))) *
          (w k * Real.exp (R * ((k : ℝ) - (c : ℝ)))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have h_exp :
          Real.exp (-(R * ((u : ℝ) + (c : ℝ) - (k : ℝ)))) =
            Real.exp (-(R * (u : ℝ))) *
              Real.exp (R * ((k : ℝ) - (c : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [h_exp]
      ring
    _ = Real.exp (-(R * (u : ℝ))) *
        ∑ k ∈ Finset.range (B + 1),
          w k * Real.exp (R * ((k : ℝ) - (c : ℝ))) := by
      rw [← Finset.mul_sum]
