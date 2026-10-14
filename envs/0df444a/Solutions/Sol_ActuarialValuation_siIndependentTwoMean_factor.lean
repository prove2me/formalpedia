-- Prove2me | solution 1 for ActuarialValuation.siIndependentTwoMean_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:13:19.274979+00:00
-- url     : https://prove2.me/submissions/9660636e-1193-4e1d-ad60-f7f76972a0a2

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siGrossMean
import Definitions.Def_actuarial_siIndependentTwoMean

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m n : ℕ} (p : Fin m → ℝ) (q : Fin n → ℝ) (r : Fin m → ℝ) (s : Fin n → ℝ) : siIndependentTwoMean p q r s=siGrossMean p r*siGrossMean q s := by
  unfold siIndependentTwoMean siGrossMean siMean
  calc
    (∑ a : Fin m, ∑ b : Fin n,
       (p a * q b) * (siGrowth (r a) * siGrowth (s b))) =
       ∑ a : Fin m, (p a * siGrowth (r a)) *
         (∑ b : Fin n, q b * siGrowth (s b)) := by
           apply Finset.sum_congr rfl
           intro a ha
           rw [Finset.mul_sum]
           apply Finset.sum_congr rfl
           intro b hb
           ring
    _ = (∑ a : Fin m, p a * siGrowth (r a)) *
        (∑ b : Fin n, q b * siGrowth (s b)) := by
           rw [Finset.sum_mul]
