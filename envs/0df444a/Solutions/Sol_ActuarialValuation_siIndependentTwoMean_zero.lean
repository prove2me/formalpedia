-- Prove2me | solution 1 for ActuarialValuation.siIndependentTwoMean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:10:03.790993+00:00
-- url     : https://prove2.me/submissions/b0f517e2-5f20-455c-8131-0eabfed25445

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siIndependentTwoMean

import Mathlib.Algebra.BigOperators.Ring.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m n : ℕ} (p : Fin m → ℝ) (q : Fin n → ℝ) (h1 : (∑ j : Fin m, p j)=1) (h2 : (∑ j : Fin n, q j)=1) : siIndependentTwoMean p q (fun _ => 0) (fun _ => 0)=1 := by
  unfold siIndependentTwoMean siGrowth
  simp only [add_zero, mul_one]
  calc
    (∑ a : Fin m, ∑ b : Fin n, p a * q b) =
        (∑ a : Fin m, p a) * (∑ b : Fin n, q b) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
    _ = 1 := by rw [h1, h2, one_mul]
