-- Prove2me | solution 1 for ActuarialValuation.pvExpected_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:04:58.272369+00:00
-- url     : https://prove2.me/submissions/e2df3d8c-69f8-4496-9632-b72f90913a53

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p a : Fin n → ℝ) (c : ℝ) : pvExpected p (fun i => c * a i) = c * pvExpected p a := by
  unfold pvExpected
  calc
    (∑ i : Fin n, p i * (c * a i)) =
        ∑ i : Fin n, c * (p i * a i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = c * (∑ i : Fin n, p i * a i) := by
      rw [Finset.mul_sum]
