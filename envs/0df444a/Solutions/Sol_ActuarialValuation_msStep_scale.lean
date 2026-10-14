-- Prove2me | solution 1 for ActuarialValuation.msStep_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:16:42.218258+00:00
-- url     : https://prove2.me/submissions/c7cf4f99-f8d5-49d7-ae5b-012114b3c33d

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msStep

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (j : Fin 3) (c : ℝ) : msStep (fun i => c*p i) T j = c*msStep p T j := by
  unfold msStep
  calc
    (∑ i : Fin 3, (c * p i) * T i j) = ∑ i : Fin 3, c * (p i * T i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = c * (∑ i : Fin 3, p i * T i j) := by rw [Finset.mul_sum]
