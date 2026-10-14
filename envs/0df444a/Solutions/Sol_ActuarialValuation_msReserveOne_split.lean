-- Prove2me | solution 1 for ActuarialValuation.msReserveOne_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:18:57.365176+00:00
-- url     : https://prove2.me/submissions/b1735d9c-da31-42db-bb61-dfa1577bb901

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msReserveOne

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b V W : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (v : ℝ) (i : Fin 3) : msReserveOne b T (fun j => V j+W j) v i = msReserveOne b T V v i + v*(∑ j : Fin 3, T i j*W j) := by
  unfold msReserveOne
  have hsum :
      (∑ j : Fin 3, T i j * (V j + W j)) =
      (∑ j : Fin 3, T i j * V j) + (∑ j : Fin 3, T i j * W j) := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [hsum]
  ring
