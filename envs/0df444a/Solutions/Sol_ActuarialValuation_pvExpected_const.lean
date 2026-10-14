-- Prove2me | solution 1 for ActuarialValuation.pvExpected_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:04:50.75586+00:00
-- url     : https://prove2.me/submissions/910c9b12-d35d-4345-8d6e-493f8d7d8897

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

theorem solution {n : ℕ} (p : Fin n → ℝ) (a : ℝ) (hp : (∑ i : Fin n, p i) = 1) : pvExpected p (fun _ => a) = a := by
  unfold pvExpected
  calc
    (∑ i : Fin n, p i * a) = (∑ i : Fin n, p i) * a := by
      rw [Finset.sum_mul]
    _ = a := by rw [hp]; ring
