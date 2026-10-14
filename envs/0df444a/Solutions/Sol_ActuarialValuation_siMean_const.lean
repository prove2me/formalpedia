-- Prove2me | solution 1 for ActuarialValuation.siMean_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:03:30.605565+00:00
-- url     : https://prove2.me/submissions/f086e252-e9a7-4478-b0b1-ab94ca9a19de

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (c : ℝ) (h : (∑ j : Fin m, p j)=1) : siMean p (fun _ => c)=c := by
  unfold siMean
  calc
    (∑ j : Fin m, p j * c) = (∑ j : Fin m, p j) * c := by rw [Finset.sum_mul]
    _ = c := by rw [h, one_mul]
