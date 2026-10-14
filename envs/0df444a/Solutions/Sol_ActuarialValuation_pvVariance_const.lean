-- Prove2me | solution 1 for ActuarialValuation.pvVariance_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:08:19.873255+00:00
-- url     : https://prove2.me/submissions/188b597f-60e6-41c1-95cc-18437131205c

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvVariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p : Fin n → ℝ) (c : ℝ) (hp : (∑ i : Fin n, p i) = 1) : pvVariance p (fun _ => c) = 0 := by
  unfold pvVariance pvExpected pvSecondMoment
  have he1 : (∑ i : Fin n, p i * c) = c := by
    calc
      (∑ i : Fin n, p i * c) = (∑ i : Fin n, p i) * c := by
        rw [Finset.sum_mul]
      _ = c := by rw [hp]; ring
  have he2 : (∑ i : Fin n, p i * c^2) = c^2 := by
    calc
      (∑ i : Fin n, p i * c^2) =
          (∑ i : Fin n, p i) * c^2 := by
        rw [Finset.sum_mul]
      _ = c^2 := by rw [hp]; ring
  rw [he1, he2]
  ring
