-- Prove2me | solution 1 for ActuarialValuation.pvExpected_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:56:17.198187+00:00
-- url     : https://prove2.me/submissions/0becd5e0-5711-4fef-86f8-88cd4d40947a

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p a b : Fin n → ℝ) : pvExpected p (fun i => a i + b i) = pvExpected p a + pvExpected p b := by
  unfold pvExpected
  simp only [mul_add, Finset.sum_add_distrib]
