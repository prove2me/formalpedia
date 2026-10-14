-- Prove2me | solution 1 for ActuarialValuation.cxPGF_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:41:52.010997+00:00
-- url     : https://prove2.me/submissions/130a286f-6cae-4125-9c59-bb183393191e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPGF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f g : ℕ → ℝ) (n : ℕ) (z : ℝ) : cxPGF (fun k => f k+g k) n z = cxPGF f n z + cxPGF g n z := by
  unfold cxPGF
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
