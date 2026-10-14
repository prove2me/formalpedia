-- Prove2me | solution 1 for ActuarialValuation.cxPGF_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:51:52.171649+00:00
-- url     : https://prove2.me/submissions/f7a1b06a-d049-4f9f-a70a-706b032fbde1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_actuarial_cxPGF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (n : ℕ) (z c : ℝ) :
    cxPGF (fun k => c*f k) n z = c*cxPGF f n z := by
  unfold cxPGF
  simp_rw [mul_assoc]
  rw [Finset.mul_sum]
