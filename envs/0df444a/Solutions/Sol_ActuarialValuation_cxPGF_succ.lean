-- Prove2me | solution 1 for ActuarialValuation.cxPGF_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:40:24.65312+00:00
-- url     : https://prove2.me/submissions/c21b816c-673d-4abc-b28f-c747e7656635

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPGF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (n : ℕ) (z : ℝ) : cxPGF f (n+1) z = cxPGF f n z + f n*z^n := by
  simp [cxPGF, Finset.sum_range_succ]
