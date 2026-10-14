-- Prove2me | solution 1 for ActuarialValuation.pucAccruedBenefit_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:03:38.969257+00:00
-- url     : https://prove2.me/submissions/3590685c-f90e-4b25-8017-159ce7425680

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucAccruedBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u v : ℕ → ℝ) (n : ℕ) : pucAccruedBenefit (fun t => u t + v t) n = pucAccruedBenefit u n + pucAccruedBenefit v n := by
  simp only [pucAccruedBenefit, Finset.sum_add_distrib]
