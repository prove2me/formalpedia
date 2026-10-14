-- Prove2me | solution 1 for ActuarialValuation.msExpectedBenefit_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:12:26.182151+00:00
-- url     : https://prove2.me/submissions/6cd2b803-ff55-40a5-858e-0b0c3a904667

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msExpectedBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p b c : Fin 3 → ℝ) : msExpectedBenefit p (fun i => b i+c i) = msExpectedBenefit p b+msExpectedBenefit p c := by
  unfold msExpectedBenefit
  simp only [mul_add, Finset.sum_add_distrib]
