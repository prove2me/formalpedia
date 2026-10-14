-- Prove2me | solution 1 for ActuarialValuation.cxRiskMean_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:30:06.54076+00:00
-- url     : https://prove2.me/submissions/582f326c-8f4d-4cce-ae59-b84e339f2651

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxRiskMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (beta c : ℝ) (risk : Finset (Fin n))
    (h : risk.Nonempty) : cxRiskMean beta risk (fun _ => c) = c := by
  classical
  have hcard : (0 : ℝ) < (risk.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr h
  have hden :
      cxRiskDenom beta risk (fun _ => c) =
        (risk.card : ℝ) * Real.exp (beta * c) := by
    simp [cxRiskDenom, cxRelativeRisk, Finset.sum_const, nsmul_eq_mul]
  have hweighted :
      cxRiskWeighted beta risk (fun _ => c) =
        (risk.card : ℝ) * (c * Real.exp (beta * c)) := by
    simp [cxRiskWeighted, cxRelativeRisk, Finset.sum_const, nsmul_eq_mul]
    <;> ring
  change cxRiskWeighted beta risk (fun _ => c) /
      cxRiskDenom beta risk (fun _ => c) = c
  rw [hden, hweighted]
  apply (div_eq_iff (mul_ne_zero (ne_of_gt hcard)
    (Real.exp_ne_zero (beta * c)))).mpr
  ring
