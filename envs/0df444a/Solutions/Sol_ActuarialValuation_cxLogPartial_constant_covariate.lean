-- Prove2me | solution 1 for ActuarialValuation.cxLogPartial_constant_covariate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:29:39.222579+00:00
-- url     : https://prove2.me/submissions/34a3c650-6291-43cb-bd71-d6200d7ef33a

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxLogPartial

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (beta c : ℝ) (events : Finset (Fin n))
    (risks : Fin n → Finset (Fin n))
    (h : ∀ i ∈ events, (risks i).Nonempty) :
    cxLogPartial beta events risks (fun _ => c) =
      -∑ i ∈ events, Real.log ((risks i).card : ℝ) := by
  classical
  have hden (i : Fin n) :
      cxRiskDenom beta (risks i) (fun _ => c) =
        ((risks i).card : ℝ) * Real.exp (beta * c) := by
    simp [cxRiskDenom, cxRelativeRisk, Finset.sum_const, nsmul_eq_mul]
  have hcard (i : Fin n) (hi : i ∈ events) :
      (0 : ℝ) < ((risks i).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (h i hi)
  calc
    cxLogPartial beta events risks (fun _ => c) =
        ∑ i ∈ events, -Real.log ((risks i).card : ℝ) := by
      unfold cxLogPartial
      apply Finset.sum_congr rfl
      intro i hi
      rw [hden i, Real.log_mul (ne_of_gt (hcard i hi))
        (Real.exp_ne_zero (beta * c)), Real.log_exp]
      ring
    _ = -∑ i ∈ events, Real.log ((risks i).card : ℝ) := by
      simp only [Finset.sum_neg_distrib]
