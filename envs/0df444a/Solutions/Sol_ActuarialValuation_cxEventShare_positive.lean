-- Prove2me | solution 1 for ActuarialValuation.cxEventShare_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:46:54.416269+00:00
-- url     : https://prove2.me/submissions/d35ceb70-2236-4138-8322-b40d8acf988b

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxEventShare

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (beta : ℝ) (risk : Finset (Fin n)) (z : Fin n → ℝ) (i : Fin n) (hr : risk.Nonempty) : 0<cxEventShare beta risk z i := by
  obtain ⟨j, hj⟩ := hr
  have hle : cxRelativeRisk beta (z j) ≤ cxRiskDenom beta risk z := by
    unfold cxRiskDenom
    apply Finset.single_le_sum _ hj
    intro k hk
    unfold cxRelativeRisk
    exact (Real.exp_pos _).le
  have hden : 0 < cxRiskDenom beta risk z := by
    have hnum : 0 < cxRelativeRisk beta (z j) := by
      unfold cxRelativeRisk
      exact Real.exp_pos _
    exact lt_of_lt_of_le hnum hle
  unfold cxEventShare
  apply div_pos _ hden
  unfold cxRelativeRisk
  exact Real.exp_pos _
