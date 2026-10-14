-- Prove2me | solution 1 for ActuarialValuation.cxEventShare_normalized
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:49:28.992996+00:00
-- url     : https://prove2.me/submissions/9042c6d7-52c4-4d1e-8d94-598cf166e030

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

theorem solution {n : ℕ} (beta : ℝ) (risk : Finset (Fin n)) (z : Fin n → ℝ) (hr : risk.Nonempty) : (∑ i ∈ risk, cxEventShare beta risk z i)=1 := by
  obtain ⟨j, hj⟩ := hr
  have hle : cxRelativeRisk beta (z j) ≤ cxRiskDenom beta risk z := by
    unfold cxRiskDenom
    apply Finset.single_le_sum _ hj
    intro k hk
    unfold cxRelativeRisk
    exact (Real.exp_pos _).le
  have hpos : 0 < cxRiskDenom beta risk z := by
    have hnum : 0 < cxRelativeRisk beta (z j) := by
      unfold cxRelativeRisk
      exact Real.exp_pos _
    exact lt_of_lt_of_le hnum hle
  calc
    (∑ i ∈ risk, cxEventShare beta risk z i) =
      (∑ i ∈ risk, cxRelativeRisk beta (z i)) / cxRiskDenom beta risk z := by
        simp_rw [cxEventShare, div_eq_mul_inv]
        rw [Finset.sum_mul]
    _ = 1 := by
      change cxRiskDenom beta risk z / cxRiskDenom beta risk z = 1
      exact div_self (ne_of_gt hpos)
