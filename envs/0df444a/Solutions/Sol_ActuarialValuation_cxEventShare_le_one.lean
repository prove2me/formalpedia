-- Prove2me | solution 1 for ActuarialValuation.cxEventShare_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:34:41.227665+00:00
-- url     : https://prove2.me/submissions/a4848fd5-fddd-4b65-bfaa-d44f13623e18

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

theorem solution {n : ℕ} (beta : ℝ) (risk : Finset (Fin n)) (z : Fin n → ℝ)
    (i : Fin n) (hi : i ∈ risk) : cxEventShare beta risk z i ≤ 1 := by
  have hterm (j : Fin n) : 0 ≤ cxRelativeRisk beta (z j) := by
    unfold cxRelativeRisk
    exact (Real.exp_pos _).le
  have hle : cxRelativeRisk beta (z i) ≤ cxRiskDenom beta risk z := by
    unfold cxRiskDenom
    exact Finset.single_le_sum (fun j hj => hterm j) hi
  have hpos : 0 < cxRiskDenom beta risk z := by
    have hexp : 0 < cxRelativeRisk beta (z i) := by
      unfold cxRelativeRisk
      exact Real.exp_pos _
    exact lt_of_lt_of_le hexp hle
  unfold cxEventShare
  exact (div_le_iff₀ hpos).2 (by simpa using hle)
