-- Prove2me | solution 1 for ActuarialValuation.cxRiskDenom_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:44:49.873772+00:00
-- url     : https://prove2.me/submissions/f44ae926-0547-4976-b898-1133c5ac2a34

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxRiskDenom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (beta : ℝ) (risk : Finset (Fin n)) (z : Fin n → ℝ) (hr : risk.Nonempty) : 0<cxRiskDenom beta risk z := by
  obtain ⟨i, hi⟩ := hr
  have hle : cxRelativeRisk beta (z i) ≤ cxRiskDenom beta risk z := by
    unfold cxRiskDenom
    apply Finset.single_le_sum _ hi
    intro j hj
    unfold cxRelativeRisk
    exact (Real.exp_pos _).le
  have hpos : 0 < cxRelativeRisk beta (z i) := by
    unfold cxRelativeRisk
    exact Real.exp_pos _
  exact lt_of_lt_of_le hpos hle
