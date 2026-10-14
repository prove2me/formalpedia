-- Prove2me | solution 1 for ActuarialValuation.cxRegression_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:36:03.966983+00:00
-- url     : https://prove2.me/submissions/0d789375-c0de-40eb-a0f2-70af0e921ae0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_cxSurvival
import Definitions.Def_actuarial_cxHazardRatio
import Definitions.Def_actuarial_cxLogPartial
import Definitions.Def_actuarial_cxScore

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (beta base H z1 z2 : ℝ)
    (events : Finset (Fin n)) (risks : Fin n → Finset (Fin n))
    (z : Fin n → ℝ) (hb : base ≠ 0) (hH : 0 ≤ H)
    (hr : ∀ i ∈ events, (risks i).Nonempty) :
    (cxHazardRatio base beta z1 z2 = Real.exp (beta * (z1 - z2))) ∧
    (cxSurvival H beta z1 ≤ 1) ∧
    HasDerivAt (fun t => cxLogPartial t events risks z)
      (cxScore beta events risks z) beta := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have h2 : Real.exp (beta * z2) ≠ 0 := ne_of_gt (Real.exp_pos _)
    rw [show beta * (z1 - z2) = beta * z1 - beta * z2 by ring,
      Real.exp_sub]
    unfold cxHazardRatio cxHazard cxRelativeRisk
    field_simp [hb, h2] <;> ring
  · unfold cxSurvival
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    apply Real.exp_le_exp.mpr
    have hp := Real.exp_pos (beta * z1)
    unfold cxRelativeRisk
    nlinarith
  · have hden_deriv (risk : Finset (Fin n)) :
        HasDerivAt (fun t : ℝ => cxRiskDenom t risk z)
          (cxRiskWeighted beta risk z) beta := by
      unfold cxRiskDenom cxRiskWeighted
      apply HasDerivAt.fun_sum
      intro j hj
      simpa [cxRelativeRisk, mul_comm] using
        (((hasDerivAt_id beta).mul_const (z j)).exp)
    have hden_pos (i : Fin n) (hi : i ∈ events) :
        0 < cxRiskDenom beta (risks i) z := by
      simpa [cxRiskDenom, cxRelativeRisk] using
        (Finset.sum_pos (fun j hj => Real.exp_pos (beta * z j)) (hr i hi))
    change HasDerivAt
      (fun t : ℝ => ∑ i ∈ events,
        (t * z i - Real.log (cxRiskDenom t (risks i) z)))
      (∑ i ∈ events, (z i - cxRiskMean beta (risks i) z)) beta
    apply HasDerivAt.fun_sum
    intro i hi
    have hlog :=
      (hden_deriv (risks i)).log (ne_of_gt (hden_pos i hi))
    convert ((hasDerivAt_id beta).mul_const (z i)).sub hlog using 1
    · ext t
      rfl
    · simp only [cxRiskMean]
      ring
