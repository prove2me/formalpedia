-- Prove2me | solution 1 for ActuarialValuation.cxLogPartial_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:32:49.572935+00:00
-- url     : https://prove2.me/submissions/fcd9b8f8-17f0-41fd-90af-ca55f1a96159

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxLogPartial
import Definitions.Def_actuarial_cxScore

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (beta : ℝ) (events : Finset (Fin n))
    (risks : Fin n → Finset (Fin n)) (z : Fin n → ℝ)
    (h : ∀ i ∈ events, (risks i).Nonempty) :
    HasDerivAt (fun t => cxLogPartial t events risks z)
      (cxScore beta events risks z) beta := by
  classical
  have hden_deriv (risk : Finset (Fin n)) :
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
      (Finset.sum_pos (fun j hj => Real.exp_pos (beta * z j)) (h i hi))
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
