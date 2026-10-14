-- Prove2me | solution 1 for ActuarialValuation.cxPartialLikelihood_baseline_free
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:56:22.114128+00:00
-- url     : https://prove2.me/submissions/c1038f86-c01d-4524-939f-5c47d61018f7

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxHazard
import Definitions.Def_actuarial_cxEventShare

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (beta base : ℝ) (risk : Finset (Fin n)) (z : Fin n → ℝ) (i : Fin n) (hb : base≠0) : (cxHazard base beta (z i))/(∑ j ∈ risk, cxHazard base beta (z j))=cxEventShare beta risk z i := by
  have hsum : (∑ j ∈ risk, cxHazard base beta (z j)) =
      base * cxRiskDenom beta risk z := by
    change (∑ j ∈ risk, base * cxRelativeRisk beta (z j)) =
      base * (∑ j ∈ risk, cxRelativeRisk beta (z j))
    rw [Finset.mul_sum]
  rw [hsum]
  change (base * cxRelativeRisk beta (z i)) /
    (base * cxRiskDenom beta risk z) =
    cxRelativeRisk beta (z i) / cxRiskDenom beta risk z
  by_cases hden : cxRiskDenom beta risk z = 0
  · simp [hden]
  · field_simp [hb, hden] <;> ring
