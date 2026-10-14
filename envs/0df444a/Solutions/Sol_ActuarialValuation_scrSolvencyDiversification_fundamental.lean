-- Prove2me | solution 1 for ActuarialValuation.scrSolvencyDiversification_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:43:10.021959+00:00
-- url     : https://prove2.me/submissions/6a9b2660-de1f-45be-b7d4-75192869e8d2

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPairSquared
import Definitions.Def_actuarial_scrSumSquared
import Definitions.Def_actuarial_scrDiversificationSquared

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rho a b : ℝ) (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) : (0 ≤ scrPairSquared rho a b) ∧ (0 ≤ scrDiversificationSquared rho a b) ∧ (scrPairSquared rho a b + scrDiversificationSquared rho a b = scrSumSquared a b) ∧ (scrPairSquared 1 a b = scrSumSquared a b) := by
  have hcov : 0 ≤ rho * a * b := mul_nonneg (mul_nonneg hr0 ha) hb
  have hcov2 : 0 ≤ (2:ℝ) * (rho * a * b) :=
    mul_nonneg (by norm_num) hcov
  have hgap : 0 ≤ 1 - rho := sub_nonneg.mpr hr1
  have hdiv : 0 ≤ (2:ℝ) * (1 - rho) * a * b :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hgap) ha) hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold scrPairSquared scrCovarianceTerm
    nlinarith [sq_nonneg a, sq_nonneg b]
  · unfold scrDiversificationSquared scrPairSquared
      scrSumSquared scrCovarianceTerm
    nlinarith
  · unfold scrDiversificationSquared
    ring
  · unfold scrPairSquared scrCovarianceTerm scrSumSquared
    ring
