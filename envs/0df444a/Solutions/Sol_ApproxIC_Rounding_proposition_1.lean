-- Prove2me | solution 1 for ApproxIC.Rounding.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T20:48:00.720004+00:00
-- url     : https://prove2.me/submissions/15b2c6ec-9407-4d35-a824-1a757e194147

import Mathlib
import Definitions.Def_ApproxIC_Rounding_Setting
import Theorems.Thm_ApproxIC_Rounding_revenue_gap_delta_bound

open ApproxIC.Rounding

theorem solution (M : ApproxIC.Rounding.Model) (hM : M.Standing) :
    ∃ C > 0, ∃ ε0 > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε0, ∀ m ∈ ApproxIC.Rounding.Mset M ε,
      ApproxIC.Rounding.revenue M m - ApproxIC.Rounding.optRev M 0 ≤ C * Real.sqrt ε := by
  refine ⟨2 * |optRev M 0| + 1, by positivity, 1 / 4, by norm_num, fun ε hε m hm => ?_⟩
  have hε0 : 0 < ε := hε.1
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε0
  have hs2 : Real.sqrt ε ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hε.2
  have h := (revenue_gap_delta_bound M hM ε hε0 m hm).2 (Real.sqrt ε) ⟨hs, hs2⟩
  have e : ε / Real.sqrt ε = Real.sqrt ε := by
    rw [div_eq_iff hs.ne']; exact (Real.mul_self_sqrt hε0.le).symm
  rw [e] at h
  have : 2 * Real.sqrt ε * optRev M 0 ≤ 2 * Real.sqrt ε * |optRev M 0| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  nlinarith
