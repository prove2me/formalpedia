-- Prove2me | solution 1 for AgreementTop736.Exact.sec3_1_regularizer_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:27:06.156329+00:00
-- url     : https://prove2.me/submissions/4edd1a8d-a4e9-485e-8fc3-cc199afb24ba

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized

section
set_option autoImplicit false
namespace AgreementTop736.Exact
theorem chk_sec3_1_regularizer_comparison {ρ a m z u : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hm : 0 ≤ m)
    (hz : 0 ≤ z) (hu : u = z / ρ) :
    z * (fReg a m - fReg a u) ^ 2 =
      z * (m - u) ^ 2 / ((m + a) * (u + a) * (Real.sqrt (m + a) + Real.sqrt (u + a)) ^ 2) ∧
    z * (m - u) ^ 2 / ((m + a) * (u + a) * (Real.sqrt (m + a) + Real.sqrt (u + a)) ^ 2) ≤
      ρ * (m - u) ^ 2 / (m + a) ^ 2 := by
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hzu : z = ρ * u := by rw [hu]; field_simp
  have hma : 0 < m + a := by linarith
  have hua : 0 < u + a := by linarith
  set p := Real.sqrt (m + a) with hp
  set q := Real.sqrt (u + a) with hq
  have hp0 : 0 < p := Real.sqrt_pos.mpr hma
  have hq0 : 0 < q := Real.sqrt_pos.mpr hua
  have hp2 : p ^ 2 = m + a := Real.sq_sqrt hma.le
  have hq2 : q ^ 2 = u + a := Real.sq_sqrt hua.le
  have hmu : m - u = (p - q) * (p + q) := by nlinarith
  constructor
  · unfold fReg
    rw [← hp, ← hq, ← hp2, ← hq2, hmu]
    field_simp
    ring
  · rw [div_le_div_iff₀ (by positivity) (by positivity), hzu]
    have key : u * (m + a) ≤ (u + a) * (p + q) ^ 2 := by
      have : m + a ≤ (p + q) ^ 2 := by nlinarith
      have h3 : u * (m + a) ≤ u * (p + q) ^ 2 := mul_le_mul_of_nonneg_left this hu0
      nlinarith [mul_nonneg ha.le (sq_nonneg (p + q))]
    have h2 : 0 ≤ ρ * (m - u) ^ 2 * (m + a) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left key h2]
end AgreementTop736.Exact
end

theorem solution : type_of% @AgreementTop736.Exact.chk_sec3_1_regularizer_comparison := @AgreementTop736.Exact.chk_sec3_1_regularizer_comparison
