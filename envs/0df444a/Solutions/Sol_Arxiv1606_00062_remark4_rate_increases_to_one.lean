-- Prove2me | solution 1 for Arxiv1606_00062.remark4_rate_increases_to_one
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:49:15.605579+00:00
-- url     : https://prove2.me/submissions/8bed1641-96e7-4d64-b1ac-4c26432c64f1

import Mathlib
import Definitions.Def_Arxiv1606_00062_Basic

open Filter Topology Set

namespace S69R
open Arxiv1606_00062

noncomputable def rr (d κ₁ κ₂ : ℝ) : ℝ :=
  Real.sqrt ((1 + d * κ₁) * (1 + d * κ₂)) * (1 + Real.sqrt (1 - ((1 + d * κ₁) * (1 + d * κ₂))⁻¹))

lemma norm_eq (k d κ₁ κ₂ : ℝ) : ‖rateR2 k d κ₁ κ₂‖ = |rr d κ₁ κ₂|⁻¹ := by
  unfold rateR2
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  have : ‖Complex.exp (2 * Complex.I * k * d)‖ = 1 := by
    rw [show (2 * Complex.I * k * d) = ((2 * k * d : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [this, one_mul]; rfl

end S69R

open Arxiv1606_00062 in
theorem solution (k κ₁ κ₂ : ℝ) (hk : 0 < k) (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) :
    StrictAntiOn (fun d : ℝ => ‖rateR2 k d κ₁ κ₂‖) (Set.Ioi 0) ∧
    Tendsto (fun d : ℝ => ‖rateR2 k d κ₁ κ₂‖) (𝓝[>] 0) (𝓝 1) := by
  simp only [S69R.norm_eq]
  constructor
  · intro x hx y hy hxy
    have hx : 0 < x := hx
    have hy : 0 < y := hy
    simp only
    have hP1 : 1 < (1 + x * κ₁) * (1 + x * κ₂) := by nlinarith [mul_pos hx hκ₁, mul_pos hx hκ₂]
    have hP12 : (1 + x * κ₁) * (1 + x * κ₂) < (1 + y * κ₁) * (1 + y * κ₂) := by
      nlinarith [mul_pos hx hκ₁, mul_pos hx hκ₂, mul_lt_mul_of_pos_right hxy hκ₁,
        mul_lt_mul_of_pos_right hxy hκ₂]
    set P := (1 + x * κ₁) * (1 + x * κ₂)
    set Q := (1 + y * κ₁) * (1 + y * κ₂)
    have hs1 : Real.sqrt P < Real.sqrt Q := Real.sqrt_lt_sqrt (by linarith) hP12
    have hinv : Q⁻¹ < P⁻¹ := inv_strictAnti₀ (by linarith) hP12
    have hs2 : Real.sqrt (1 - P⁻¹) ≤ Real.sqrt (1 - Q⁻¹) := Real.sqrt_le_sqrt (by linarith)
    have hsp : 0 < Real.sqrt P := Real.sqrt_pos.mpr (by linarith)
    have h0 := Real.sqrt_nonneg (1 - P⁻¹)
    have hr1 : 0 < S69R.rr x κ₁ κ₂ := by unfold S69R.rr; positivity
    have hr12 : S69R.rr x κ₁ κ₂ < S69R.rr y κ₁ κ₂ := by
      unfold S69R.rr
      calc Real.sqrt P * (1 + Real.sqrt (1 - P⁻¹)) < Real.sqrt Q * (1 + Real.sqrt (1 - P⁻¹)) :=
            mul_lt_mul_of_pos_right hs1 (by linarith)
        _ ≤ Real.sqrt Q * (1 + Real.sqrt (1 - Q⁻¹)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [abs_of_pos hr1, abs_of_pos (hr1.trans hr12)]
    exact inv_strictAnti₀ hr1 hr12
  · have h0 : S69R.rr 0 κ₁ κ₂ = 1 := by simp [S69R.rr]
    have hc : ContinuousAt (fun d => |S69R.rr d κ₁ κ₂|⁻¹) 0 := by
      apply ContinuousAt.inv₀
      · unfold S69R.rr
        have hP : ContinuousAt (fun d : ℝ => ((1 + d * κ₁) * (1 + d * κ₂))⁻¹) 0 :=
          ContinuousAt.inv₀ (by fun_prop) (by simp)
        refine continuous_abs.continuousAt.comp ?_
        refine ContinuousAt.mul (by fun_prop) ?_
        refine continuousAt_const.add ?_
        exact Real.continuous_sqrt.continuousAt.comp (continuousAt_const.sub hP)
      · simp [h0]
    have := hc.tendsto
    simp only [h0, abs_one, inv_one] at this
    exact this.mono_left nhdsWithin_le_nhds
