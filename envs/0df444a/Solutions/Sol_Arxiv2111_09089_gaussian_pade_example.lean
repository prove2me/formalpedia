-- Prove2me | solution 1 for Arxiv2111_09089.gaussian_pade_example
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:32:14.219004+00:00
-- url     : https://prove2.me/submissions/73087c88-5fb5-4bcb-975b-2f30d443724e

import Mathlib
import Definitions.Def_Arxiv2111_09089_Basic

open Complex MeasureTheory Filter Topology Asymptotics
open Arxiv2111_09089

lemma gp_near : ∀ᶠ x : ℝ in 𝓝 0, x ^ 2 ≤ 1 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  have : |x| ^ 2 ≤ 1 := by nlinarith [abs_nonneg x]
  simpa [sq_abs] using this

lemma gp1 : (fun x : ℝ => Real.exp (-x ^ 2) - gaussTaylor x) =O[𝓝 0] (fun x => x ^ 8) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [gp_near] with x hx
  have hb := Real.exp_bound (x := -x ^ 2) (by rw [abs_neg, abs_of_nonneg (sq_nonneg x)]; exact hx)
    (n := 4) (by norm_num)
  have hs : ∑ i ∈ Finset.range 4, (-x ^ 2) ^ i / (i.factorial : ℝ) = gaussTaylor x := by
    simp [Finset.sum_range_succ, Nat.factorial, gaussTaylor]; ring
  rw [hs, abs_neg, abs_of_nonneg (sq_nonneg x)] at hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 8)]
  have : (x ^ 2) ^ 4 = x ^ 8 := by ring
  rw [this] at hb
  have hx8 : 0 ≤ x ^ 8 := by positivity
  norm_num at hb
  nlinarith

lemma gp2 : (fun x : ℝ => padeP1 x - gaussTaylor x) =O[𝓝 0] (fun x => x ^ 8) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [gp_near] with x hx
  have hd : 1 ≤ 1 + 2 * x ^ 2 / 3 + x ^ 4 / 6 := by nlinarith [sq_nonneg x, sq_nonneg (x^2)]
  have he : padeP1 x - gaussTaylor x = x ^ 8 * (1 + x ^ 2) / 36 / (1 + 2 * x ^ 2 / 3 + x ^ 4 / 6) := by
    unfold padeP1 gaussTaylor
    field_simp
    ring
  rw [he, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 8),
    abs_of_nonneg (by positivity)]
  rw [div_le_iff₀ (by linarith)]
  have hx8 : 0 ≤ x ^ 8 := by positivity
  nlinarith [mul_nonneg hx8 (sq_nonneg x)]

lemma gp_d2 (x : ℝ) : 1 ≤ 1 + x ^ 2 + x ^ 4 / 2 := by nlinarith [sq_nonneg x, sq_nonneg (x^2)]

lemma gp3 : (fun x : ℝ => padeP2 x - (1 - x ^ 2 + x ^ 4 / 2)) =O[𝓝 0] (fun x => x ^ 6) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [gp_near] with x hx
  have hd := gp_d2 x
  have he : padeP2 x - (1 - x ^ 2 + x ^ 4 / 2) = -(x ^ 8 / 4 / (1 + x ^ 2 + x ^ 4 / 2)) := by
    unfold padeP2
    field_simp
    ring
  rw [he, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 6),
    abs_of_nonneg (by positivity)]
  rw [div_le_iff₀ (by linarith)]
  have hx6 : 0 ≤ x ^ 6 := by positivity
  have h86 : x ^ 8 ≤ x ^ 6 := by
    have : x ^ 8 = x ^ 6 * x ^ 2 := by ring
    rw [this]; nlinarith
  nlinarith [mul_nonneg hx6 (sq_nonneg x)]

lemma gp4 : Tendsto (fun x : ℝ => (padeP2 x - gaussTaylor x) / x ^ 6) (𝓝[≠] 0) (𝓝 (1 / 6)) := by
  have hc : Tendsto (fun x : ℝ => 1 / 6 - x ^ 2 / (4 * (1 + x ^ 2 + x ^ 4 / 2))) (𝓝 0) (𝓝 (1 / 6)) := by
    have : ContinuousAt (fun x : ℝ => 1 / 6 - x ^ 2 / (4 * (1 + x ^ 2 + x ^ 4 / 2))) 0 := by
      apply ContinuousAt.sub continuousAt_const
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      norm_num
    simpa using this.tendsto
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := hx
  have hd := gp_d2 x
  unfold padeP2 gaussTaylor
  field_simp
  ring



lemma gp_sq : Tendsto (fun x : ℝ => x ^ 2) (cocompact ℝ) atTop := by
  have := (tendsto_pow_atTop (two_ne_zero (α := ℕ))).comp (tendsto_norm_cocompact_atTop (E := ℝ))
  refine this.congr (fun x => ?_)
  simp [Real.norm_eq_abs, sq_abs]

lemma gp5 : Tendsto gaussTaylor (cocompact ℝ) atBot := by
  have hg : Tendsto (fun x : ℝ => 1 + -(x ^ 2)) (cocompact ℝ) atBot :=
    tendsto_atBot_add_const_left _ 1 (tendsto_neg_atTop_atBot.comp gp_sq)
  refine tendsto_atBot_mono' _ ?_ hg
  filter_upwards [gp_sq.eventually_ge_atTop 6] with x hx
  unfold gaussTaylor
  have h4 : x ^ 4 = (x ^ 2) ^ 2 := by ring
  have h6 : x ^ 6 = (x ^ 2) ^ 3 := by ring
  rw [h4, h6]
  nlinarith [mul_nonneg (sq_nonneg (x ^ 2)) (by linarith : (0:ℝ) ≤ x ^ 2 - 3)]

lemma gp_w : Tendsto (fun x : ℝ => (x ^ 2)⁻¹) (cocompact ℝ) (𝓝 0) :=
  tendsto_inv_atTop_zero.comp gp_sq

lemma gp6 : Tendsto (fun x : ℝ => x ^ 2 * padeP1 x) (cocompact ℝ) (𝓝 (-2)) := by
  have hF : Tendsto (fun w : ℝ => (w - 1 / 3) / (w ^ 2 + 2 * w / 3 + 1 / 6)) (𝓝 0) (𝓝 (-2)) := by
    have : ContinuousAt (fun w : ℝ => (w - 1 / 3) / (w ^ 2 + 2 * w / 3 + 1 / 6)) 0 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop); norm_num
    have h := this.tendsto
    norm_num at h
    exact h
  refine (hF.comp gp_w).congr' ?_
  filter_upwards [gp_sq.eventually_ge_atTop 1] with x hx
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
  have hd : 0 < 1 + 2 * x ^ 2 / 3 + x ^ 4 / 6 := by positivity
  have hd' : ((x ^ 2)⁻¹) ^ 2 + 2 * (x ^ 2)⁻¹ / 3 + 1 / 6 ≠ 0 := by positivity
  simp only [Function.comp, padeP1]
  field_simp

lemma gp7 : Tendsto (fun x : ℝ => x ^ 4 * padeP2 x) (cocompact ℝ) (𝓝 2) := by
  have hF : Tendsto (fun w : ℝ => 1 / (w ^ 2 + w + 1 / 2)) (𝓝 0) (𝓝 2) := by
    have : ContinuousAt (fun w : ℝ => 1 / (w ^ 2 + w + 1 / 2)) 0 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop); norm_num
    have h := this.tendsto
    norm_num at h
    simpa only [one_div] using h
  refine (hF.comp gp_w).congr' ?_
  filter_upwards [gp_sq.eventually_ge_atTop 1] with x hx
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
  have hd : 0 < 1 + x ^ 2 + x ^ 4 / 2 := by positivity
  have hd' : ((x ^ 2)⁻¹) ^ 2 + (x ^ 2)⁻¹ + 1 / 2 ≠ 0 := by positivity
  simp only [Function.comp, padeP2]
  field_simp

lemma gp8 (n : ℕ) : Tendsto (fun x : ℝ => x ^ n * Real.exp (-x ^ 2)) (cocompact ℝ) (𝓝 0) := by
  have hb := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp gp_sq
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [gp_sq.eventually_ge_atTop 1] with x hx
  simp only [Function.comp, norm_mul, Real.norm_eq_abs, abs_pow, Real.abs_exp]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply pow_le_pow_left₀ (abs_nonneg x)
  have : |x| ≤ |x| ^ 2 := by
    have h1 : 1 ≤ |x| := by
      by_contra h; push_neg at h
      have : |x| ^ 2 < 1 := by nlinarith [abs_nonneg x]
      rw [sq_abs] at this; linarith
    nlinarith
  rwa [sq_abs] at this


theorem solution :
    (fun x : ℝ => Real.exp (-x ^ 2) - gaussTaylor x) =O[𝓝 0] (fun x => x ^ 8) ∧
    (fun x : ℝ => padeP1 x - gaussTaylor x) =O[𝓝 0] (fun x => x ^ 8) ∧
    (fun x : ℝ => padeP2 x - (1 - x ^ 2 + x ^ 4 / 2)) =O[𝓝 0] (fun x => x ^ 6) ∧
    Tendsto (fun x : ℝ => (padeP2 x - gaussTaylor x) / x ^ 6) (𝓝[≠] 0) (𝓝 (1 / 6)) ∧
    Tendsto gaussTaylor (cocompact ℝ) atBot ∧
    Tendsto (fun x : ℝ => x ^ 2 * padeP1 x) (cocompact ℝ) (𝓝 (-2)) ∧
    Tendsto (fun x : ℝ => x ^ 4 * padeP2 x) (cocompact ℝ) (𝓝 2) ∧
    ∀ n : ℕ, Tendsto (fun x : ℝ => x ^ n * Real.exp (-x ^ 2)) (cocompact ℝ) (𝓝 0) :=
  ⟨gp1, gp2, gp3, gp4, gp5, gp6, gp7, gp8⟩

