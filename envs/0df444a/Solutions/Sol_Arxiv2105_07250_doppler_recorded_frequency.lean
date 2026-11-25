-- Prove2me | solution 1 for Arxiv2105_07250.doppler_recorded_frequency
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T21:44:13.890187+00:00
-- url     : https://prove2.me/submissions/e551da7b-0893-4f24-b531-3cd84cf590f2

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology

namespace S71DP
open Arxiv2105_07250

lemma dN (x v : Plane) (t : ℝ) (h : x ≠ t • v) :
    HasDerivAt (fun s : ℝ => ‖x - s • v‖) (-(inner ℝ (x - t • v) v) / ‖x - t • v‖) t := by
  have hN : ∀ s : ℝ, ‖x - s • v‖ =
      √(‖x‖ ^ 2 - 2 * inner ℝ x v * s + s * s * ‖v‖ ^ 2) := by
    intro s
    rw [← Real.sqrt_sq (norm_nonneg (x - s • v)), norm_sub_sq_real, norm_smul, real_inner_smul_right,
      Real.norm_eq_abs, mul_pow, sq_abs]
    congr 1; ring
  have h0 : ‖x - t • v‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]; exact h
  have h1 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id' t
  have hp : HasDerivAt (fun s : ℝ => ‖x‖ ^ 2 - 2 * inner ℝ x v * s + s * s * ‖v‖ ^ 2)
      (-(2 * inner ℝ x v * 1) + (1 * t + t * 1) * ‖v‖ ^ 2) t :=
    ((h1.const_mul (2 * inner ℝ x v)).const_sub (‖x‖ ^ 2)).add ((h1.mul h1).mul_const (‖v‖ ^ 2))
  have hp0 : ‖x‖ ^ 2 - 2 * inner ℝ x v * t + t * t * ‖v‖ ^ 2 ≠ 0 := by
    intro hz; apply h0; rw [hN t, hz, Real.sqrt_zero]
  have := hp.sqrt hp0
  rw [show (fun s : ℝ => √(‖x‖ ^ 2 - 2 * inner ℝ x v * s + s * s * ‖v‖ ^ 2)) =
    fun s => ‖x - s • v‖ from funext fun s => (hN s).symm, ← hN t] at this
  refine this.congr_deriv ?_
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp
  ring

lemma derivN (x v : Plane) (hv : v ≠ 0) (t : ℝ) (h : x ≠ t • v) :
    deriv (fun s : ℝ => ‖x - s • v‖) t = -‖v‖ * cosTheta x v t := by
  rw [(dN x v t h).deriv, cosTheta]
  have h0 : ‖x - t • v‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]; exact h
  have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  field_simp

lemma cos_le (x v : Plane) (t : ℝ) : |cosTheta x v t| ≤ 1 :=
  abs_real_inner_div_norm_mul_norm_le_one _ _

lemma cos_atBot (x v : Plane) (hv : v ≠ 0) : Tendsto (cosTheta x v) atBot (𝓝 1) := by
  have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  let F : ℝ → ℝ := fun u => inner ℝ (u • x + v) v / (‖u • x + v‖ * ‖v‖)
  have hF : ContinuousAt F 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simp [hv0]
  have hF0 : F 0 = 1 := by
    simp only [F, zero_smul, zero_add, real_inner_self_eq_norm_mul_norm]
    field_simp
  have hu : Tendsto (fun t : ℝ => (-t)⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_neg_atBot_atTop
  have hlim := (hF0 ▸ hF.tendsto).comp hu
  apply hlim.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
  have htn : 0 < -t := by linarith
  have e : x - t • v = (-t) • ((-t)⁻¹ • x + v) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ htn.ne', one_smul, neg_smul, sub_eq_add_neg]
  simp only [Function.comp, F, cosTheta]
  rw [e, real_inner_smul_left, norm_smul, Real.norm_eq_abs, abs_of_pos htn]
  rw [mul_assoc, mul_div_mul_left _ _ (by positivity)]

lemma cos_atTop (x v : Plane) (hv : v ≠ 0) : Tendsto (cosTheta x v) atTop (𝓝 (-1)) := by
  have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  let F : ℝ → ℝ := fun u => inner ℝ (u • x - v) v / (‖u • x - v‖ * ‖v‖)
  have hF : ContinuousAt F 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simp [hv0]
  have hF0 : F 0 = -1 := by
    simp only [F, zero_smul, zero_sub, inner_neg_left, norm_neg, real_inner_self_eq_norm_mul_norm]
    field_simp
  have hu : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hlim := (hF0 ▸ hF.tendsto).comp hu
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have e : x - t • v = t • (t⁻¹ • x - v) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  simp only [Function.comp, F, cosTheta]
  rw [e, real_inner_smul_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  rw [mul_assoc, mul_div_mul_left _ _ (by positivity)]

end S71DP

open Arxiv2105_07250 S71DP in
theorem solution (c : ℝ) (hc : 0 < c) (v : Plane) (hv0 : v ≠ 0) (hv : ‖v‖ < c)
    (wt : ℝ) (hwt : 0 < wt) (x : Plane) :
    (∀ ω t' : ℝ, x ≠ t' • v →
      (deriv (dopplerPhase c ω wt x v) t' = 0 ↔ ω = -recordedFrequency c wt x v t')) ∧
    (∀ t' : ℝ, x ≠ t' • v →
      wt / (1 + ‖v‖ / c) ≤ recordedFrequency c wt x v t' ∧
        recordedFrequency c wt x v t' ≤ wt / (1 - ‖v‖ / c)) ∧
    (∀ t' : ℝ, x ≠ t' • v →
      (deriv (fun s : ℝ => ‖x - s • v‖) t' < 0 ↔ wt < recordedFrequency c wt x v t') ∧
      (0 < deriv (fun s : ℝ => ‖x - s • v‖) t' ↔ recordedFrequency c wt x v t' < wt) ∧
      (cosTheta x v t' = 0 ↔ recordedFrequency c wt x v t' = wt)) ∧
    Tendsto (recordedFrequency c wt x v) atBot (𝓝 (wt / (1 - ‖v‖ / c))) ∧
    Tendsto (recordedFrequency c wt x v) atTop (𝓝 (wt / (1 + ‖v‖ / c))) := by
  have hvp : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have ha0 : 0 < ‖v‖ / c := div_pos hvp hc
  have ha1 : ‖v‖ / c < 1 := (div_lt_one hc).2 hv
  set a := ‖v‖ / c with ha
  have hD : ∀ t, 1 - a ≤ 1 - a * cosTheta x v t ∧ 1 - a * cosTheta x v t ≤ 1 + a := by
    intro t
    have := abs_le.1 (cos_le x v t)
    constructor <;> nlinarith [this.1, this.2]
  have hDp : ∀ t, 0 < 1 - a * cosTheta x v t := fun t => by linarith [(hD t).1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω t' h
    have hd : HasDerivAt (dopplerPhase c ω wt x v)
        ((ω + wt) * 1 + ω / c * (-(inner ℝ (x - t' • v) v) / ‖x - t' • v‖)) t' := by
      have := (((hasDerivAt_id t').const_mul (ω + wt)).add ((dN x v t' h).const_mul (ω / c))).sub_const
        (Real.pi / 4)
      exact this
    rw [hd.deriv]
    have e : (ω + wt) * 1 + ω / c * (-(inner ℝ (x - t' • v) v) / ‖x - t' • v‖) =
        ω * (1 - a * cosTheta x v t') + wt := by
      have := derivN x v hv0 t' h
      rw [(dN x v t' h).deriv] at this
      rw [this, ha]; ring
    rw [e, recordedFrequency, ← ha]
    have := hDp t'
    constructor
    · intro h0; field_simp; linarith
    · intro h0; rw [h0]; field_simp; ring
  · intro t' _
    unfold recordedFrequency
    rw [← ha]
    have h1 := hD t'
    constructor
    · exact div_le_div_of_nonneg_left hwt.le (hDp t') h1.2
    · exact div_le_div_of_nonneg_left hwt.le (by linarith) h1.1
  · intro t' h
    rw [derivN x v hv0 t' h]
    unfold recordedFrequency
    rw [← ha]
    have hp := hDp t'
    have hwa : 0 < wt * a := mul_pos hwt ha0
    set sc := cosTheta x v t'
    have hs1 : -‖v‖ * sc < 0 ↔ 0 < sc := by
      constructor
      · intro h1; by_contra hn; push Not at hn; nlinarith [mul_nonpos_of_nonneg_of_nonpos hvp.le hn]
      · intro h1; nlinarith [mul_pos hvp h1]
    have hs2 : 0 < -‖v‖ * sc ↔ sc < 0 := by
      constructor
      · intro h1; by_contra hn; push Not at hn; nlinarith [mul_nonneg hvp.le hn]
      · intro h1; nlinarith [mul_pos hvp (neg_pos.2 h1)]
    have hs3 : wt * (1 - a * sc) < wt ↔ 0 < sc := by
      constructor
      · intro h1; by_contra hn; push Not at hn; nlinarith [mul_nonpos_of_nonneg_of_nonpos hwa.le hn]
      · intro h1; nlinarith [mul_pos hwa h1]
    have hs4 : wt < wt * (1 - a * sc) ↔ sc < 0 := by
      constructor
      · intro h1; by_contra hn; push Not at hn; nlinarith [mul_nonneg hwa.le hn]
      · intro h1; nlinarith [mul_pos hwa (neg_pos.2 h1)]
    refine ⟨?_, ?_, ?_⟩
    · rw [lt_div_iff₀ hp, hs1, hs3]
    · rw [div_lt_iff₀ hp, hs2, hs4]
    · rw [div_eq_iff hp.ne']
      constructor
      · intro h1; rw [h1]; ring
      · intro h1
        have : wt * (a * cosTheta x v t') = 0 := by linarith
        rcases mul_eq_zero.1 this with h2 | h2
        · linarith
        · rcases mul_eq_zero.1 h2 with h3 | h3
          · linarith
          · exact h3
  · have := (cos_atBot x v hv0)
    have h2 : Tendsto (fun t => wt / (1 - a * cosTheta x v t)) atBot (𝓝 (wt / (1 - a * 1))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.sub (tendsto_const_nhds.mul this))
        (by linarith)
    rw [mul_one] at h2
    exact h2
  · have := (cos_atTop x v hv0)
    have h2 : Tendsto (fun t => wt / (1 - a * cosTheta x v t)) atTop (𝓝 (wt / (1 - a * (-1)))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.sub (tendsto_const_nhds.mul this))
        (by linarith)
    rw [show 1 - a * (-1) = 1 + a by ring] at h2
    exact h2
