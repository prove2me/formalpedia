-- Prove2me | solution 1 for Arxivmath_ph_0108008.wronskP_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T00:38:12.083934+00:00
-- url     : https://prove2.me/submissions/5c8f0e90-8457-4c45-a981-6e954f513238

import Mathlib
import Definitions.Def_Arxivmath_ph_0108008_Basic

set_option autoImplicit false

open Filter Topology Asymptotics

namespace S73WP
open Arxivmath_ph_0108008

lemma formula (r : ℝ) (hr : 0 < r) :
    wronskP r = 1 - (3 + 3 * Real.cos r ^ 2) / r ^ 2 + 3 * Real.sin (2 * r) / r ^ 3 := by
  have hr0 : r ≠ 0 := hr.ne'
  have h1 := ((((hasDerivAt_const r (3:ℝ)).div (hasDerivAt_pow 2 r) (pow_ne_zero 2 hr0)).sub
    (hasDerivAt_const r (1:ℝ))).mul (Real.hasDerivAt_sin r)).sub
    (((hasDerivAt_const r (3:ℝ)).div (hasDerivAt_id' r) hr0).mul (Real.hasDerivAt_cos r))
  have hd : deriv riccatiU2 r = ((0 * r ^ 2 - 3 * (↑2 * r ^ (2 - 1))) / (r ^ 2) ^ 2 - 0) * Real.sin r +
      (3 / r ^ 2 - 1) * Real.cos r -
      ((0 * r - 3 * 1) / r ^ 2 * Real.cos r + 3 / r * -Real.sin r) := h1.deriv
  have hc : deriv (fun x => -Real.cos x) r = Real.sin r := by
    have := (Real.hasDerivAt_cos r).neg
    exact this.deriv.trans (neg_neg _)
  unfold wronskP
  rw [hd, hc]
  unfold riccatiU2
  rw [Real.sin_two_mul]
  field_simp
  have := Real.sin_sq_add_cos_sq r
  push_cast
  linear_combination (-3 * r ^ 2 + r ^ 4) * this


lemma tay (u : ℝ) (hu : |u| ≤ 1) :
    |Real.cos u - (1 - u^2/2 + u^4/24 - u^6/720)| ≤ 2 * |u|^8 ∧
    |Real.sin u - (u - u^3/6 + u^5/120 - u^7/5040)| ≤ 2 * |u|^8 := by
  have hn : ‖(u:ℂ) * Complex.I‖ = |u| := by simp
  have h := Complex.exp_bound (x := (u:ℂ) * Complex.I) (by rw [hn]; exact hu) (n := 8) (by norm_num)
  rw [hn] at h
  have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, h2]; ring
  have h4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have h5 : Complex.I ^ 5 = Complex.I := by rw [pow_succ, h4]; ring
  have h6 : Complex.I ^ 6 = -1 := by rw [pow_succ, h5, Complex.I_mul_I]
  have h7 : Complex.I ^ 7 = -Complex.I := by rw [pow_succ, h6]; ring
  have hsum : (∑ m ∈ Finset.range 8, ((u:ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) =
      ((1 - u^2/2 + u^4/24 - u^6/720 : ℝ) : ℂ) + ((u - u^3/6 + u^5/120 - u^7/5040 : ℝ) : ℂ) * Complex.I := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, mul_pow, h2, h3, h4, h5, h6, h7,
      Nat.factorial]
    push_cast
    ring
  have he : Complex.exp ((u:ℂ) * Complex.I) = (Real.cos u : ℂ) + (Real.sin u : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [he, hsum] at h
  have hb : ‖(u:ℂ) * Complex.I‖ ^ 0 = 1 := by simp
  have hz : ((Real.cos u : ℂ) + (Real.sin u : ℂ) * Complex.I) -
      (((1 - u^2/2 + u^4/24 - u^6/720 : ℝ) : ℂ) + ((u - u^3/6 + u^5/120 - u^7/5040 : ℝ) : ℂ) * Complex.I) =
      ((Real.cos u - (1 - u^2/2 + u^4/24 - u^6/720) : ℝ) : ℂ) +
        ((Real.sin u - (u - u^3/6 + u^5/120 - u^7/5040) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hz] at h
  have h8 : (0:ℝ) ≤ |u|^8 := by positivity
  replace h := h.trans (show |u| ^ 8 * ((Nat.succ 8 : ℕ) * ((Nat.factorial 8 : ℕ) * (8:ℕ) : ℝ)⁻¹) ≤ 2 * |u|^8 by
    norm_num [Nat.factorial]; nlinarith)
  generalize (Real.cos u - (1 - u^2/2 + u^4/24 - u^6/720) : ℝ) = A at h ⊢
  generalize (Real.sin u - (u - u^3/6 + u^5/120 - u^7/5040) : ℝ) = B at h ⊢
  constructor
  · have := Complex.abs_re_le_norm ((A : ℂ) + (B : ℂ) * Complex.I)
    simp at this; linarith
  · have := Complex.abs_im_le_norm ((A : ℂ) + (B : ℂ) * Complex.I)
    simp at this; linarith

end S73WP

namespace S74WA
open Arxivmath_ph_0108008 S73WP

lemma small_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1 / 2) :
    |wronskP r + r ^ 2 / 5| ≤ 2400 * r ^ 4 := by
  have hu : |2 * r| ≤ 1 := by rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨hc, hs⟩ := tay (2 * r) hu
  rw [abs_of_pos (by linarith : (0:ℝ) < 2 * r)] at hc hs
  set ec := Real.cos (2 * r) - (1 - (2*r)^2/2 + (2*r)^4/24 - (2*r)^6/720) with hec
  set es := Real.sin (2 * r) - (2*r - (2*r)^3/6 + (2*r)^5/120 - (2*r)^7/5040) with hes
  have hr0 : r ≠ 0 := hr.ne'
  have key : wronskP r + r ^ 2 / 5 = 16 / 280 * r ^ 4 + (-3/2 * ec) / r ^ 2 + 3 * es / r ^ 3 := by
    rw [formula r hr, Real.cos_sq r, hec, hes]
    field_simp
    ring
  rw [key]
  have h1 : |(-3/2 * ec) / r ^ 2| ≤ 3/2 * 512 * r ^ 6 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < r ^ 2), div_le_iff₀ (by positivity)]
    norm_num
    nlinarith [hc]
  have h2 : |3 * es / r ^ 3| ≤ 3 * 512 * r ^ 5 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < r ^ 3), div_le_iff₀ (by positivity)]
    norm_num
    nlinarith [hs]
  have h3 : |16 / 280 * r ^ 4| ≤ r ^ 4 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith [pow_pos hr 4]
  have hr6 : r ^ 6 ≤ r ^ 4 := by
    have : r ^ 6 = r ^ 4 * r ^ 2 := by ring
    rw [this]; have : r ^ 2 ≤ 1 := by nlinarith
    nlinarith [pow_pos hr 4]
  have hr5 : r ^ 5 ≤ r ^ 4 := by
    have : r ^ 5 = r ^ 4 * r := by ring
    rw [this]; nlinarith [pow_pos hr 4]
  calc _ ≤ |16 / 280 * r ^ 4 + (-3/2 * ec) / r ^ 2| + |3 * es / r ^ 3| := abs_add_le _ _
    _ ≤ |16 / 280 * r ^ 4| + |(-3/2 * ec) / r ^ 2| + |3 * es / r ^ 3| := by
        gcongr; exact abs_add_le _ _
    _ ≤ 2400 * r ^ 4 := by nlinarith

lemma big_tendsto : Tendsto wronskP atTop (𝓝 1) := by
  have hev : (fun r => 1 - (3 + 3 * Real.cos r ^ 2) / r ^ 2 + 3 * Real.sin (2 * r) / r ^ 3) =ᶠ[atTop] wronskP := by
    filter_upwards [eventually_gt_atTop 0] with r hr
    exact (formula r hr).symm
  refine Tendsto.congr' hev ?_
  have hA : Tendsto (fun r : ℝ => (3 + 3 * Real.cos r ^ 2) / r ^ 2) atTop (𝓝 0) := by
    have h6 : Tendsto (fun r : ℝ => 6 / r ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
    refine squeeze_zero' ?_ ?_ h6
    · filter_upwards with r; positivity
    · filter_upwards [eventually_gt_atTop 0] with r hr
      gcongr; nlinarith [Real.cos_sq_le_one r]
  have hB : Tendsto (fun r : ℝ => 3 * Real.sin (2 * r) / r ^ 3) atTop (𝓝 0) := by
    have h6 : Tendsto (fun r : ℝ => 3 / r ^ 3) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop three_ne_zero)
    refine squeeze_zero_norm' ?_ h6
    filter_upwards [eventually_gt_atTop 0] with r hr
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < r ^ 3)]
    gcongr
    rw [abs_of_pos (by norm_num : (0:ℝ) < 3)]
    nlinarith [Real.abs_sin_le_one (2 * r)]
  have := (tendsto_const_nhds (x := (1:ℝ))).sub hA |>.add hB
  simpa using this

end S74WA

open Arxivmath_ph_0108008 S74WA in
theorem solution :
    (fun r => wronskP r + r ^ 2 / 5) =o[𝓝[>] 0] (fun r => r ^ 2) ∧
    (∀ᶠ r in 𝓝[>] 0, wronskP r < 0) ∧
    Tendsto wronskP atTop (𝓝 1) ∧ (∀ᶠ r in atTop, 0 < wronskP r) := by
  have hev : ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < r ∧ r < 1 / 200 := by
    have h1 : ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < r := self_mem_nhdsWithin
    have h2 : ∀ᶠ r in 𝓝[>] (0:ℝ), r < 1 / 200 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    exact h1.and h2
  refine ⟨?_, ?_, big_tendsto, (tendsto_order.1 big_tendsto).1 0 one_pos⟩
  · have hO : (fun r => wronskP r + r ^ 2 / 5) =O[𝓝[>] 0] (fun r : ℝ => r ^ 4) := by
      refine IsBigO.of_bound 2400 ?_
      filter_upwards [hev] with r ⟨hr, hr1⟩
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ 4)]
      exact small_bound r hr (by linarith)
    refine hO.trans_isLittleO ?_
    have : (fun r : ℝ => r ^ 4) =o[𝓝 0] (fun r : ℝ => r ^ 2) :=
      Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 4)
    exact this.mono nhdsWithin_le_nhds
  · filter_upwards [hev] with r ⟨hr, hr1⟩
    have := small_bound r hr (by linarith)
    have h4 : 2400 * r ^ 4 < r ^ 2 / 5 := by
      have : r ^ 4 = r ^ 2 * r ^ 2 := by ring
      rw [this]; have : r ^ 2 < 1 / 40000 := by nlinarith
      nlinarith [pow_pos hr 2]
    have := (abs_le.1 this).2
    linarith
