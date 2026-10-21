-- Prove2me | solution 1 for AVRideHail.IndepPlatform.eq240_nMin_log_derivative_bounds
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:11:07.768041+00:00
-- url     : https://prove2.me/submissions/2782cb4c-facb-4f3d-868c-758183e16874

import Mathlib
import Definitions.Def_AVRideHail_IndepPlatform_Model

set_option autoImplicit false
open AVRideHail.PureHV AVRideHail.IndepPlatform

lemma aTilde_pos' (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r) : 0 < aTilde P := by
  unfold aTilde
  have h1 : 0 < P.r ^ (1 / (P.r + 1)) * P.a ^ (1 / (P.r + 1)) := by positivity
  have h2 : 0 < P.r ^ (-P.r / (P.r + 1)) * P.a ^ (1 / (P.r + 1)) := by positivity
  linarith

lemma nMin_hasDeriv' (P : MarketParams) (d : ℝ) (hd : 0 < d) :
    HasDerivAt (nMin P)
      (aTilde P * ((1 / (P.r + 1)) * d ^ (1 / (P.r + 1) - 1)) + P.t2) d := by
  have h1 := Real.hasDerivAt_rpow_const (x := d) (p := 1 / (P.r + 1)) (Or.inl hd.ne')
  have h2 := (h1.const_mul (aTilde P)).add ((hasDerivAt_id d).const_mul P.t2)
  exact h2.congr_deriv (by ring)

theorem solution (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : 0 ≤ P.alpha)
    (d : ℝ) (hd : 0 < d) :
    1 / (2 * d) < deriv (AVRideHail.PureHV.nMin P) d / AVRideHail.PureHV.nMin P d ∧ deriv (AVRideHail.PureHV.nMin P) d / AVRideHail.PureHV.nMin P d < 1 / d := by
  have hder := nMin_hasDeriv' P d hd
  rw [hder.deriv]
  have hu : 0 < d ^ (1 / (P.r + 1)) := Real.rpow_pos_of_pos hd _
  have hA := aTilde_pos' P ha hr0
  rw [Real.rpow_sub_one hd.ne']
  have hn : nMin P d = aTilde P * d ^ (1 / (P.r + 1)) + P.t2 * d := rfl
  rw [hn]
  generalize d ^ (1 / (P.r + 1)) = u at hu ⊢
  have hs1 : 1 / (P.r + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hs2 : 1 / 2 < 1 / (P.r + 1) := by
    rw [div_lt_div_iff₀ (by norm_num) (by linarith)]; linarith
  generalize 1 / (P.r + 1) = s at hs1 hs2
  have hpos : 0 < aTilde P * u + P.t2 * d := by positivity
  have e1 : (aTilde P * (s * (u / d)) + P.t2) * d = aTilde P * s * u + P.t2 * d := by
    field_simp
  constructor
  · rw [div_lt_div_iff₀ (by positivity) hpos]
    have : (aTilde P * (s * (u / d)) + P.t2) * (2 * d) = 2 * (aTilde P * s * u + P.t2 * d) := by
      rw [← e1]; ring
    rw [this]
    nlinarith [mul_pos (mul_pos hA hu) (sub_pos.2 (by linarith : (1:ℝ) / 2 < s)), mul_pos ht2 hd]
  · rw [div_lt_div_iff₀ hpos hd]
    nlinarith [mul_pos (mul_pos hA hu) (sub_pos.2 hs1)]
