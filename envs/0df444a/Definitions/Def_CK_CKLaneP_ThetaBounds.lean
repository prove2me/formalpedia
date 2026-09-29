-- Prove2me | Definitions.Def_CK_CKLaneP_ThetaBounds
-- name    : CK_CKLaneP_ThetaBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:07:20.970732+00:00
-- url     : https://prove2.me/theorems/472f8ca5-7698-4968-9d9d-7e3d7e33700c
-- title:
--   Courtade–Kumar proof module `CKLaneP.ThetaBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.ThetaBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.ThetaBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.ThetaBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/ThetaBounds.lean)

import Definitions.Def_CK_GeneralCK_PureGapMiddleDeterministic
import Definitions.Def_CK_GeneralCK_Certificates_E8ThetaHigherDerivatives
import Definitions.Def_CK_CKLaneP_LogCheck

-- ===== source module CKLaneP.ThetaBounds =====
section
/-
Lane P — elementary bounds on the E8 radial slope `e8Theta` (Θ).

* `theta_eq_radialSlope`   : Θ(x) = radialSlope(v), v = radialContact (2x) 1.
* `theta_le_twelve`        : Θ(x) ≤ 12 x for 0 < x ≤ 2/25            (slope at the origin is 8/log 2 ≈ 11.54).
* `profile_log2_ge_one`    : 1 ≤ profile(v)·log 2 for 0 < v ≤ 13/100000 (i.e. x Θ'(x) ≥ 1/log 2 for large x).
* `theta_log_increment`    : log(Y/X)/log 2 ≤ Θ(Y) − Θ(X) for 300 ≤ X ≤ Y.
* `J_mul_le_H_sub`         : J b (b − a) ≤ H b − H a for 0 ≤ a ≤ b ≤ 1/2      (concavity of H).
* `log_half_one_add_ge`    : (r−1)/(r+1) ≤ log((1+r)/2) for 1 ≤ r.
All proofs are analytic; the only numerics are certified log enclosures (`logChk`, decided by the kernel).
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK Set
open GeneralCK.Certificates.Mixed

theorem log_two_gt : (6931 / 10000 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

theorem log_two_lt : Real.log 2 < (6932 / 10000 : ℝ) := by
  have := Real.log_two_lt_d9; linarith

/-- Θ is the radial slope at the unit-entropy contact. -/
theorem theta_eq_radialSlope {x : ℝ} (hx : 0 < x) :
    e8Theta x = radialSlope (radialContact (2 * x) 1) := by
  unfold e8Theta
  exact deriv_F_radius_slope (by positivity) (by norm_num)

/-- `log((1+t)/(1-t)) ≤ 2t/(1-t^2)` for `0 ≤ t < 1`. -/
theorem log_ratio_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Real.log ((1 + t) / (1 - t)) ≤ 2 * t / (1 - t ^ 2) := by
  have h := Real.log_div_le_sum_range_add ht0 ht1 0
  simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, pow_one] at h
  have e : 2 * t / (1 - t ^ 2) = 2 * (t / (1 - t ^ 2)) := by ring
  rw [e]
  linarith

/-- `kap v ≥ log 2` on `(0,1)`. -/
theorem kap_ge_log_two {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : Real.log 2 ≤ kap v := by
  unfold kap
  have hp : 0 < v * (1 - v) := mul_pos hv0 (by linarith)
  have hq : v * (1 - v) ≤ 1 / 4 := by nlinarith [sq_nonneg (v - 1 / 2)]
  have hl : Real.log (v * (1 - v)) ≤ Real.log (1 / 4) := Real.log_le_log hp hq
  have h4 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
    rw [show (1 / 4 : ℝ) = ((2 : ℝ) ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    push_cast; ring
  linarith

/-- `hn v ≤ log 2`. -/
theorem hn_le_log_two (v : ℝ) : hn v ≤ Real.log 2 := by
  rw [hn_eq_H_mul_log]
  have := H_le_one v
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- Near the origin the slope of Θ is below 12. -/
theorem theta_le_twelve {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 2 / 25) : e8Theta x ≤ 12 * x := by
  have hz : (0 : ℝ) < 2 * x := by positivity
  set v := radialContact (2 * x) 1 with hvdef
  have hv0 : 0 < v := radialContact_pos hz one_pos
  have hvh : v < 1 / 2 := radialContact_lt_half hz one_pos
  have heq : 2 * x * H v = 1 * (1 - 2 * v) := radialContact_equation hz one_pos
  have hv42 : (21 / 50 : ℝ) ≤ v := by
    rw [hvdef]
    apply (le_radialContact_iff hz one_pos (by norm_num) (by norm_num)).2
    have hH := H_le_one (21 / 50 : ℝ)
    have hH0 : 0 ≤ H (21 / 50 : ℝ) := H_nonneg (by norm_num) (by norm_num)
    nlinarith
  set t := 1 - 2 * v with htdef
  have ht0 : 0 < t := by linarith
  have ht1 : t ≤ 4 / 25 := by linarith
  have hHv1 : H v ≤ 1 := H_le_one v
  have hHv0 : 0 < H v := H_pos hv0 (by linarith)
  have h12 : 6 * t ≤ 12 * x := by nlinarith
  have hL := log_two_gt
  have hlog2 : 0 < Real.log 2 := by linarith
  have ht2 : 0 < 1 - t ^ 2 := by nlinarith
  -- first term
  have hJ : J v ≤ 2 * t / (1 - t ^ 2) / Real.log 2 := by
    have hratio : (1 - v) / v = (1 + t) / (1 - t) := by
      rw [htdef]; field_simp; ring
    unfold J
    rw [hratio]
    exact div_le_div_of_nonneg_right (log_ratio_le ht0.le (by linarith)) hlog2.le
  -- second term
  have hk := kap_ge_log_two hv0 (by linarith)
  have hkpos : 0 < kap v := by linarith
  have hhn := hn_le_log_two v
  have hhn0 : 0 ≤ hn v := by rw [hn_eq_H_mul_log]; positivity
  have hvv : 2 * v * (1 - v) = (1 - t ^ 2) / 2 := by rw [htdef]; ring
  have hT : (1 - 2 * v) * hn v / (2 * Real.log 2 * v * (1 - v) * kap v) ≤
      2 * t / (1 - t ^ 2) / Real.log 2 := by
    have hden : 2 * Real.log 2 * v * (1 - v) * kap v = Real.log 2 * kap v * ((1 - t ^ 2) / 2) := by
      rw [← hvv]; ring
    rw [hden, ← htdef]
    rw [div_le_div_iff₀ (by positivity) hlog2]
    have e1 : t * hn v * Real.log 2 ≤ t * Real.log 2 * Real.log 2 := by
      have := mul_le_mul_of_nonneg_left hhn ht0.le
      nlinarith
    have e2 : t * Real.log 2 * Real.log 2 ≤ t * Real.log 2 * kap v := by
      have := mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ t * Real.log 2)
      linarith
    have e3 : 2 * t / (1 - t ^ 2) * (Real.log 2 * kap v * ((1 - t ^ 2) / 2)) =
        t * Real.log 2 * kap v := by
      field_simp
    rw [e3]
    linarith
  -- combine
  rw [theta_eq_radialSlope hx, ← hvdef]
  unfold radialSlope
  have hsum : J v + (1 - 2 * v) * hn v / (2 * Real.log 2 * v * (1 - v) * kap v) ≤
      4 * t / ((1 - t ^ 2) * Real.log 2) := by
    have e4 : 2 * t / (1 - t ^ 2) / Real.log 2 + 2 * t / (1 - t ^ 2) / Real.log 2 =
        4 * t / ((1 - t ^ 2) * Real.log 2) := by
      field_simp; ring
    linarith
  have hfin : 4 * t / ((1 - t ^ 2) * Real.log 2) ≤ 6 * t := by
    rw [div_le_iff₀ (by positivity)]
    have htt : t ^ 2 ≤ 16 / 625 := by nlinarith
    have h1 : (609 / 625 : ℝ) * (6931 / 10000) ≤ (1 - t ^ 2) * Real.log 2 :=
      mul_le_mul (by linarith) (le_of_lt hL) (by norm_num) (by linarith)
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 6 * t by linarith)
    nlinarith
  linarith

/-- `-log(1-v)` is between `v` and `2v` on `[0, 1/2]`. -/
theorem neg_log_one_sub_bounds {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) :
    v ≤ -Real.log (1 - v) ∧ -Real.log (1 - v) ≤ 2 * v := by
  have hpos : 0 < 1 - v := by linarith
  constructor
  · have := Real.log_le_sub_one_of_pos hpos
    linarith
  · have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at h
    have hinv : (1 - v)⁻¹ - 1 ≤ 2 * v := by
      rw [inv_eq_one_div, div_sub_one hpos.ne', div_le_iff₀ hpos]
      nlinarith
    linarith

/-- `v (-log v)^3 ≤ 27`. -/
theorem mul_neg_log_cube_le {v : ℝ} (hv0 : 0 < v) :
    v * (-Real.log v) ^ 3 ≤ 27 := by
  set L := -Real.log v with hLdef
  by_cases hL : L ≤ 0
  · have : L ^ 3 ≤ 0 := by
      have := pow_le_pow_left₀ (le_refl (0:ℝ)) (show (0:ℝ) ≤ 0 from le_refl 0) 3
      nlinarith [sq_nonneg L]
    nlinarith
  push Not at hL
  have hexp : Real.exp L = v⁻¹ := by
    rw [hLdef, Real.exp_neg, Real.exp_log hv0]
  have h1 : L / 3 + 1 ≤ Real.exp (L / 3) := Real.add_one_le_exp (L / 3)
  have h2 : (L / 3) ≤ Real.exp (L / 3) := by linarith
  have h3 : (L / 3) ^ 3 ≤ Real.exp (L / 3) ^ 3 := pow_le_pow_left₀ (by linarith) h2 3
  have h4 : Real.exp (L / 3) ^ 3 = Real.exp L := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h4, hexp] at h3
  have h5 : v * (L / 3) ^ 3 ≤ v * v⁻¹ := mul_le_mul_of_nonneg_left h3 hv0.le
  rw [mul_inv_cancel₀ hv0.ne'] at h5
  nlinarith

/-- A certified lower bound `log(100000/13) ≥ 89/10`. -/
theorem log_big_ge : (89 / 10 : ℝ) ≤ Real.log (100000 / 13) := by
  have h := logChk_sound (q := 100000 / 13) (k := 12) (n := 12) (lo := 89 / 10) (hi := 9)
    (by decide +kernel)
  have e : ((100000 / 13 : ℚ) : ℝ) = (100000 / 13 : ℝ) := by push_cast; ring
  rw [e] at h
  have h1 := h.1
  push_cast at h1
  linarith

/-- The polynomial core of the profile estimate. -/
theorem profile_poly {L v : ℝ} (hL : 89 / 10 ≤ L) (hv0 : 0 < v) (hv1 : v ≤ 13 / 100000)
    (hvL : v * L ^ 3 ≤ 27) :
    (L + 2 * v) ^ 3 ≤ (1 - 2 * v) * (L + 1 - v) ^ 2 * (L - 1) := by
  have hP : (1 - 2 * v) * (L + 1 - v) ^ 2 * (L - 1) - (L + 2 * v) ^ 3 =
      -2 * (v * L ^ 3) + ((1 - 2 * v) ^ 2 - 6 * v) * L ^ 2 -
        ((1 - 2 * v) * (1 - v ^ 2) + 12 * v ^ 2) * L -
        ((1 - 2 * v) * (1 - v) ^ 2 + 8 * v ^ 3) := by ring
  have hA : (998 / 1000 : ℝ) ≤ (1 - 2 * v) ^ 2 - 6 * v := by nlinarith
  have hB : (1 - 2 * v) * (1 - v ^ 2) + 12 * v ^ 2 ≤ 1001 / 1000 := by nlinarith
  have hC : (1 - 2 * v) * (1 - v) ^ 2 + 8 * v ^ 3 ≤ 1001 / 1000 := by nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  have hAL : (998 / 1000 : ℝ) * L ^ 2 ≤ ((1 - 2 * v) ^ 2 - 6 * v) * L ^ 2 :=
    mul_le_mul_of_nonneg_right hA hL2
  have hBL : ((1 - 2 * v) * (1 - v ^ 2) + 12 * v ^ 2) * L ≤ (1001 / 1000) * L :=
    mul_le_mul_of_nonneg_right hB hL0
  have hQ : 0 ≤ (998 / 1000 : ℝ) * L ^ 2 - (1001 / 1000) * L - 1001 / 1000 - 54 := by
    nlinarith [mul_self_nonneg (L - 89 / 10)]
  nlinarith

/-- `x Θ'(x) ≥ 1/log 2` at small contacts, stated for the compact profile. -/
theorem profile_log2_ge_one {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 13 / 100000) :
    1 ≤ profile v * Real.log 2 := by
  have hvh : v ≤ 1 / 2 := by linarith
  set L := -Real.log v with hLdef
  have hLb : 89 / 10 ≤ L := by
    have hle : Real.log v ≤ Real.log (13 / 100000) := Real.log_le_log hv0 hv1
    have h13 : Real.log (13 / 100000 : ℝ) = -Real.log (100000 / 13) := by
      rw [show (13 / 100000 : ℝ) = (100000 / 13)⁻¹ by norm_num, Real.log_inv]
    have := log_big_ge
    rw [hLdef]; linarith
  have hvL := mul_neg_log_cube_le hv0
  rw [← hLdef] at hvL
  obtain ⟨hm1, hm2⟩ := neg_log_one_sub_bounds hv0.le hvh
  set m := -Real.log (1 - v) with hmdef
  have hlog1v : Real.log (1 - v) = -m := by rw [hmdef]; ring
  have hlogv : Real.log v = -L := by rw [hLdef]; ring
  have hhn : hn v = v * L + (1 - v) * m := by
    unfold hn; rw [hlog1v, hlogv]; ring
  have hkap : kap v = (L + m) / 2 := by
    unfold kap
    rw [Real.log_mul hv0.ne' (by linarith), hlog1v, hlogv]; ring
  have hhn_lo : v * (L + 1 - v) ≤ hn v := by
    rw [hhn]; nlinarith
  have hhn_nonneg : 0 ≤ v * (L + 1 - v) := by
    apply mul_nonneg hv0.le; linarith
  have hk_lo : L / 2 ≤ kap v := by rw [hkap]; linarith
  have hk_hi : kap v ≤ (L + 2 * v) / 2 := by rw [hkap]; linarith
  have hkpos : 0 < kap v := by linarith
  have hD : L - 1 ≤ 2 * kap v - (1 - 2 * v) ^ 2 := by
    have : (1 - 2 * v) ^ 2 ≤ 1 := by nlinarith
    linarith
  have hr : 0 ≤ 1 - 2 * v := by linarith
  have hnu : 4 * v * (1 - v) ≤ 4 * v := by nlinarith
  have hnu0 : 0 ≤ 4 * v * (1 - v) := by nlinarith
  have hpoly := profile_poly hLb hv0 hv1 hvL
  -- numerator lower bound
  have hnum : 2 * (1 - 2 * v) * (v * (L + 1 - v)) ^ 2 * (L - 1) ≤
      2 * (1 - 2 * v) * (hn v) ^ 2 * (2 * kap v - (1 - 2 * v) ^ 2) := by
    have h1 : (v * (L + 1 - v)) ^ 2 ≤ (hn v) ^ 2 := pow_le_pow_left₀ hhn_nonneg hhn_lo 2
    have h2 : 0 ≤ L - 1 := by linarith
    have h3 : (v * (L + 1 - v)) ^ 2 * (L - 1) ≤ (hn v) ^ 2 * (2 * kap v - (1 - 2 * v) ^ 2) :=
      mul_le_mul h1 hD h2 (sq_nonneg _)
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * (1 - 2 * v))
    nlinarith
  -- denominator upper bound
  have hden : (4 * v * (1 - v)) ^ 2 * (kap v) ^ 3 ≤ 16 * v ^ 2 * ((L + 2 * v) / 2) ^ 3 := by
    have h1 : (4 * v * (1 - v)) ^ 2 ≤ 16 * v ^ 2 := by
      have := pow_le_pow_left₀ hnu0 hnu 2
      nlinarith
    have h2 : (kap v) ^ 3 ≤ ((L + 2 * v) / 2) ^ 3 := pow_le_pow_left₀ hkpos.le hk_hi 3
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hmid : 16 * v ^ 2 * ((L + 2 * v) / 2) ^ 3 ≤ 2 * (1 - 2 * v) * (v * (L + 1 - v)) ^ 2 * (L - 1) := by
    have e : 16 * v ^ 2 * ((L + 2 * v) / 2) ^ 3 = 2 * v ^ 2 * (L + 2 * v) ^ 3 := by ring
    have e2 : 2 * (1 - 2 * v) * (v * (L + 1 - v)) ^ 2 * (L - 1) =
        2 * v ^ 2 * ((1 - 2 * v) * (L + 1 - v) ^ 2 * (L - 1)) := by ring
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left hpoly (by positivity)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdpos : 0 < Real.log 2 * (4 * v * (1 - v)) ^ 2 * (kap v) ^ 3 := by
    have : 0 < 4 * v * (1 - v) := by nlinarith
    positivity
  unfold profile
  rw [div_mul_eq_mul_div, le_div_iff₀ hdpos]
  nlinarith

/-- For `t ≥ 300` the unit contact is below `13/100000`. -/
theorem contact_small_of_large {t : ℝ} (ht : 300 ≤ t) :
    radialContact (2 * t) 1 ≤ 13 / 100000 := by
  have hz : (0 : ℝ) < 2 * t := by linarith
  apply (radialContact_le_iff hz one_pos (by norm_num) (by norm_num)).2
  -- need 1 * (1 - 2 * (13/100000)) ≤ 2 t * H (13/100000); suffices H(13/100000) ≥ 1/600
  have hv0 : (0 : ℝ) < 13 / 100000 := by norm_num
  set L := -Real.log (13 / 100000 : ℝ) with hLdef
  have hLb : 89 / 10 ≤ L := by
    have h13 : Real.log (13 / 100000 : ℝ) = -Real.log (100000 / 13) := by
      rw [show (13 / 100000 : ℝ) = (100000 / 13)⁻¹ by norm_num, Real.log_inv]
    have := log_big_ge
    rw [hLdef, h13]; linarith
  obtain ⟨hm1, _⟩ := neg_log_one_sub_bounds (v := 13 / 100000) (by norm_num) (by norm_num)
  have hhn : hn (13 / 100000) = (13 / 100000) * L + (1 - 13 / 100000) * (-Real.log (1 - 13 / 100000)) := by
    unfold hn; rw [hLdef]; ring
  have hhn_lo : (13 / 100000 : ℝ) * (89 / 10 + 1 - 13 / 100000) ≤ hn (13 / 100000) := by
    rw [hhn]; nlinarith
  have hH : H (13 / 100000) * Real.log 2 = hn (13 / 100000) := (hn_eq_H_mul_log _).symm
  have hl2 := log_two_lt
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hHge : (1 : ℝ) / 600 ≤ H (13 / 100000) := by
    by_contra hcon
    push Not at hcon
    have : H (13 / 100000) * Real.log 2 < (1 / 600) * (6932 / 10000) := by
      have h0 : 0 ≤ H (13 / 100000 : ℝ) := H_nonneg (by norm_num) (by norm_num)
      calc H (13 / 100000) * Real.log 2 ≤ (1 / 600) * Real.log 2 := by
            exact mul_le_mul_of_nonneg_right hcon.le hlog2.le
        _ < (1 / 600) * (6932 / 10000) := by nlinarith
    linarith
  nlinarith

/-- The logarithmic growth of Θ at large arguments. -/
theorem theta_log_increment {X Y : ℝ} (hX : 300 ≤ X) (hXY : X ≤ Y) :
    Real.log (Y / X) / Real.log 2 ≤ e8Theta Y - e8Theta X := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let g : ℝ → ℝ := fun t => e8Theta t - Real.log t / Real.log 2
  have hpos : ∀ t ∈ Ici (300 : ℝ), 0 < t := fun t ht => lt_of_lt_of_le (by norm_num) ht
  have hmono : MonotoneOn g (Ici 300) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 300)
    · have h1 : ContinuousOn e8Theta (Ici 300) :=
        continuousOn_e8Theta_pos.mono (fun t ht => hpos t ht)
      have h2 : ContinuousOn (fun t => Real.log t / Real.log 2) (Ici 300) :=
        (Real.continuousOn_log.mono (fun t ht => ne_of_gt (hpos t ht))).div_const _
      exact h1.sub h2
    · rw [interior_Ici]
      intro t ht
      have ht0 : 0 < t := lt_trans (by norm_num) ht
      exact ((hasDerivAt_e8Theta ht0).differentiableAt.sub
        ((Real.hasDerivAt_log ht0.ne').div_const _).differentiableAt).differentiableWithinAt
    · rw [interior_Ici]
      intro t ht
      have ht0 : 0 < t := lt_trans (by norm_num) ht
      have hd : HasDerivAt g (deriv e8Theta t - t⁻¹ / Real.log 2) t := by
        have h1 := (hasDerivAt_e8Theta ht0)
        have h2 := (Real.hasDerivAt_log ht0.ne').div_const (Real.log 2)
        have h3 := h1.sub h2
        rw [← deriv_e8Theta ht0] at h3
        exact h3
      rw [hd.deriv, deriv_e8Theta_eq_profile ht0]
      have hv := contact_small_of_large (le_of_lt (show (300 : ℝ) < t from ht))
      have hv0 : 0 < radialContact (2 * t) 1 := radialContact_pos (by positivity) one_pos
      have hp := profile_log2_ge_one hv0 hv
      have e : profile (radialContact (2 * t) 1) / t - t⁻¹ / Real.log 2 =
          (profile (radialContact (2 * t) 1) * Real.log 2 - 1) / (t * Real.log 2) := by
        field_simp
      rw [e]
      apply div_nonneg (by linarith) (by positivity)
  have hgle := hmono (show X ∈ Ici (300 : ℝ) from hX) (show Y ∈ Ici (300 : ℝ) from le_trans hX hXY) hXY
  simp only [g] at hgle
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  rw [Real.log_div hY0.ne' hX0.ne', sub_div]
  linarith

/-- Concavity of `H`: `J b (b - a) ≤ H b - H a` for `0 ≤ a ≤ b ≤ 1/2`. -/
theorem J_mul_le_H_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    J b * (b - a) ≤ H b - H a := by
  let φ : ℝ → ℝ := fun t => H t - J b * t
  have hmono : MonotoneOn φ (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact (H_continuous.continuousOn.sub (continuousOn_const.mul continuousOn_id))
    · rw [interior_Icc]
      intro t ht
      have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
      have ht1 : t < 1 := by linarith [ht.2]
      exact ((Comparison.hasDerivAt_H ht0 ht1).sub
        ((hasDerivAt_id t).const_mul (J b))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
      have ht1 : t < 1 := by linarith [ht.2]
      have hd : HasDerivAt (fun y => H y - J b * y) (J t - J b) t := by
        have h1 := Comparison.hasDerivAt_H ht0 ht1
        have h2 : HasDerivAt (fun y : ℝ => J b * y) (J b) t := by
          simpa using (hasDerivAt_id t).const_mul (J b)
        exact h1.sub h2
      show 0 ≤ deriv (fun y => H y - J b * y) t
      rw [hd.deriv]
      have := J_antitone ht0 hb ht.2.le
      linarith
  have h := hmono ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab
  simp only [φ] at h
  linarith

/-- `(r-1)/(r+1) ≤ log((1+r)/2)` for `1 ≤ r`. -/
theorem log_half_one_add_ge {r : ℝ} (hr : 1 ≤ r) :
    (r - 1) / (r + 1) ≤ Real.log ((1 + r) / 2) := by
  set x := (r - 1) / (r + 3) with hxdef
  have hx0 : 0 ≤ x := div_nonneg (by linarith) (by linarith)
  have hx1 : x < 1 := by rw [hxdef, div_lt_one (by linarith)]; linarith
  have h := Real.sum_range_le_log_div hx0 hx1 1
  simp only [Finset.range_one, Finset.sum_singleton, mul_zero, zero_add, pow_one,
    Nat.cast_zero, div_one] at h
  have hratio : (1 + x) / (1 - x) = (1 + r) / 2 := by
    rw [hxdef]; field_simp; ring
  rw [hratio] at h
  have h2 : (r - 1) / (r + 1) ≤ 2 * x := by
    rw [hxdef, div_le_iff₀ (by linarith)]
    rw [show 2 * ((r - 1) / (r + 3)) * (r + 1) = (r - 1) * (2 * (r + 1) / (r + 3)) by ring]
    have : 1 ≤ 2 * (r + 1) / (r + 3) := by rw [le_div_iff₀ (by linarith)]; linarith
    nlinarith
  linarith

end CKLaneP

end


