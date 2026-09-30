-- Prove2me | Definitions.Def_CK_CKLaneP_SeamDip
-- name    : CK_CKLaneP_SeamDip
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:08:36.444187+00:00
-- url     : https://prove2.me/theorems/8bc961b8-b1a0-40f3-b2ed-5336c675e7cf
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamDip` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamDip` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamDip` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamDip (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamDip.lean)

import Definitions.Def_CK_CKLaneP_ProfileBounds

-- ===== source module CKLaneP.SeamDip =====
section
/-
Lane P — dip bounds for stationary seam points.

* `seam_kbound_gen` : s(y*) ≥ s(y0) + (F(y*,E/2) − F(y0,E/2)) − (y* − y0)·Θ(y*/E)   (stationary y*)
* `F_diff_ge`       : F(y,E/2) − F(y0,E/2) ≥ (y−y0)Θ(y/E) − M(y−y0)²/(2E) from a Θ-slope bound M
* `seam_dip_M`      : s(y*) ≥ s(y0) − M(y*−y0)²/(2E)
* `theta_slope_small` : Θ(y) − Θ(x) ≤ PsiUB(da, dh)·(y − x) for 0 < x ≤ y ≤ x2 (dh = VD at 1/2)
* `seamDelta_le`    : Δ(y) ≤ (P/2)(f²−e²)/(2ef) + P·y/(1−S−y)   (profile ≤ P on the contacts)
* `seamDelta_ge`    : (P/2)·log(f/e) ≤ Δ(y)                          (profile ≥ P on the contacts)
* `xstar_le`        : y* ≤ A0·E/(θ̄/x̄ − λE)  when Θ(x̄) ≥ θ̄ > A0 + λ·y_hi
* `seam_no_stat`    : no stationary point when Θ(y_hi/E) < B0 ≤ Δ
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

theorem kAux_mono {S e f y0 ys : ℝ} (hS : 0 ≤ S) (he : 0 < e) (hf : 0 < f)
    (hy0 : 0 ≤ y0) (h0s : y0 < ys) (hS1 : S + ys < 1) :
    kAux S e f ys y0 ≤ kAux S e f ys ys := by
  have hh : 0 < (e + f) / 2 := by linarith
  have hys : 0 < ys := lt_of_le_of_lt hy0 h0s
  have hcont : ContinuousOn (kAux S e f ys) (Icc y0 ys) := by
    have h1 : ContinuousOn (seamCurve S e f) (Icc y0 ys) :=
      (continuousOn_seamCurve hS1 hys.le he hf).mono (Icc_subset_Icc hy0 le_rfl)
    have h2 : ContinuousOn (fun y => F y ((e + f) / 2)) (Icc y0 ys) :=
      (continuousOn_F_radius hh).mono (fun y hy => (show y ∈ Ici (0 : ℝ) from hy0.trans hy.1))
    have h3 : ContinuousOn (fun y : ℝ => y * seamDelta S e f ys) (Icc y0 ys) :=
      continuousOn_id.mul continuousOn_const
    exact (h1.sub h2).add h3
  have hmono : MonotoneOn (kAux S e f ys) (Icc y0 ys) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc y0 ys) hcont
    · intro y hy
      rw [interior_Icc] at hy
      have hy0' : 0 < y := lt_of_le_of_lt hy0 hy.1
      exact (hasDerivAt_kAux hS he hf hy0' (by linarith [hy.2])).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hy0' : 0 < y := lt_of_le_of_lt hy0 hy.1
      rw [(hasDerivAt_kAux hS he hf hy0' (by linarith [hy.2])).deriv, seamD_eq_sub]
      have hm := seamDelta_mono (S := S) he hf (by linarith) hy.2.le (by linarith)
      linarith
  exact hmono ⟨le_rfl, h0s.le⟩ ⟨h0s.le, le_rfl⟩ h0s.le

/-- General K-bound (no dropped terms). -/
theorem seam_kbound_gen {S e f y0 ys : ℝ} (hS : 0 ≤ S) (he : 0 < e) (hf : 0 < f)
    (hy0 : 0 ≤ y0) (h0s : y0 < ys) (hS1 : S + ys < 1) (hstat : seamD S e f ys = 0) :
    seamCurve S e f y0 + (F ys ((e + f) / 2) - F y0 ((e + f) / 2)) -
        (ys - y0) * e8Theta (ys / (e + f)) ≤ seamCurve S e f ys := by
  have hTD : e8Theta (ys / (e + f)) = seamDelta S e f ys := by
    have h := seamD_eq_sub S e f ys
    rw [hstat] at h
    linarith
  have key := kAux_mono hS he hf hy0 h0s hS1
  unfold kAux at key
  rw [hTD]
  linarith

/-- Lower bound for an increment of `F` from a slope bound on Θ. -/
theorem F_diff_ge {E y0 y M : ℝ} (hE : 0 < E) (hy0 : 0 ≤ y0) (h0y : y0 ≤ y)
    (hM : ∀ t ∈ Ioo y0 y, e8Theta (y / E) - e8Theta (t / E) ≤ M * ((y - t) / E)) :
    (y - y0) * e8Theta (y / E) - M * (y - y0) ^ 2 / (2 * E) ≤ F y (E / 2) - F y0 (E / 2) := by
  have hh : 0 < E / 2 := by linarith
  set T := e8Theta (y / E) with hT
  have hd : ∀ t ∈ Ioo y0 y, HasDerivAt (fun t => F t (E / 2) - t * T - M * (y - t) ^ 2 / (2 * E))
      (e8Theta (t / E) - T + M * ((y - t) / E)) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt hy0 ht.1
    have hF := hasDerivAt_F_theta ht0 hh
    have e2 : t / (2 * (E / 2)) = t / E := by ring_nf
    rw [e2] at hF
    have h2 := (hasDerivAt_id t).mul_const T
    have h3 := ((((hasDerivAt_id t).const_sub y).pow 2).const_mul M).div_const (2 * E)
    refine ((hF.sub h2).sub h3).congr_deriv ?_
    simp only [id_eq, Nat.cast_ofNat]
    field_simp
    ring
  have hcont : ContinuousOn (fun t => F t (E / 2) - t * T - M * (y - t) ^ 2 / (2 * E)) (Icc y0 y) := by
    have h1 : ContinuousOn (fun t => F t (E / 2)) (Icc y0 y) :=
      (continuousOn_F_radius hh).mono (fun t ht => (show t ∈ Ici (0 : ℝ) from hy0.trans ht.1))
    have h2 : ContinuousOn (fun t : ℝ => t * T) (Icc y0 y) := by fun_prop
    have h3 : ContinuousOn (fun t : ℝ => M * (y - t) ^ 2 / (2 * E)) (Icc y0 y) := by fun_prop
    exact (h1.sub h2).sub h3
  have hmono : MonotoneOn (fun t => F t (E / 2) - t * T - M * (y - t) ^ 2 / (2 * E)) (Icc y0 y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc y0 y) hcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t ht).deriv]
      have := hM t ht
      linarith
  have h := hmono ⟨le_rfl, h0y⟩ ⟨h0y, le_rfl⟩ h0y
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_div, sub_zero] at h
  nlinarith

/-- The dip bound with a Θ-slope constant `M`. -/
theorem seam_dip_M {S e f y0 ys M : ℝ} (hS : 0 ≤ S) (he : 0 < e) (hf : 0 < f)
    (hy0 : 0 ≤ y0) (h0s : y0 < ys) (hS1 : S + ys < 1) (hstat : seamD S e f ys = 0)
    (hM : ∀ t ∈ Ioo y0 ys, e8Theta (ys / (e + f)) - e8Theta (t / (e + f)) ≤ M * ((ys - t) / (e + f))) :
    seamCurve S e f y0 - M * (ys - y0) ^ 2 / (2 * (e + f)) ≤ seamCurve S e f ys := by
  have hE : 0 < e + f := by linarith
  have h1 := seam_kbound_gen hS he hf hy0 h0s hS1 hstat
  have h2 := F_diff_ge hE hy0 h0s.le hM
  linarith

/-- Θ-slope bound near the origin from a contact bracket `[da.v, 1/2]`. -/
theorem theta_slope_small {da dh : VD} (hda : da.Sound) (hdh : dh.Sound) (hk : 0 < dh.kapLo)
    (hh : dh.v = 1 / 2) {x2 : ℚ} (hA : 2 * x2 * da.Hhi ≤ 1 - 2 * da.v)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ (x2 : ℝ)) :
    e8Theta y - e8Theta x ≤ ((PsiUB da dh : ℚ) : ℝ) * (y - x) := by
  obtain ⟨x1, hx1a, hx1b⟩ := exists_rat_btwn hx
  have hx1 : (0 : ℚ) < x1 := by exact_mod_cast hx1a
  have hH0 : (0 : ℚ) ≤ dh.Hlo := by
    unfold VD.Hlo; apply div_nonneg (le_max_left _ _); unfold L2hiD; norm_num
  have hB : 1 - 2 * dh.v ≤ 2 * x1 * dh.Hlo := by
    rw [hh]; nlinarith
  exact theta_sub_le hda hdh hk hx1 hA hB hx1b.le hxy hy

/-- Upper bound of `Δ(y)` in the logarithmic form. -/
theorem seamDelta_le {S e f y P : ℝ} (he : 0 < e) (hef : e ≤ f) (hy : 0 ≤ y) (hS1 : S + y < 1)
    (hP0 : 0 ≤ P)
    (hP : ∀ t ∈ Icc ((1 - S - y) / (2 * f)) ((1 - S + y) / (2 * e)),
      profile (radialContact (2 * t) 1) ≤ P) :
    seamDelta S e f y ≤ P / 2 * ((f ^ 2 - e ^ 2) / (2 * e * f)) + P * (y / (1 - S - y)) := by
  have hf : 0 < f := lt_of_lt_of_le he hef
  have hA : 0 < 1 - S - y := by linarith
  have hB : 0 < 1 - S + y := by linarith
  have hX : 0 < (1 - S - y) / (2 * f) := by positivity
  have hXY : (1 - S - y) / (2 * f) ≤ (1 - S + y) / (2 * e) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (1 - S - y) * (2 * e) ≤ (1 - S + y) * (2 * e) := by nlinarith
    have h2 : (1 - S + y) * (2 * e) ≤ (1 - S + y) * (2 * f) := by nlinarith
    linarith
  have hlog := theta_log_le hX hXY hP
  -- log(X_e/X_f) = log(f/e) + log((1-S+y)/(1-S-y))
  have hratio : (1 - S + y) / (2 * e) / ((1 - S - y) / (2 * f)) =
      (f / e) * ((1 - S + y) / (1 - S - y)) := by
    field_simp
  rw [hratio, Real.log_mul (by positivity) (by positivity)] at hlog
  -- log(f/e) ≤ (f² − e²)/(2ef)
  have hfe : Real.log (f / e) ≤ (f ^ 2 - e ^ 2) / (2 * e * f) := by
    have hne : e ≠ 0 := he.ne'
    have hfne : f ≠ 0 := hf.ne'
    have hfe0 : f + e ≠ 0 := by linarith
    set t := (f - e) / (f + e) with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have ht1 : t < 1 := by rw [ht, div_lt_one (by linarith)]; linarith
    have h := log_ratio_le ht0 ht1
    have h1t : 1 + t = 2 * f / (f + e) := by rw [ht]; field_simp; ring
    have h2t : 1 - t = 2 * e / (f + e) := by rw [ht]; field_simp; ring
    have e1 : (1 + t) / (1 - t) = f / e := by
      rw [h1t, h2t]; field_simp
    have e2 : 2 * t / (1 - t ^ 2) = (f ^ 2 - e ^ 2) / (2 * e * f) := by
      rw [show 1 - t ^ 2 = (1 - t) * (1 + t) by ring, h1t, h2t, ht]
      field_simp
      ring
    rw [e1, e2] at h
    exact h
  -- log((1-S+y)/(1-S-y)) ≤ 2y/(1-S-y)
  have hy2 : Real.log ((1 - S + y) / (1 - S - y)) ≤ 2 * y / (1 - S - y) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 - S + y) / (1 - S - y) by positivity)
    have e : (1 - S + y) / (1 - S - y) - 1 = 2 * y / (1 - S - y) := by field_simp; ring
    linarith
  unfold seamDelta
  have hP2 : P * (Real.log (f / e) + Real.log ((1 - S + y) / (1 - S - y))) ≤
      P * ((f ^ 2 - e ^ 2) / (2 * e * f) + 2 * y / (1 - S - y)) :=
    mul_le_mul_of_nonneg_left (by linarith) hP0
  have e3 : P * ((f ^ 2 - e ^ 2) / (2 * e * f) + 2 * y / (1 - S - y)) / 2 =
      P / 2 * ((f ^ 2 - e ^ 2) / (2 * e * f)) + P * (y / (1 - S - y)) := by ring
  linarith

/-- Lower bound of `Δ(y)` in the logarithmic form. -/
theorem seamDelta_ge {S e f y P : ℝ} (he : 0 < e) (hef : e ≤ f) (hy : 0 ≤ y) (hS1 : S + y < 1)
    (hP0 : 0 ≤ P)
    (hP : ∀ t ∈ Icc ((1 - S - y) / (2 * f)) ((1 - S + y) / (2 * e)),
      P ≤ profile (radialContact (2 * t) 1)) :
    P / 2 * Real.log (f / e) ≤ seamDelta S e f y := by
  have hf : 0 < f := lt_of_lt_of_le he hef
  have hA : 0 < 1 - S - y := by linarith
  have hB : 0 < 1 - S + y := by linarith
  have hX : 0 < (1 - S - y) / (2 * f) := by positivity
  have hXY : (1 - S - y) / (2 * f) ≤ (1 - S + y) / (2 * e) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (1 - S - y) * (2 * e) ≤ (1 - S + y) * (2 * e) := by nlinarith
    have h2 : (1 - S + y) * (2 * e) ≤ (1 - S + y) * (2 * f) := by nlinarith
    linarith
  have hlog := theta_log_ge hX hXY hP
  have hratio : (1 - S + y) / (2 * e) / ((1 - S - y) / (2 * f)) =
      (f / e) * ((1 - S + y) / (1 - S - y)) := by
    field_simp
  rw [hratio, Real.log_mul (by positivity) (by positivity)] at hlog
  have hy2 : 0 ≤ Real.log ((1 - S + y) / (1 - S - y)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hA]; linarith
  unfold seamDelta
  have := mul_le_mul_of_nonneg_left hy2 hP0
  linarith

/-- Upper bound for the stationary point. -/
theorem xstar_le {S e f ys yhi A0 lam xb θb : ℝ} (he : 0 < e) (hf : 0 < f)
    (hstat : seamD S e f ys = 0) (hΔ : seamDelta S e f ys ≤ A0 + lam * ys)
    (hys : 0 < ys) (hyh : ys ≤ yhi) (hlam : 0 ≤ lam)
    (hxb : 0 < xb) (hθb : θb ≤ e8Theta xb) (hneed : A0 + lam * yhi < θb)
    (hden : lam * (e + f) < θb / xb) :
    ys ≤ A0 * (e + f) / (θb / xb - lam * (e + f)) := by
  have hE : 0 < e + f := by linarith
  have hTD : e8Theta (ys / (e + f)) = seamDelta S e f ys := by
    have h := seamD_eq_sub S e f ys
    rw [hstat] at h
    linarith
  have hlt : ys / (e + f) < xb := by
    by_contra hcon
    push Not at hcon
    have h1 := e8Theta_mono hxb hcon
    have : lam * ys ≤ lam * yhi := mul_le_mul_of_nonneg_left hyh hlam
    linarith
  have hyE : 0 < ys / (e + f) := div_pos hys hE
  have hr := theta_ge_ratio hyE hlt.le
  have hr2 : ys / (e + f) * (θb / xb) ≤ ys / (e + f) * (e8Theta xb / xb) := by
    apply mul_le_mul_of_nonneg_left _ hyE.le
    exact div_le_div_of_nonneg_right hθb hxb.le
  -- ys/E * (θb/xb) ≤ A0 + lam*ys
  have hmain : ys / (e + f) * (θb / xb) ≤ A0 + lam * ys := by linarith
  have hd : 0 < θb / xb - lam * (e + f) := by linarith
  rw [le_div_iff₀ hd]
  have e1 : ys / (e + f) * (θb / xb) * (e + f) = ys * (θb / xb) := by field_simp
  have := mul_le_mul_of_nonneg_right hmain hE.le
  nlinarith

/-- No stationary point below `y_hi` when `Θ(y_hi/E) < B0 ≤ Δ(y*)`. -/
theorem seam_no_stat {S e f ys yhi B0 : ℝ} (he : 0 < e) (hf : 0 < f)
    (hstat : seamD S e f ys = 0) (hys0 : 0 ≤ ys) (hyh : ys ≤ yhi)
    (hΔ : B0 ≤ seamDelta S e f ys) (hΘ : e8Theta (yhi / (e + f)) < B0) : False := by
  have hE : 0 < e + f := by linarith
  have hTD : e8Theta (ys / (e + f)) = seamDelta S e f ys := by
    have h := seamD_eq_sub S e f ys
    rw [hstat] at h
    linarith
  have hm := e8Theta_mono0 (div_nonneg hys0 hE.le) (div_le_div_of_nonneg_right hyh hE.le)
  linarith

end CKLaneP

end


