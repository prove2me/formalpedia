-- Prove2me | Definitions.Def_CK_CKLaneP_ThetaBulk
-- name    : CK_CKLaneP_ThetaBulk
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:26:16.998823+00:00
-- url     : https://prove2.me/theorems/16bf544a-9380-43d0-9865-f005d65e6262
-- title:
--   Courtade–Kumar proof module `CKLaneP.ThetaBulk` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.ThetaBulk` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.ThetaBulk` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.ThetaBulk (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/ThetaBulk.lean)

import Definitions.Def_CK_CKLaneP_SeamCore

-- ===== source module CKLaneP.ThetaBulk =====
section
/-
Lane P — quantitative convexity of `h ↦ Θ(Z/(2h))` in the small-entropy regime and the
equal-mean ("bulk") lower bound for the seam base.

Contact parametrization (`v = radialContact (2x) 1`, `x = Xv v`):
    Mv v = x²·Θ'(x) = (1−2v)²·hn·(2kap − (1−2v)²) / (16 v² (1−v)² kap³),   Xv v = (1−2v)/(2 H v).
* `Mv − (9/10)·Xv` is antitone on `(0, 1/10000]`: log-derivatives `v·lM ≤ −0.67`, `v·lX ≥ −1.0003`
  (L = −log v ≥ 9.21) and `profile ≥ 1/log 2` (`profile_log2_ge_one`).
* Hence `x ↦ x² Θ'(x)` increases at rate ≥ 9/10 once the contact is ≤ 1/10000, so
  `g ↦ Θ(1/g) − (C/2) g²` is convex for `C ≤ (9/10)/g_max²`, and
    jdef e f m = Θ(Z/2e) + Θ(Z/2f) − 2Θ(Z/(e+f)) ≥ (9/10)(f−e)²/(4f²).
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

noncomputable def Mv (v : ℝ) : ℝ :=
  (1 - 2 * v) ^ 2 * hn v * (2 * kap v - (1 - 2 * v) ^ 2) / (16 * v ^ 2 * (1 - v) ^ 2 * kap v ^ 3)

noncomputable def Xv (v : ℝ) : ℝ := (1 - 2 * v) / (2 * H v)

/-- Log-derivative of `Mv`. -/
noncomputable def lM (v : ℝ) : ℝ :=
  -4 / (1 - 2 * v) + J v * Real.log 2 / hn v +
    (2 * (-(1 - 2 * v) / (2 * v * (1 - v))) + 4 * (1 - 2 * v)) / (2 * kap v - (1 - 2 * v) ^ 2) -
    2 / v + 2 / (1 - v) - 3 * (-(1 - 2 * v) / (2 * v * (1 - v))) / kap v

/-- Log-derivative of `Xv`. -/
noncomputable def lX (v : ℝ) : ℝ := -2 / (1 - 2 * v) - J v / H v

theorem hn_pos' {v : ℝ} (hv : 0 < v) (hv1 : v < 1) : 0 < hn v := by
  rw [hn_eq_H_mul_log]; exact mul_pos (H_pos hv hv1) log_two_pos

theorem K2_pos {v : ℝ} (hv : 0 < v) (hv1 : v < 1 / 2) : 0 < 2 * kap v - (1 - 2 * v) ^ 2 := by
  have := kap_ge_log_two hv (by linarith)
  have hl : (1 : ℝ) / 2 < Real.log 2 := by linarith [log_two_gt]
  nlinarith

theorem hasDerivAt_Xv {v : ℝ} (hv : 0 < v) (hv1 : v < 1 / 2) :
    HasDerivAt Xv (Xv v * lX v) v := by
  have hH : 0 < H v := H_pos hv (by linarith)
  have hHd := Comparison.hasDerivAt_H hv (by linarith)
  have h := (((hasDerivAt_id v).const_mul 2).const_sub 1).div (hHd.const_mul 2) (by positivity)
  refine h.congr_deriv ?_
  unfold Xv lX
  simp only [id_eq]
  have h12 : 1 - 2 * v ≠ 0 := by linarith
  field_simp

theorem hasDerivAt_Mv {v : ℝ} (hv : 0 < v) (hv1 : v < 1 / 2) :
    HasDerivAt Mv (Mv v * lM v) v := by
  have hv1' : v < 1 := by linarith
  have hk : 0 < kap v := kap_pos hv hv1
  have hn0 : 0 < hn v := hn_pos' hv hv1'
  have hK2 := K2_pos hv hv1
  have hr := ((hasDerivAt_id v).const_mul 2).const_sub 1
  have hh := hasDerivAt_hn hv hv1'
  have hkd := hasDerivAt_kap hv hv1'
  have hnum := ((hr.pow 2).mul hh).mul ((hkd.const_mul 2).sub (hr.pow 2))
  have hden := ((((hasDerivAt_id v).pow 2).const_mul 16).mul
    (((hasDerivAt_id v).const_sub 1).pow 2)).mul (hkd.pow 3)
  have hdenne : 16 * v ^ 2 * (1 - v) ^ 2 * kap v ^ 3 ≠ 0 := by positivity
  have h := hnum.div hden (by simpa using hdenne)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
  unfold Mv lM
  have hvne : v ≠ 0 := hv.ne'
  have h1v : 1 - v ≠ 0 := by linarith
  have h12v : 1 - 2 * v ≠ 0 := by linarith
  have hkne : kap v ≠ 0 := hk.ne'
  have hnne : hn v ≠ 0 := hn0.ne'
  have hK2ne : 2 * kap v - (1 - 2 * v) ^ 2 ≠ 0 := hK2.ne'
  field_simp
  ring

/-- `Mv = Xv · profile`. -/
theorem Mv_eq_Xv_profile {v : ℝ} (hv : 0 < v) (hv1 : v < 1 / 2) : Mv v = Xv v * profile v := by
  have hH : 0 < H v := H_pos hv (by linarith)
  have hk : 0 < kap v := kap_pos hv hv1
  have hhn : hn v = H v * Real.log 2 := hn_eq_H_mul_log v
  have hL : 0 < Real.log 2 := log_two_pos
  unfold Mv Xv profile
  rw [hhn]
  have h1v : 1 - v ≠ 0 := by linarith
  field_simp
  ring

/-- `Mv` is `x² Θ'(x)` at the contact point, and `x = Xv(contact)`. -/
theorem Mv_eq {x : ℝ} (hx : 0 < x) :
    x ^ 2 * deriv e8Theta x = Mv (radialContact (2 * x) 1) ∧
      x = Xv (radialContact (2 * x) 1) := by
  set v := radialContact (2 * x) 1 with hvdef
  have hv0 : 0 < v := radialContact_pos (by positivity) one_pos
  have hvh : v < 1 / 2 := radialContact_lt_half (by positivity) one_pos
  have heq : 2 * x * H v = 1 * (1 - 2 * v) := radialContact_equation (by positivity) one_pos
  have hH : 0 < H v := H_pos hv0 (by linarith)
  have hxv : x = Xv v := by
    unfold Xv; field_simp; linarith
  refine ⟨?_, hxv⟩
  rw [deriv_e8Theta_eq_profile hx, ← hvdef, Mv_eq_Xv_profile hv0 hvh, ← hxv]
  field_simp

/-- `log 10000 ≥ 9.21` (certified). -/
theorem log_10000_ge : (921 / 100 : ℝ) ≤ Real.log 10000 := by
  have h := logChk_sound (q := 10000) (k := 13) (n := 20) (lo := 921 / 100) (hi := 10)
    (by decide +kernel)
  have e : ((10000 : ℚ) : ℝ) = 10000 := by norm_num
  have e2 : ((921 / 100 : ℚ) : ℝ) = 921 / 100 := by norm_num
  rw [e, e2] at h
  exact h.1

theorem neg_log_ge {v : ℝ} (hv : 0 < v) (hv0 : v ≤ 1 / 10000) : (921 / 100 : ℝ) ≤ -Real.log v := by
  have h1 : Real.log v ≤ Real.log (1 / 10000) := Real.log_le_log hv hv0
  have h2 : Real.log (1 / 10000 : ℝ) = -Real.log 10000 := by rw [one_div, Real.log_inv]
  linarith [log_10000_ge]

theorem lX_ge {v : ℝ} (hv : 0 < v) (hv0 : v ≤ 1 / 10000) : -(10003 / 10000) ≤ v * lX v := by
  have hv1 : v < 1 / 2 := by linarith
  have hH : 0 < H v := H_pos hv (by linarith)
  have hHJ : v * J v ≤ H v := by
    have := J_mul_le_H_sub (le_refl (0 : ℝ)) hv.le hv1.le
    simp only [H_zero, sub_zero] at this
    linarith
  have e1 : v * (J v / H v) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hH]; exact hHJ
  have e2 : v * (2 / (1 - 2 * v)) ≤ 3 / 10000 := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  unfold lX
  have : v * (-2 / (1 - 2 * v) - J v / H v) = -(v * (2 / (1 - 2 * v))) - v * (J v / H v) := by ring
  rw [this]
  linarith

theorem lM_le {v : ℝ} (hv : 0 < v) (hv0 : v ≤ 1 / 10000) : v * lM v ≤ -(67 / 100) := by
  have hv1 : v < 1 / 2 := by linarith
  have hv1' : v < 1 := by linarith
  have hk : 0 < kap v := kap_pos hv hv1
  have hn0 : 0 < hn v := hn_pos' hv hv1'
  have hK2 := K2_pos hv hv1
  have hL2 := log_two_pos
  have hLv := neg_log_ge hv hv0
  -- T2 ≤ 1 :  J·log2 ≤ -log v  and  hn ≥ v·(-log v)
  have hJlog : J v * Real.log 2 ≤ -Real.log v := by
    unfold J
    rw [div_mul_cancel₀ _ hL2.ne', Real.log_div (by linarith) hv.ne']
    have : Real.log (1 - v) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    linarith
  have hhn : v * (-Real.log v) ≤ hn v := by
    unfold hn
    have : 0 ≤ -(1 - v) * Real.log (1 - v) := by
      have := Real.log_nonpos (by linarith : (0 : ℝ) ≤ 1 - v) (by linarith)
      nlinarith
    linarith
  have hT2 : v * (J v * Real.log 2 / hn v) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hn0]
    have := mul_le_mul_of_nonneg_left hJlog hv.le
    linarith
  -- T3 ≤ 0
  have hT3 : v * ((2 * (-(1 - 2 * v) / (2 * v * (1 - v))) + 4 * (1 - 2 * v)) /
      (2 * kap v - (1 - 2 * v) ^ 2)) ≤ 0 := by
    rw [mul_div_assoc']
    apply div_nonpos_of_nonpos_of_nonneg _ hK2.le
    have e : v * (2 * (-(1 - 2 * v) / (2 * v * (1 - v))) + 4 * (1 - 2 * v)) =
        (1 - 2 * v) * (4 * v - 1 / (1 - v)) := by field_simp; ring
    rw [e]
    apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
    have : 1 ≤ 1 / (1 - v) := by rw [le_div_iff₀ (by linarith)]; linarith
    linarith
  -- T6 ≤ 3 / ((1-v) L)
  have hkapL : -Real.log v / 2 ≤ kap v := by
    unfold kap
    rw [Real.log_mul hv.ne' (by linarith)]
    have : Real.log (1 - v) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    linarith
  have hT6 : v * (-(3 * (-(1 - 2 * v) / (2 * v * (1 - v))) / kap v)) ≤ 3258 / 10000 := by
    have e : v * (-(3 * (-(1 - 2 * v) / (2 * v * (1 - v))) / kap v)) =
        3 * (1 - 2 * v) / (2 * (1 - v) * kap v) := by field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have hk2 : (921 / 200 : ℝ) ≤ kap v := by linarith
    nlinarith
  have hT1 : v * (-4 / (1 - 2 * v)) ≤ 0 := by
    rw [mul_div_assoc']; apply div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by linarith)
  have hT5 : v * (2 / (1 - v)) ≤ 3 / 10000 := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  have hT4 : v * (2 / v) = 2 := by field_simp
  unfold lM
  have e : v * (-4 / (1 - 2 * v) + J v * Real.log 2 / hn v +
      (2 * (-(1 - 2 * v) / (2 * v * (1 - v))) + 4 * (1 - 2 * v)) / (2 * kap v - (1 - 2 * v) ^ 2) -
      2 / v + 2 / (1 - v) - 3 * (-(1 - 2 * v) / (2 * v * (1 - v))) / kap v) =
      v * (-4 / (1 - 2 * v)) + v * (J v * Real.log 2 / hn v) +
      v * ((2 * (-(1 - 2 * v) / (2 * v * (1 - v))) + 4 * (1 - 2 * v)) /
        (2 * kap v - (1 - 2 * v) ^ 2)) - v * (2 / v) + v * (2 / (1 - v)) +
      v * (-(3 * (-(1 - 2 * v) / (2 * v * (1 - v))) / kap v)) := by ring
  rw [e]
  linarith

/-- `Mv − (9/10) Xv` is antitone on `[v1, 1/10000]` for every `v1 > 0`. -/
theorem Mv_sub_antitone {v1 : ℝ} (hv1 : 0 < v1) :
    AntitoneOn (fun v => Mv v - 9 / 10 * Xv v) (Icc v1 (1 / 10000)) := by
  have hder : ∀ v ∈ Icc v1 (1 / 10000), HasDerivAt (fun v => Mv v - 9 / 10 * Xv v)
      (Mv v * lM v - 9 / 10 * (Xv v * lX v)) v := by
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le hv1 hv.1
    have hvh : v < 1 / 2 := by linarith [hv.2]
    exact (hasDerivAt_Mv hv0 hvh).sub ((hasDerivAt_Xv hv0 hvh).const_mul (9 / 10))
  apply antitoneOn_of_deriv_nonpos (convex_Icc v1 (1 / 10000))
  · exact fun v hv => (hder v hv).continuousAt.continuousWithinAt
  · intro v hv; exact (hder v (interior_subset hv)).differentiableAt.differentiableWithinAt
  · intro v hv
    have hv' := interior_subset hv
    rw [(hder v hv').deriv]
    have hv0 : 0 < v := lt_of_lt_of_le hv1 hv'.1
    have hvh : v < 1 / 2 := by linarith [hv'.2]
    have hX : 0 < Xv v := by
      unfold Xv; have := H_pos hv0 (by linarith : v < 1); apply div_pos (by linarith) (by positivity)
    have hprof := profile_log2_ge_one hv0 (by linarith [hv'.2])
    have hL2 := log_two_pos
    have hLlt : Real.log 2 < 6932 / 10000 := log_two_lt
    have hlM := lM_le hv0 hv'.2
    have hlX := lX_ge hv0 hv'.2
    rw [Mv_eq_Xv_profile hv0 hvh]
    -- Xv·(profile·lM − 0.9 lX) ≤ 0
    have hkey : profile v * (v * lM v) ≤ 9 / 10 * (v * lX v) := by
      have hp : 1 / Real.log 2 ≤ profile v := by
        rw [div_le_iff₀ hL2]; linarith
      have h1 : profile v * (v * lM v) ≤ (1 / Real.log 2) * (v * lM v) :=
        mul_le_mul_of_nonpos_right hp (by linarith)
      have h2 : (1 / Real.log 2) * (v * lM v) ≤ (1 / Real.log 2) * (-(67 / 100)) :=
        mul_le_mul_of_nonneg_left hlM (by positivity)
      have h3 : (1 / Real.log 2) * (-(67 / 100)) ≤ -(9 / 10) * (10003 / 10000) := by
        rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hL2]; nlinarith
      nlinarith
    have : Xv v * profile v * lM v - 9 / 10 * (Xv v * lX v) =
        Xv v / v * (profile v * (v * lM v) - 9 / 10 * (v * lX v)) := by field_simp
    rw [this]
    apply mul_nonpos_of_nonneg_of_nonpos (div_nonneg hX.le hv0.le)
    linarith

/-- Rate of increase of `x² Θ'(x)` in the small-contact regime. -/
theorem sqDeriv_rate {xa xb : ℝ} (hxa : 0 < xa) (hab : xa ≤ xb)
    (hca : radialContact (2 * xa) 1 ≤ 1 / 10000) :
    9 / 10 * (xb - xa) ≤ xb ^ 2 * deriv e8Theta xb - xa ^ 2 * deriv e8Theta xa := by
  have hxb : 0 < xb := lt_of_lt_of_le hxa hab
  obtain ⟨ha1, ha2⟩ := Mv_eq hxa
  obtain ⟨hb1, hb2⟩ := Mv_eq hxb
  set va := radialContact (2 * xa) 1
  set vb := radialContact (2 * xb) 1
  have hvb0 : 0 < vb := radialContact_pos (by positivity) one_pos
  have hvba : vb ≤ va := by
    apply (radialContact_le_iff_ratio (by positivity) (by positivity) one_pos one_pos).2
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hanti := Mv_sub_antitone hvb0 ⟨le_rfl, hvba.trans hca⟩ ⟨hvba, hca⟩ hvba
  simp only at hanti
  rw [ha1, hb1]
  rw [← ha2, ← hb2] at hanti
  linarith

/-- The bulk integrand lower bound (convexity of `g ↦ Θ(1/g)` with rate). -/
theorem jdef_lower {e f m : ℝ} (he : 0 < e) (hef : e ≤ f) (hm : m < 1 / 2)
    (hcap : radialContact ((1 - 2 * m) / f) 1 ≤ 1 / 10000) :
    9 / 10 * (f - e) ^ 2 / (4 * f ^ 2) ≤ jdef e f m := by
  have hf : 0 < f := lt_of_lt_of_le he hef
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = 1 - 2 * m := ⟨_, rfl⟩
  have hZ0 : 0 < Z := by rw [hZ]; linarith
  rw [← hZ] at hcap
  have hZne : Z ≠ 0 := hZ0.ne'
  have hene : e ≠ 0 := he.ne'
  have hfne : f ≠ 0 := hf.ne'
  have hef0 : 0 < e + f := by linarith
  obtain ⟨g1, hg1d⟩ : ∃ g : ℝ, g = 2 * e / Z := ⟨_, rfl⟩
  obtain ⟨g2, hg2d⟩ : ∃ g : ℝ, g = (e + f) / Z := ⟨_, rfl⟩
  obtain ⟨g3, hg3d⟩ : ∃ g : ℝ, g = 2 * f / Z := ⟨_, rfl⟩
  have hg1 : 0 < g1 := by rw [hg1d]; exact div_pos (by linarith) hZ0
  have hg3 : 0 < g3 := by rw [hg3d]; exact div_pos (by linarith) hZ0
  have hg13 : g1 ≤ g3 := by
    rw [hg1d, hg3d]; exact div_le_div_of_nonneg_right (by linarith) hZ0.le
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 9 / 10 / g3 ^ 2 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun g => e8Theta (1 / g) - C / 2 * g ^ 2 := ⟨_, rfl⟩
  have hx1 : 1 / g1 = Z / (2 * e) := by rw [hg1d, one_div_div]
  have hx2 : 1 / g2 = Z / (e + f) := by rw [hg2d, one_div_div]
  have hx3 : 1 / g3 = Z / (2 * f) := by rw [hg3d, one_div_div]
  have hcap3 : radialContact (2 * (1 / g3)) 1 ≤ 1 / 10000 := by
    rw [hx3, mul_div_assoc', mul_div_mul_left _ _ (two_ne_zero)]; exact hcap
  -- derivative of G
  have hGd : ∀ g ∈ Icc g1 g3, HasDerivAt G (-(1 / g) ^ 2 * deriv e8Theta (1 / g) - C * g) g := by
    intro g hg
    have hg0 : 0 < g := lt_of_lt_of_le hg1 hg.1
    have hinv : HasDerivAt (fun g : ℝ => 1 / g) (-(1 / g) ^ 2) g := by
      have h := hasDerivAt_inv hg0.ne'
      have e1 : (fun y : ℝ => y⁻¹) = (fun g : ℝ => 1 / g) := by funext y; rw [one_div]
      have e2 : -(g ^ 2)⁻¹ = -(1 / g) ^ 2 := by rw [one_div, inv_pow]
      rw [e1, e2] at h; exact h
    have hT := (hasDerivAt_e8Theta (show 0 < 1 / g by positivity)).differentiableAt.hasDerivAt.comp g hinv
    have hq := ((hasDerivAt_id g).pow 2).const_mul (C / 2)
    rw [hG]
    refine (hT.sub hq).congr_deriv ?_
    simp only [id_eq, Nat.cast_ofNat]
    ring
  have hconv : ConvexOn ℝ (Icc g1 g3) G := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc g1 g3)
    · exact fun g hg => (hGd g hg).continuousAt.continuousWithinAt
    · intro g hg; exact (hGd g (interior_subset hg)).differentiableAt.differentiableWithinAt
    · intro u hu w hw huw
      have hu' := interior_subset hu
      have hw' := interior_subset hw
      rw [(hGd u hu').deriv, (hGd w hw').deriv]
      have hu0 : 0 < u := lt_of_lt_of_le hg1 hu'.1
      have hw0 : 0 < w := lt_of_lt_of_le hg1 hw'.1
      have hxw : 1 / g3 ≤ 1 / w := one_div_le_one_div_of_le hw0 hw'.2
      have hcw : radialContact (2 * (1 / w)) 1 ≤ 1 / 10000 := by
        have : radialContact (2 * (1 / w)) 1 ≤ radialContact (2 * (1 / g3)) 1 := by
          apply (radialContact_le_iff_ratio (by positivity) (by positivity) one_pos one_pos).2
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
        linarith
      have hrate := sqDeriv_rate (show 0 < 1 / w by positivity) (one_div_le_one_div_of_le hu0 huw) hcw
      have hdiff : (w - u) / g3 ^ 2 ≤ 1 / u - 1 / w := by
        rw [div_sub_div _ _ hu0.ne' hw0.ne', one_mul, mul_one]
        apply div_le_div₀ (by linarith) le_rfl (by positivity)
        have h1 : u * w ≤ g3 * g3 := mul_le_mul hu'.2 hw'.2 hw0.le hg3.le
        nlinarith
      have hCdef : C * w - C * u = 9 / 10 * ((w - u) / g3 ^ 2) := by rw [hC]; ring
      linarith
  -- midpoint inequality
  have hmid : (1 / 2 : ℝ) • g1 + (1 / 2 : ℝ) • g3 = g2 := by
    rw [smul_eq_mul, smul_eq_mul, hg1d, hg2d, hg3d]; ring
  have hJ := hconv.2 ⟨le_rfl, hg13⟩ ⟨hg13, le_rfl⟩ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [hmid, hG] at hJ
  simp only [smul_eq_mul] at hJ
  rw [hx1, hx2, hx3] at hJ
  unfold jdef
  rw [← hZ]
  have hsq : C / 2 * g1 ^ 2 + C / 2 * g3 ^ 2 - 2 * (C / 2 * g2 ^ 2) =
      9 / 10 * (f - e) ^ 2 / (4 * f ^ 2) := by
    rw [hC, hg1d, hg2d, hg3d]; field_simp; ring
  linarith

end CKLaneP

end


