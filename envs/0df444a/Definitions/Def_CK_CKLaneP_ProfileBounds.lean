-- Prove2me | Definitions.Def_CK_CKLaneP_ProfileBounds
-- name    : CK_CKLaneP_ProfileBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:59:09.224381+00:00
-- url     : https://prove2.me/theorems/3fbca270-d5d6-4cb3-a9a1-c53407cc2b2a
-- title:
--   Courtade–Kumar proof module `CKLaneP.ProfileBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.ProfileBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.ProfileBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.ProfileBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/ProfileBounds.lean)

import Definitions.Def_CK_CKLaneP_SeamK

-- ===== source module CKLaneP.ProfileBounds =====
section
/-
Lane P — sharp two-sided bounds on the contact profile `profile v = x·Θ'(x)` at small contacts
(`L = −log v`) and the logarithmic mean-value bounds for Θ they give.

* `profile_le_L` : profile v ≤ (L+1)²(L − (1−2v)²)/(log 2·(1−v)²·L³)        (0 < v ≤ 1/2, L ≥ 2)
* `profile_ge_L` : (1−2v)(L+1−v)²(L−1)/(log 2·(L+2v)³) ≤ profile v           (0 < v ≤ 1/2, L ≥ 1)
* `psiHi_anti`, `psiLo_mono`: monotonicity in `u = 1/L` (cubic polynomials) for brackets.
* `profile_le_bracket`, `profile_ge_bracket`: bounds for all `v` in a contact bracket.
* `theta_log_le`, `theta_log_ge`: `Θ(Y) − Θ(X)` vs `P·log(Y/X)` from profile bounds on `[X, Y]`.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

theorem one_sub_mul_neg_log_le {v : ℝ} (_hv0 : 0 ≤ v) (hv1 : v < 1) :
    (1 - v) * (-Real.log (1 - v)) ≤ v := by
  have hpos : 0 < 1 - v := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have e : (1 - v) * ((1 - v)⁻¹ - 1) = v := by
    rw [mul_sub, mul_inv_cancel₀ hpos.ne', mul_one]; ring
  have := mul_le_mul_of_nonneg_left h hpos.le
  linarith

theorem profile_eq_s {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) (hk : 0 < kap v) :
    profile v = (1 - 2 * v) * hn v ^ 2 * (2 * kap v - (1 - 2 * v) ^ 2) /
      (Real.log 2 * (v ^ 2 * (1 - v) ^ 2) * (2 * kap v) ^ 3) := by
  unfold profile
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h1 : 1 - v ≠ 0 := by linarith
  have hv : v ≠ 0 := hv0.ne'
  have hk' : kap v ≠ 0 := hk.ne'
  field_simp
  ring

/-- Upper profile bound in terms of `L = −log v`. -/
theorem profile_le_L {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1 / 2) (hL2 : 2 ≤ -Real.log v) :
    profile v ≤ (-Real.log v + 1) ^ 2 * (-Real.log v - (1 - 2 * v) ^ 2) /
      (Real.log 2 * (1 - v) ^ 2 * (-Real.log v) ^ 3) := by
  have hv1' : v < 1 := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = -Real.log v := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = -Real.log (1 - v) := ⟨_, rfl⟩
  rw [← hL]
  rw [← hL] at hL2
  have hm1 : v ≤ m := by rw [hm]; exact (neg_log_one_sub_bounds hv0.le hv1).1
  have hm3 : (1 - v) * m ≤ v := by rw [hm]; exact one_sub_mul_neg_log_le hv0.le hv1'
  have hhn : hn v = v * L + (1 - v) * m := by unfold hn; rw [hL, hm]; ring
  have hkap2 : 2 * kap v = L + m := by
    unfold kap; rw [Real.log_mul hv0.ne' (by linarith), hL, hm]; ring
  have hkpos : 0 < kap v := by have : 0 ≤ m := le_trans hv0.le hm1; linarith
  rw [profile_eq_s hv0 hv1' hkpos, hkap2]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hv1p : 0 < 1 - v := by linarith
  have hL0 : 0 < L := by linarith
  have hm0 : 0 ≤ m := le_trans hv0.le hm1
  have hs0 : 0 < L + m := by linarith
  have hc0 : 0 ≤ (1 - 2 * v) ^ 2 := sq_nonneg _
  have hc1 : (1 - 2 * v) ^ 2 ≤ 1 := by nlinarith
  have hr0 : 0 ≤ 1 - 2 * v := by linarith
  have hhn0 : 0 ≤ hn v := by rw [hhn]; positivity
  have hhn_hi : hn v ≤ v * (L + 1) := by rw [hhn]; nlinarith
  -- key: (s - c)/s³ ≤ (L - c)/L³ for s = L + m ≥ L ≥ 2
  have key : (L + m - (1 - 2 * v) ^ 2) / (L + m) ^ 3 ≤ (L - (1 - 2 * v) ^ 2) / L ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have fac : (L - (1 - 2 * v) ^ 2) * (L + m) ^ 3 - (L + m - (1 - 2 * v) ^ 2) * L ^ 3 =
        m * (L * (L + m) * (L + m + L) - (1 - 2 * v) ^ 2 *
          ((L + m) ^ 2 + (L + m) * L + L ^ 2)) := by ring
    have hq0 : 0 ≤ (L + m) ^ 2 + (L + m) * L + L ^ 2 := by positivity
    have hq : (L + m) ^ 2 + (L + m) * L + L ^ 2 ≤ L * (L + m) * (L + m + L) := by
      have h1 : 2 * ((L + m) * (L + m + L)) ≤ L * ((L + m) * (L + m + L)) :=
        mul_le_mul_of_nonneg_right hL2 (by positivity)
      nlinarith
    have h2 : 0 ≤ L * (L + m) * (L + m + L) - (1 - 2 * v) ^ 2 *
        ((L + m) ^ 2 + (L + m) * L + L ^ 2) := by
      have := mul_le_mul_of_nonneg_right hc1 hq0
      linarith
    nlinarith [mul_nonneg hm0 h2]
  have hA : (1 - 2 * v) * hn v ^ 2 ≤ v ^ 2 * (L + 1) ^ 2 := by
    have h1 : hn v ^ 2 ≤ (v * (L + 1)) ^ 2 := pow_le_pow_left₀ hhn0 hhn_hi 2
    have h2 : (1 - 2 * v) * hn v ^ 2 ≤ 1 * hn v ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    nlinarith
  have hB0 : 0 ≤ (L + m - (1 - 2 * v) ^ 2) / (L + m) ^ 3 := by
    apply div_nonneg _ (by positivity); linarith
  have e1 : (1 - 2 * v) * hn v ^ 2 * (L + m - (1 - 2 * v) ^ 2) /
      (Real.log 2 * (v ^ 2 * (1 - v) ^ 2) * (L + m) ^ 3) =
      ((1 - 2 * v) * hn v ^ 2) * ((L + m - (1 - 2 * v) ^ 2) / (L + m) ^ 3) /
        (Real.log 2 * v ^ 2 * (1 - v) ^ 2) := by
    field_simp
  have e2 : (L + 1) ^ 2 * (L - (1 - 2 * v) ^ 2) / (Real.log 2 * (1 - v) ^ 2 * L ^ 3) =
      (v ^ 2 * (L + 1) ^ 2) * ((L - (1 - 2 * v) ^ 2) / L ^ 3) /
        (Real.log 2 * v ^ 2 * (1 - v) ^ 2) := by
    field_simp
  rw [e1, e2]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul hA key hB0 (by positivity)

/-- Lower profile bound in terms of `L = −log v`. -/
theorem profile_ge_L {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1 / 2) (hL1 : 1 ≤ -Real.log v) :
    (1 - 2 * v) * (-Real.log v + 1 - v) ^ 2 * (-Real.log v - 1) /
      (Real.log 2 * (-Real.log v + 2 * v) ^ 3) ≤ profile v := by
  have hv1' : v < 1 := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = -Real.log v := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = -Real.log (1 - v) := ⟨_, rfl⟩
  rw [← hL]
  rw [← hL] at hL1
  obtain ⟨hm1, hm2⟩ := neg_log_one_sub_bounds hv0.le hv1
  rw [← hm] at hm1 hm2
  have hhn : hn v = v * L + (1 - v) * m := by unfold hn; rw [hL, hm]; ring
  have hkap2 : 2 * kap v = L + m := by
    unfold kap; rw [Real.log_mul hv0.ne' (by linarith), hL, hm]; ring
  have hkpos : 0 < kap v := by have : 0 ≤ m := le_trans hv0.le hm1; linarith
  rw [profile_eq_s hv0 hv1' hkpos, hkap2]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hv1p : 0 < 1 - v := by linarith
  have hL0 : 0 < L := by linarith
  have hm0 : 0 ≤ m := le_trans hv0.le hm1
  have hr0 : 0 ≤ 1 - 2 * v := by linarith
  have hc1 : (1 - 2 * v) ^ 2 ≤ 1 := by nlinarith
  have hhn_lo : v * (L + 1 - v) ≤ hn v := by rw [hhn]; nlinarith
  have hlo0 : 0 ≤ v * (L + 1 - v) := by apply mul_nonneg hv0.le; linarith
  -- numerator: (1-2v) (v(L+1-v))² (L-1) ≤ (1-2v) hn² (s - c)
  have hN : (1 - 2 * v) * (v * (L + 1 - v)) ^ 2 * (L - 1) ≤
      (1 - 2 * v) * hn v ^ 2 * (L + m - (1 - 2 * v) ^ 2) := by
    have h1 : (v * (L + 1 - v)) ^ 2 ≤ hn v ^ 2 := pow_le_pow_left₀ hlo0 hhn_lo 2
    have h2 : L - 1 ≤ L + m - (1 - 2 * v) ^ 2 := by linarith
    have h3 := mul_le_mul h1 h2 (by linarith) (sq_nonneg _)
    have h4 := mul_le_mul_of_nonneg_left h3 hr0
    nlinarith
  -- denominator: v²(1-v)²(L+m)³ ≤ v²(L+2v)³
  have hD : v ^ 2 * (1 - v) ^ 2 * (L + m) ^ 3 ≤ v ^ 2 * (L + 2 * v) ^ 3 := by
    have h1 : (1 - v) ^ 2 ≤ 1 := by nlinarith
    have h2 : (L + m) ^ 3 ≤ (L + 2 * v) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    have h3 : (1 - v) ^ 2 * (L + m) ^ 3 ≤ 1 * (L + 2 * v) ^ 3 :=
      mul_le_mul h1 h2 (by positivity) (by norm_num)
    nlinarith [sq_nonneg v]
  have hNpos : 0 ≤ (1 - 2 * v) * (v * (L + 1 - v)) ^ 2 * (L - 1) := by
    apply mul_nonneg (mul_nonneg hr0 (sq_nonneg _)); linarith
  have e1 : (1 - 2 * v) * (L + 1 - v) ^ 2 * (L - 1) / (Real.log 2 * (L + 2 * v) ^ 3) =
      ((1 - 2 * v) * (v * (L + 1 - v)) ^ 2 * (L - 1)) /
        (Real.log 2 * (v ^ 2 * (L + 2 * v) ^ 3)) := by
    field_simp
  rw [e1]
  have hden_pos : 0 < Real.log 2 * (v ^ 2 * (1 - v) ^ 2) * (L + m) ^ 3 := by positivity
  calc ((1 - 2 * v) * (v * (L + 1 - v)) ^ 2 * (L - 1)) / (Real.log 2 * (v ^ 2 * (L + 2 * v) ^ 3))
      ≤ ((1 - 2 * v) * (v * (L + 1 - v)) ^ 2 * (L - 1)) /
          (Real.log 2 * (v ^ 2 * (1 - v) ^ 2) * (L + m) ^ 3) := by
        apply div_le_div_of_nonneg_left hNpos hden_pos
        have := mul_le_mul_of_nonneg_left hD hlog2.le
        nlinarith
    _ ≤ (1 - 2 * v) * hn v ^ 2 * (L + m - (1 - 2 * v) ^ 2) /
          (Real.log 2 * (v ^ 2 * (1 - v) ^ 2) * (L + m) ^ 3) :=
        div_le_div_of_nonneg_right hN hden_pos.le

/-! ### Monotonicity in `u = 1/L` -/

/-- `(1+u)²(1−cu)` is increasing on `[0, 1/4]` for `0 ≤ c ≤ 1`. -/
theorem psiHi_poly_mono {c u u' : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu : 0 ≤ u) (huu : u ≤ u')
    (hu' : u' ≤ 1 / 4) : (1 + u) ^ 2 * (1 - c * u) ≤ (1 + u') ^ 2 * (1 - c * u') := by
  have fac : (1 + u') ^ 2 * (1 - c * u') - (1 + u) ^ 2 * (1 - c * u) =
      (u' - u) * ((2 - c) + (1 - 2 * c) * (u + u') - c * (u ^ 2 + u * u' + u' ^ 2)) := by ring
  have hQ : 0 ≤ (2 - c) + (1 - 2 * c) * (u + u') - c * (u ^ 2 + u * u' + u' ^ 2) := by
    have h1 : -(u + u') ≤ (1 - 2 * c) * (u + u') := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 - 2 * c by linarith) (show 0 ≤ u + u' by linarith)]
    have h2 : c * (u ^ 2 + u * u' + u' ^ 2) ≤ 3 / 16 := by
      have : u ^ 2 + u * u' + u' ^ 2 ≤ 3 / 16 := by nlinarith
      nlinarith
    linarith
  nlinarith [mul_nonneg (sub_nonneg.2 huu) hQ]

/-- `(1+(1−w)u)²(1−u)` is increasing on `[0, 1/4]` for `0 ≤ w ≤ 1/100`. -/
theorem psiLo_poly_mono {w u u' : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 100) (hu : 0 ≤ u) (huu : u ≤ u')
    (hu' : u' ≤ 1 / 4) :
    (1 + (1 - w) * u) ^ 2 * (1 - u) ≤ (1 + (1 - w) * u') ^ 2 * (1 - u') := by
  set a := 1 - w with ha
  have ha0 : 99 / 100 ≤ a := by rw [ha]; linarith
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  have fac : (1 + a * u') ^ 2 * (1 - u') - (1 + a * u) ^ 2 * (1 - u) =
      (u' - u) * ((2 * a - 1) + (a ^ 2 - 2 * a) * (u + u') - a ^ 2 * (u ^ 2 + u * u' + u' ^ 2)) := by
    ring
  have hQ : 0 ≤ (2 * a - 1) + (a ^ 2 - 2 * a) * (u + u') - a ^ 2 * (u ^ 2 + u * u' + u' ^ 2) := by
    have h1 : -(u + u') ≤ (a ^ 2 - 2 * a) * (u + u') := by
      nlinarith [mul_nonneg (sq_nonneg (a - 1)) (show 0 ≤ u + u' by linarith)]
    have h2 : a ^ 2 * (u ^ 2 + u * u' + u' ^ 2) ≤ 3 / 16 := by
      have : u ^ 2 + u * u' + u' ^ 2 ≤ 3 / 16 := by nlinarith
      have : a ^ 2 ≤ 1 := by nlinarith
      nlinarith
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 huu) hQ]

/-! ### Bracket bounds -/

/-- Upper profile bound on a bracket `0 < v ≤ vb`, from any `4 ≤ Lb ≤ −log vb`. -/
theorem profile_le_bracket {v vb Lb : ℝ} (hv0 : 0 < v) (hvb : v ≤ vb) (hvb1 : vb ≤ 1 / 1000)
    (hLb4 : 4 ≤ Lb) (hLb : Lb ≤ -Real.log vb) :
    profile v ≤ (1 + 1 / Lb) ^ 2 * (1 - (1 - 2 * vb) ^ 2 / Lb) / (Real.log 2 * (1 - vb) ^ 2) := by
  have hvb0 : 0 < vb := lt_of_lt_of_le hv0 hvb
  have hLv : -Real.log vb ≤ -Real.log v := by
    have := Real.log_le_log hv0 hvb; linarith
  set L := -Real.log v with hLdef
  have hL4 : 4 ≤ L := le_trans hLb4 (le_trans hLb hLv)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := profile_le_L hv0 (by linarith) (by linarith)
  have hL0 : 0 < L := by linarith
  have hLb0 : 0 < Lb := by linarith
  -- rewrite in u = 1/L
  have e1 : (L + 1) ^ 2 * (L - (1 - 2 * v) ^ 2) / (Real.log 2 * (1 - v) ^ 2 * L ^ 3) =
      (1 + 1 / L) ^ 2 * (1 - (1 - 2 * v) ^ 2 * (1 / L)) / (Real.log 2 * (1 - v) ^ 2) := by
    field_simp
  rw [e1] at h1
  have hcv : (1 - 2 * vb) ^ 2 ≤ (1 - 2 * v) ^ 2 := by nlinarith
  have hcb0 : 0 ≤ (1 - 2 * vb) ^ 2 := sq_nonneg _
  have hcb1 : (1 - 2 * vb) ^ 2 ≤ 1 := by nlinarith
  have hu : 1 / L ≤ 1 / Lb := one_div_le_one_div_of_le hLb0 (le_trans hLb hLv)
  have hu0 : 0 ≤ 1 / L := by positivity
  have hub : 1 / Lb ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hLb4
  have hmono := psiHi_poly_mono hcb0 hcb1 hu0 hu hub
  have hstep : (1 + 1 / L) ^ 2 * (1 - (1 - 2 * v) ^ 2 * (1 / L)) ≤
      (1 + 1 / L) ^ 2 * (1 - (1 - 2 * vb) ^ 2 * (1 / L)) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have := mul_le_mul_of_nonneg_right hcv hu0
    linarith
  have hnum0 : 0 ≤ (1 + 1 / Lb) ^ 2 * (1 - (1 - 2 * vb) ^ 2 / Lb) := by
    apply mul_nonneg (sq_nonneg _)
    rw [sub_nonneg, div_le_one hLb0]; linarith
  have hden : Real.log 2 * (1 - vb) ^ 2 ≤ Real.log 2 * (1 - v) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hlog2.le
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  have hdenb : 0 < Real.log 2 * (1 - vb) ^ 2 := by
    have : 0 < 1 - vb := by linarith
    positivity
  calc profile v ≤ (1 + 1 / L) ^ 2 * (1 - (1 - 2 * v) ^ 2 * (1 / L)) / (Real.log 2 * (1 - v) ^ 2) := h1
    _ ≤ (1 + 1 / Lb) ^ 2 * (1 - (1 - 2 * vb) ^ 2 / Lb) / (Real.log 2 * (1 - v) ^ 2) := by
        apply div_le_div_of_nonneg_right _ (le_trans hdenb.le hden)
        rw [div_eq_mul_one_div ((1 - 2 * vb) ^ 2) Lb]
        linarith
    _ ≤ (1 + 1 / Lb) ^ 2 * (1 - (1 - 2 * vb) ^ 2 / Lb) / (Real.log 2 * (1 - vb) ^ 2) :=
        div_le_div_of_nonneg_left hnum0 hdenb hden

/-- Lower profile bound on a bracket `va ≤ v ≤ vb ≤ 1/1000`, from `−log va ≤ La`, `4 ≤ −log vb`. -/
theorem profile_ge_bracket {v va vb La : ℝ} (hva0 : 0 < va) (hvav : va ≤ v) (hvb : v ≤ vb)
    (hvb1 : vb ≤ 1 / 1000) (hLa : -Real.log va ≤ La) (hL4 : 4 ≤ -Real.log vb) :
    (1 - 2 * vb) * (1 + (1 - vb) * (1 / La)) ^ 2 * (1 - 1 / La) /
      ((1 + vb / 2) ^ 3 * Real.log 2) ≤ profile v := by
  have hv0 : 0 < v := lt_of_lt_of_le hva0 hvav
  have hvb0 : 0 < vb := lt_of_lt_of_le hv0 hvb
  have hLv : -Real.log vb ≤ -Real.log v := by
    have := Real.log_le_log hv0 hvb; linarith
  have hLva : -Real.log v ≤ -Real.log va := by
    have := Real.log_le_log hva0 hvav; linarith
  set L := -Real.log v with hLdef
  have hL4' : 4 ≤ L := le_trans hL4 hLv
  have hLLa : L ≤ La := le_trans hLva hLa
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 < L := by linarith
  have hLa0 : 0 < La := by linarith
  have h1 := profile_ge_L hv0 (by linarith) (by linarith)
  -- monotone in v: (1-2v) ≥ (1-2vb), (L+1-v) ≥ (L+1-vb), (L+2v) ≤ (L+2vb) ≤ L(1+vb/2)
  have hstep1 : (1 - 2 * vb) * (L + 1 - vb) ^ 2 * (L - 1) / (Real.log 2 * (L * (1 + vb / 2)) ^ 3) ≤
      (1 - 2 * v) * (L + 1 - v) ^ 2 * (L - 1) / (Real.log 2 * (L + 2 * v) ^ 3) := by
    have hn1 : (1 - 2 * vb) * (L + 1 - vb) ^ 2 * (L - 1) ≤ (1 - 2 * v) * (L + 1 - v) ^ 2 * (L - 1) := by
      have a1 : 1 - 2 * vb ≤ 1 - 2 * v := by linarith
      have a2 : (L + 1 - vb) ^ 2 ≤ (L + 1 - v) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      have a3 := mul_le_mul a1 a2 (sq_nonneg _) (by linarith)
      exact mul_le_mul_of_nonneg_right a3 (by linarith)
    have hn0 : 0 ≤ (1 - 2 * vb) * (L + 1 - vb) ^ 2 * (L - 1) := by
      apply mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)); linarith
    have hd1 : Real.log 2 * (L + 2 * v) ^ 3 ≤ Real.log 2 * (L * (1 + vb / 2)) ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ hlog2.le
      apply pow_le_pow_left₀ (by linarith)
      nlinarith
    have hd0 : 0 < Real.log 2 * (L + 2 * v) ^ 3 := by positivity
    calc (1 - 2 * vb) * (L + 1 - vb) ^ 2 * (L - 1) / (Real.log 2 * (L * (1 + vb / 2)) ^ 3)
        ≤ (1 - 2 * vb) * (L + 1 - vb) ^ 2 * (L - 1) / (Real.log 2 * (L + 2 * v) ^ 3) :=
          div_le_div_of_nonneg_left hn0 hd0 hd1
      _ ≤ (1 - 2 * v) * (L + 1 - v) ^ 2 * (L - 1) / (Real.log 2 * (L + 2 * v) ^ 3) :=
          div_le_div_of_nonneg_right hn1 hd0.le
  -- rewrite in u = 1/L and use monotonicity in u (u ≥ 1/La)
  have e1 : (1 - 2 * vb) * (L + 1 - vb) ^ 2 * (L - 1) / (Real.log 2 * (L * (1 + vb / 2)) ^ 3) =
      (1 - 2 * vb) * ((1 + (1 - vb) * (1 / L)) ^ 2 * (1 - 1 / L)) /
        ((1 + vb / 2) ^ 3 * Real.log 2) := by
    field_simp
    ring
  rw [e1] at hstep1
  have hu : 1 / La ≤ 1 / L := one_div_le_one_div_of_le hL0 hLLa
  have hua0 : 0 ≤ 1 / La := by positivity
  have hu4 : 1 / L ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hL4'
  have hmono := psiLo_poly_mono (w := vb) hvb0.le (by linarith) hua0 hu hu4
  have hdpos : 0 < (1 + vb / 2) ^ 3 * Real.log 2 := by positivity
  have hr0 : 0 ≤ 1 - 2 * vb := by linarith
  calc (1 - 2 * vb) * (1 + (1 - vb) * (1 / La)) ^ 2 * (1 - 1 / La) / ((1 + vb / 2) ^ 3 * Real.log 2)
      = (1 - 2 * vb) * ((1 + (1 - vb) * (1 / La)) ^ 2 * (1 - 1 / La)) /
          ((1 + vb / 2) ^ 3 * Real.log 2) := by ring
    _ ≤ (1 - 2 * vb) * ((1 + (1 - vb) * (1 / L)) ^ 2 * (1 - 1 / L)) /
          ((1 + vb / 2) ^ 3 * Real.log 2) := by
        apply div_le_div_of_nonneg_right _ hdpos.le
        exact mul_le_mul_of_nonneg_left hmono hr0
    _ ≤ profile v := le_trans hstep1 h1

/-! ### Logarithmic mean-value bounds for Θ -/

theorem theta_log_le {X Y P : ℝ} (hX : 0 < X) (hXY : X ≤ Y)
    (hP : ∀ t ∈ Icc X Y, profile (radialContact (2 * t) 1) ≤ P) :
    e8Theta Y - e8Theta X ≤ P * Real.log (Y / X) := by
  have hpos : ∀ t ∈ Icc X Y, 0 < t := fun t ht => lt_of_lt_of_le hX ht.1
  have hd : ∀ t ∈ Icc X Y, HasDerivAt (fun t => P * Real.log t - e8Theta t)
      (P * t⁻¹ - deriv e8Theta t) t := by
    intro t ht
    have ht0 := hpos t ht
    exact ((Real.hasDerivAt_log ht0.ne').const_mul P).sub
      (hasDerivAt_e8Theta ht0).differentiableAt.hasDerivAt
  have hcont : ContinuousOn (fun t => P * Real.log t - e8Theta t) (Icc X Y) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hmono : MonotoneOn (fun t => P * Real.log t - e8Theta t) (Icc X Y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc X Y) hcont
    · intro t ht; exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      have ht0 := hpos t ht'
      rw [(hd t ht').deriv, deriv_e8Theta_eq_profile ht0]
      have hp := hP t ht'
      have e : P * t⁻¹ - profile (radialContact (2 * t) 1) / t =
          (P - profile (radialContact (2 * t) 1)) / t := by field_simp
      rw [e]
      apply div_nonneg (by linarith) ht0.le
  have h := hmono ⟨le_rfl, hXY⟩ ⟨hXY, le_rfl⟩ hXY
  simp only at h
  have hY0 : 0 < Y := lt_of_lt_of_le hX hXY
  rw [Real.log_div hY0.ne' hX.ne']
  linarith

theorem theta_log_ge {X Y P : ℝ} (hX : 0 < X) (hXY : X ≤ Y)
    (hP : ∀ t ∈ Icc X Y, P ≤ profile (radialContact (2 * t) 1)) :
    P * Real.log (Y / X) ≤ e8Theta Y - e8Theta X := by
  have hpos : ∀ t ∈ Icc X Y, 0 < t := fun t ht => lt_of_lt_of_le hX ht.1
  have hd : ∀ t ∈ Icc X Y, HasDerivAt (fun t => e8Theta t - P * Real.log t)
      (deriv e8Theta t - P * t⁻¹) t := by
    intro t ht
    have ht0 := hpos t ht
    exact (hasDerivAt_e8Theta ht0).differentiableAt.hasDerivAt.sub
      ((Real.hasDerivAt_log ht0.ne').const_mul P)
  have hcont : ContinuousOn (fun t => e8Theta t - P * Real.log t) (Icc X Y) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hmono : MonotoneOn (fun t => e8Theta t - P * Real.log t) (Icc X Y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc X Y) hcont
    · intro t ht; exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      have ht0 := hpos t ht'
      rw [(hd t ht').deriv, deriv_e8Theta_eq_profile ht0]
      have hp := hP t ht'
      have e : profile (radialContact (2 * t) 1) / t - P * t⁻¹ =
          (profile (radialContact (2 * t) 1) - P) / t := by field_simp
      rw [e]
      apply div_nonneg (by linarith) ht0.le
  have h := hmono ⟨le_rfl, hXY⟩ ⟨hXY, le_rfl⟩ hXY
  simp only at h
  have hY0 : 0 < Y := lt_of_lt_of_le hX hXY
  rw [Real.log_div hY0.ne' hX.ne']
  linarith

end CKLaneP

end


