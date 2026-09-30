-- Prove2me | Definitions.Def_CK_GeneralCK_PsiRatioEightContactRefinement
-- name    : CK_GeneralCK_PsiRatioEightContactRefinement
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:22:50.07461+00:00
-- url     : https://prove2.me/theorems/b9892e06-4c68-4759-b626-0919814b6769
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiRatioEightContactRefinement` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiRatioEightContactRefinement` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiRatioEightContactRefinement` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiRatioEightContactRefinement (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiRatioEightContactRefinement.lean)

import Definitions.Def_CK_GeneralCK_PsiQuarterBiasClosure

-- ===== source module GeneralCK.PsiRatioEightContactRefinement =====
section

/-! A strict improvement of the quadratic odds envelope at the actual contact. -/

namespace GeneralCK.PsiRatioEightContactRefinement

theorem entropy_logit_upper {v : ℝ} (hv : 0 < v) (hvu : v ≤ 1 / 61) :
    H v * Real.log 2 ≤ v * (Real.log ((1 - v) / v) + 61 / 60) := by
  have hvc : 0 < 1 - v := by linarith
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hvc)
  have hm := mul_le_mul_of_nonneg_left hl hvc.le
  rw [show (1 - v) * ((1 - v)⁻¹ - 1) = v by field_simp; ring, Real.log_inv] at hm
  have hn : 0 ≤ -Real.log (1 - v) :=
    neg_nonneg.mpr (Real.log_nonpos hvc.le (by linarith))
  have hc : -Real.log (1 - v) ≤ (61 / 60) * v := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hvu) hn]
  rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy,
    Real.log_div hvc.ne' hv.ne']
  simp only [Real.log_inv]
  nlinarith only [hc]

theorem contact_odds_le_nineteen_twentieths {q E : ℝ}
    (hq : 0 < q) (hE : 0 < E) (hr : 8 * E ≤ q) :
    (1 - radialContact q E) / radialContact q E ≤ (19 / 20) * (q / E) ^ 2 := by
  let v := radialContact q E
  let y := (1 - v) / v
  let x := q / E
  have hv : 0 < v := radialContact_pos hq hE
  have hx : 8 ≤ x := (le_div_iff₀ hE).mpr hr
  have hxpos : 0 < x := by linarith
  have hyv : v * y = 1 - v := by dsimp [y]; field_simp
  have hxe : E * x = q := mul_div_cancel₀ _ hE.ne'
  have hF := PsiParentDominance.F_le_logarithmic_ratio8 hq hE hr
  have hid : F q E * Real.log 2 = q * Real.log y := by
    unfold F
    rw [if_neg hq.ne']
    change q * (Real.log y / Real.log 2) * Real.log 2 = _
    field_simp
  have hlog : Real.log y ≤ 2 * Real.log x := by
    have hh := (le_div_iff₀ log_two_pos).mp hF
    rw [hid] at hh
    apply (mul_le_mul_iff_left₀ hq).mp
    convert! hh using 1 <;> ring
  change y ≤ (19 / 20) * x ^ 2
  by_contra hcontra
  have hylo : (19 / 20) * x ^ 2 < y := lt_of_not_ge hcontra
  have hvu : v ≤ 1 / 61 := by
    have hy : 60 < y := by nlinarith [sq_nonneg (x - 8)]
    nlinarith only [hyv, mul_pos hv (show 0 < y - 60 by linarith)]
  have heq := radialContact_equation hq hE
  have hh := mul_le_mul_of_nonneg_left (entropy_logit_upper hv hvu) hq.le
  have hc : Real.log 2 * (y - 1) ≤ x * (Real.log y + 61 / 60) := by
    apply (mul_le_mul_iff_right₀ (mul_pos hE hv)).mp
    change q * H v = E * (1 - 2 * v) at heq
    change q * (H v * Real.log 2) ≤ q * (v * (Real.log y + 61 / 60)) at hh
    calc
      (E * v) * (Real.log 2 * (y - 1)) = q * (H v * Real.log 2) := by
        linear_combination E * Real.log 2 * hyv - Real.log 2 * heq
      _ ≤ q * (v * (Real.log y + 61 / 60)) := hh
      _ = (E * v) * (x * (Real.log y + 61 / 60)) := by rw [← hxe]; ring
  have ht := Real.log_le_sub_one_of_pos (show 0 < x / 8 by positivity)
  rw [Real.log_div hxpos.ne' (by norm_num : (8 : ℝ) ≠ 0),
    show Real.log (8 : ℝ) = 3 * Real.log 2 by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num] at ht
  have hcost : Real.log 2 * (y - 1) ≤ x * (6 * Real.log 2 + x / 4 - 59 / 60) := by
    nlinarith only [hc, mul_nonneg hxpos.le (show 0 ≤ 2 * Real.log x - Real.log y from sub_nonneg.mpr hlog),
      mul_nonneg hxpos.le (show 0 ≤ 3 * Real.log 2 + x / 8 - 1 - Real.log x by linarith)]
  have hL : (69 / 100 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hb : 0 ≤ (19 / 20) * x ^ 2 - 6 * x - 1 := by nlinarith [sq_nonneg (x - 8)]
  have hprod := mul_le_mul_of_nonneg_right hL hb
  have hstrict := mul_lt_mul_of_pos_left hylo log_two_pos
  have he : (69 / 100) * ((19 / 20) * x ^ 2 - 6 * x - 1) - x ^ 2 / 4 + 59 * x / 60 =
      (811 / 2000) * (x - 8) ^ 2 + (4997 / 1500) * (x - 8) + 13 / 1500 := by ring
  have hpositive : 0 < (69 / 100) * ((19 / 20) * x ^ 2 - 6 * x - 1) - x ^ 2 / 4 + 59 * x / 60 := by
    rw [he]
    have : 0 ≤ x - 8 := by linarith
    positivity
  nlinarith only [hprod, hstrict, hcost, hpositive]

theorem F_log_bound {q E : ℝ} (hq : 0 < q) (hE : 0 < E) (hr : 8 * E ≤ q) :
    F q E * Real.log 2 ≤ q * (2 * Real.log (q / E) - 1 / 20) := by
  have hv := radialContact_pos hq hE
  have hvh := radialContact_lt_half hq hE
  have hx : 0 < q / E := div_pos hq hE
  have hh := Real.log_le_log (div_pos (by linarith : 0 < 1 - radialContact q E) hv)
    (contact_odds_le_nineteen_twentieths hq hE hr)
  rw [Real.log_mul (by norm_num : (19 / 20 : ℝ) ≠ 0) (pow_ne_zero _ hx.ne'), Real.log_pow] at hh
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 19 / 20)
  have hl : Real.log ((1 - radialContact q E) / radialContact q E) ≤
      2 * Real.log (q / E) - 1 / 20 := by linarith only [hh, hc]
  have hm := mul_le_mul_of_nonneg_left hl hq.le
  unfold F
  rw [if_neg hq.ne']
  unfold J
  convert! hm using 1
  field_simp

theorem contact_odds_le_forty_seven_fiftieths {q E : ℝ}
    (hq : 0 < q) (hE : 0 < E) (hr : 8 * E ≤ q) :
    (1 - radialContact q E) / radialContact q E ≤ (47 / 50) * (q / E) ^ 2 := by
  let v := radialContact q E
  let y := (1 - v) / v
  let x := q / E
  have hv : 0 < v := radialContact_pos hq hE
  have hx : 8 ≤ x := (le_div_iff₀ hE).mpr hr
  have hxpos : 0 < x := by linarith
  have hyv : v * y = 1 - v := by dsimp [y]; field_simp
  have hxe : E * x = q := mul_div_cancel₀ _ hE.ne'
  have hF := F_log_bound hq hE hr
  have hid : F q E * Real.log 2 = q * Real.log y := by
    unfold F
    rw [if_neg hq.ne']
    change q * (Real.log y / Real.log 2) * Real.log 2 = _
    field_simp
  have hlog : Real.log y ≤ 2 * Real.log x - 1 / 20 := by
    have hh := hF
    rw [hid] at hh
    apply (mul_le_mul_iff_left₀ hq).mp
    convert! hh using 1 <;> ring
  change y ≤ (47 / 50) * x ^ 2
  by_contra hcontra
  have hylo : (47 / 50) * x ^ 2 < y := lt_of_not_ge hcontra
  have hvu : v ≤ 1 / 61 := by
    have hy : 60 < y := by nlinarith [sq_nonneg (x - 8)]
    nlinarith only [hyv, mul_pos hv (show 0 < y - 60 by linarith)]
  have heq := radialContact_equation hq hE
  have hh := mul_le_mul_of_nonneg_left (entropy_logit_upper hv hvu) hq.le
  have hc : Real.log 2 * (y - 1) ≤ x * (Real.log y + 61 / 60) := by
    apply (mul_le_mul_iff_right₀ (mul_pos hE hv)).mp
    change q * H v = E * (1 - 2 * v) at heq
    change q * (H v * Real.log 2) ≤ q * (v * (Real.log y + 61 / 60)) at hh
    calc
      (E * v) * (Real.log 2 * (y - 1)) = q * (H v * Real.log 2) := by
        linear_combination E * Real.log 2 * hyv - Real.log 2 * heq
      _ ≤ q * (v * (Real.log y + 61 / 60)) := hh
      _ = (E * v) * (x * (Real.log y + 61 / 60)) := by rw [← hxe]; ring
  have ht := Real.log_le_sub_one_of_pos (show 0 < x / 8 by positivity)
  rw [Real.log_div hxpos.ne' (by norm_num : (8 : ℝ) ≠ 0),
    show Real.log (8 : ℝ) = 3 * Real.log 2 by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num] at ht
  have hcost : Real.log 2 * (y - 1) ≤ x * (6 * Real.log 2 + x / 4 - 31 / 30) := by
    nlinarith only [hc, mul_nonneg hxpos.le (show 0 ≤ 2 * Real.log x - 1 / 20 - Real.log y from sub_nonneg.mpr hlog),
      mul_nonneg hxpos.le (show 0 ≤ 3 * Real.log 2 + x / 8 - 1 - Real.log x by linarith)]
  have hL : (693 / 1000 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hb : 0 ≤ (47 / 50) * x ^ 2 - 6 * x - 1 := by nlinarith [sq_nonneg (x - 8)]
  have hprod := mul_le_mul_of_nonneg_right hL hb
  have hstrict := mul_lt_mul_of_pos_left hylo log_two_pos
  have he : (693 / 1000) * ((47 / 50) * x ^ 2 - 6 * x - 1) - x ^ 2 / 4 + 31 * x / 30 =
      (20071 / 50000) * (x - 8) ^ 2 + (123677 / 37500) * (x - 8) + 41 / 75000 := by ring
  have hpositive : 0 < (693 / 1000) * ((47 / 50) * x ^ 2 - 6 * x - 1) - x ^ 2 / 4 + 31 * x / 30 := by
    rw [he]
    have : 0 ≤ x - 8 := by linarith
    positivity
  nlinarith only [hprod, hstrict, hcost, hpositive]

theorem F_log_bound_refined {q E : ℝ} (hq : 0 < q) (hE : 0 < E) (hr : 8 * E ≤ q) :
    F q E * Real.log 2 ≤ q * (2 * Real.log (q / E) - 3 / 50) := by
  have hv := radialContact_pos hq hE
  have hvh := radialContact_lt_half hq hE
  have hx : 0 < q / E := div_pos hq hE
  have hh := Real.log_le_log (div_pos (by linarith : 0 < 1 - radialContact q E) hv)
    (contact_odds_le_forty_seven_fiftieths hq hE hr)
  rw [Real.log_mul (by norm_num : (47 / 50 : ℝ) ≠ 0) (pow_ne_zero _ hx.ne'), Real.log_pow] at hh
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 47 / 50)
  have hl : Real.log ((1 - radialContact q E) / radialContact q E) ≤
      2 * Real.log (q / E) - 3 / 50 := by linarith only [hh, hc]
  have hm := mul_le_mul_of_nonneg_left hl hq.le
  unfold F
  rw [if_neg hq.ne']
  unfold J
  convert! hm using 1
  field_simp

end GeneralCK.PsiRatioEightContactRefinement

#print axioms GeneralCK.PsiRatioEightContactRefinement.entropy_logit_upper
#print axioms GeneralCK.PsiRatioEightContactRefinement.contact_odds_le_nineteen_twentieths
#print axioms GeneralCK.PsiRatioEightContactRefinement.F_log_bound

#print axioms GeneralCK.PsiRatioEightContactRefinement.contact_odds_le_forty_seven_fiftieths
#print axioms GeneralCK.PsiRatioEightContactRefinement.F_log_bound_refined

end


