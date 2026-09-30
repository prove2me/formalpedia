-- Prove2me | Definitions.Def_CK_GeneralCK_PsiThreeTenthsContactRefinement
-- name    : CK_GeneralCK_PsiThreeTenthsContactRefinement
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:51:11.132917+00:00
-- url     : https://prove2.me/theorems/94e1f990-ad09-426b-87a7-7b54c2c16d19
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiThreeTenthsContactRefinement` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiThreeTenthsContactRefinement` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiThreeTenthsContactRefinement` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiThreeTenthsContactRefinement (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiThreeTenthsContactRefinement.lean)

import Definitions.Def_CK_GeneralCK_PsiTwoSeventhsBiasClosure
import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneNoFold

-- ===== source module GeneralCK.PsiThreeTenthsContactRefinement =====
section

/-! Reusable actual-contact refinement and the fifteen-sixteenths odds bound. -/

namespace GeneralCK.PsiThreeTenthsContactRefinement

theorem contact_odds_of_cost_saving {q E r s : ℝ}
    (hq : 0 < q) (hE : 0 < E) (hratio : 8 * E ≤ q) (hr : 15 / 16 ≤ r)
    (hprevious : F q E * Real.log 2 ≤ q * (2 * Real.log (q / E) - s))
    (hpoly : ∀ x : ℝ, 8 ≤ x →
      0 < (69314 / 100000) * (r * x ^ 2 - 6 * x - 1) - x ^ 2 / 4 + (59 / 60 + s) * x) :
    (1 - radialContact q E) / radialContact q E ≤ r * (q / E) ^ 2 := by
  let v := radialContact q E
  let y := (1 - v) / v
  let x := q / E
  have hv : 0 < v := radialContact_pos hq hE
  have hx : 8 ≤ x := (le_div_iff₀ hE).mpr hratio
  have hxpos : 0 < x := by linarith
  have hyv : v * y = 1 - v := by dsimp [y]; field_simp
  have hxe : E * x = q := mul_div_cancel₀ _ hE.ne'
  have hid : F q E * Real.log 2 = q * Real.log y := by
    unfold F
    rw [if_neg hq.ne']
    change q * (Real.log y / Real.log 2) * Real.log 2 = _
    field_simp
  have hlog : Real.log y ≤ 2 * Real.log x - s := by
    rw [hid] at hprevious
    apply (mul_le_mul_iff_left₀ hq).mp
    convert! hprevious using 1 <;> ring
  change y ≤ r * x ^ 2
  by_contra hcontra
  have hylo : r * x ^ 2 < y := lt_of_not_ge hcontra
  have hrx := mul_nonneg (show 0 ≤ r - 15 / 16 by linarith) (sq_nonneg x)
  have hvu : v ≤ 1 / 61 := by
    have hy : 60 < y := by nlinarith [sq_nonneg (x - 8)]
    nlinarith only [hyv, mul_pos hv (show 0 < y - 60 by linarith)]
  have heq := radialContact_equation hq hE
  have hh := mul_le_mul_of_nonneg_left
    (PsiRatioEightContactRefinement.entropy_logit_upper hv hvu) hq.le
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
  have hcost : Real.log 2 * (y - 1) ≤ x * (6 * Real.log 2 + x / 4 - 59 / 60 - s) := by
    nlinarith only [hc, mul_nonneg hxpos.le
      (show 0 ≤ 2 * Real.log x - s - Real.log y from sub_nonneg.mpr hlog),
      mul_nonneg hxpos.le (show 0 ≤ 3 * Real.log 2 + x / 8 - 1 - Real.log x by linarith)]
  have hL : (69314 / 100000 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hb : 0 ≤ r * x ^ 2 - 6 * x - 1 := by nlinarith [sq_nonneg (x - 8)]
  have hprod := mul_le_mul_of_nonneg_right hL hb
  have hstrict := mul_lt_mul_of_pos_left hylo log_two_pos
  nlinarith only [hprod, hstrict, hcost, hpoly x hx]

theorem F_log_bound_of_odds {q E r s : ℝ} (hq : 0 < q) (hE : 0 < E)
    (hr : 0 < r) (hlog : Real.log r ≤ -s)
    (hodds : (1 - radialContact q E) / radialContact q E ≤ r * (q / E) ^ 2) :
    F q E * Real.log 2 ≤ q * (2 * Real.log (q / E) - s) := by
  have hv := radialContact_pos hq hE
  have hvh := radialContact_lt_half hq hE
  have hx : 0 < q / E := div_pos hq hE
  have hh := Real.log_le_log (div_pos (by linarith : 0 < 1 - radialContact q E) hv) hodds
  rw [Real.log_mul hr.ne' (pow_ne_zero _ hx.ne'), Real.log_pow] at hh
  have hl : Real.log ((1 - radialContact q E) / radialContact q E) ≤
      2 * Real.log (q / E) - s := by linarith only [hh, hlog]
  have hm := mul_le_mul_of_nonneg_left hl hq.le
  unfold F
  rw [if_neg hq.ne']
  unfold J
  convert! hm using 1
  field_simp

theorem F_log_bound_six_ninety_sevenths {q E : ℝ}
    (hq : 0 < q) (hE : 0 < E) (hr : 8 * E ≤ q) :
    F q E * Real.log 2 ≤ q * (2 * Real.log (q / E) - 6 / 97) := by
  apply F_log_bound_of_odds hq hE (by norm_num : (0 : ℝ) < 47 / 50) ?_
    (PsiRatioEightContactRefinement.contact_odds_le_forty_seven_fiftieths hq hE hr)
  have h := PsiEndpointPlane.log_le_twice_sub_div_add (by norm_num : (0 : ℝ) < 47 / 50)
    (by norm_num : (47 / 50 : ℝ) ≤ 1)
  norm_num at h ⊢
  exact h

theorem contact_odds_le_four_sixty_nine_five_hundredths {q E : ℝ}
    (hq : 0 < q) (hE : 0 < E) (hr : 8 * E ≤ q) :
    (1 - radialContact q E) / radialContact q E ≤ (469 / 500) * (q / E) ^ 2 := by
  apply contact_odds_of_cost_saving hq hE hr (by norm_num)
    (F_log_bound_six_ninety_sevenths hq hE hr)
  intro x hx
  have hy : 0 ≤ x - 8 := by linarith
  have he : (69314 / 100000) * ((469 / 500) * x ^ 2 - 6 * x - 1) - x ^ 2 / 4 + (59 / 60 + 6 / 97) * x =
      (10004133 / 25000000) * (x - 8) ^ 2 + (2990929031 / 909375000) * (x - 8) +
        14972873 / 1818750000 := by ring
  rw [he]
  positivity

theorem F_log_bound_sixty_two_nine_sixty_ninths {q E : ℝ}
    (hq : 0 < q) (hE : 0 < E) (hr : 8 * E ≤ q) :
    F q E * Real.log 2 ≤ q * (2 * Real.log (q / E) - 62 / 969) := by
  apply F_log_bound_of_odds hq hE (by norm_num : (0 : ℝ) < 469 / 500) ?_
    (contact_odds_le_four_sixty_nine_five_hundredths hq hE hr)
  have h := PsiEndpointPlane.log_le_twice_sub_div_add (by norm_num : (0 : ℝ) < 469 / 500)
    (by norm_num : (469 / 500 : ℝ) ≤ 1)
  norm_num at h ⊢
  exact h

theorem contact_odds_le_fifteen_sixteenths {q E : ℝ}
    (hq : 0 < q) (hE : 0 < E) (hr : 8 * E ≤ q) :
    (1 - radialContact q E) / radialContact q E ≤ (15 / 16) * (q / E) ^ 2 := by
  apply contact_odds_of_cost_saving hq hE hr (by norm_num)
    (F_log_bound_sixty_two_nine_sixty_ninths hq hE hr)
  intro x hx
  have hy : 0 ≤ x - 8 := by linarith
  have he : (69314 / 100000) * ((15 / 16) * x ^ 2 - 6 * x - 1) - x ^ 2 / 4 + (59 / 60 + 62 / 969) * x =
      (63971 / 160000) * (x - 8) ^ 2 + (159186197 / 48450000) * (x - 8) +
        148963 / 48450000 := by ring
  rw [he]
  positivity

theorem F_log_bound {q E : ℝ} (hq : 0 < q) (hE : 0 < E) (hr : 8 * E ≤ q) :
    F q E * Real.log 2 ≤ q * (2 * Real.log (q / E) - 2 / 31) := by
  apply F_log_bound_of_odds hq hE (by norm_num : (0 : ℝ) < 15 / 16) ?_
    (contact_odds_le_fifteen_sixteenths hq hE hr)
  have h := PsiEndpointPlane.log_le_twice_sub_div_add (by norm_num : (0 : ℝ) < 15 / 16)
    (by norm_num : (15 / 16 : ℝ) ≤ 1)
  norm_num at h ⊢
  exact h

end GeneralCK.PsiThreeTenthsContactRefinement

#print axioms GeneralCK.PsiThreeTenthsContactRefinement.contact_odds_of_cost_saving
#print axioms GeneralCK.PsiThreeTenthsContactRefinement.F_log_bound_of_odds
#print axioms GeneralCK.PsiThreeTenthsContactRefinement.F_log_bound_six_ninety_sevenths
#print axioms GeneralCK.PsiThreeTenthsContactRefinement.contact_odds_le_four_sixty_nine_five_hundredths
#print axioms GeneralCK.PsiThreeTenthsContactRefinement.F_log_bound_sixty_two_nine_sixty_ninths
#print axioms GeneralCK.PsiThreeTenthsContactRefinement.contact_odds_le_fifteen_sixteenths
#print axioms GeneralCK.PsiThreeTenthsContactRefinement.F_log_bound

end


