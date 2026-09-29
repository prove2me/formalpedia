-- Prove2me | Definitions.Def_CK_GeneralCK_PsiParentDominance
-- name    : CK_GeneralCK_PsiParentDominance
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:03:05.123806+00:00
-- url     : https://prove2.me/theorems/68bb5140-146e-4595-8d81-669f07fa1b23
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiParentDominance` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiParentDominance` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiParentDominance` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiParentDominance (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiParentDominance.lean)

import Definitions.Def_CK_GeneralCK_PsiParentEntropyGain
import Definitions.Def_CK_GeneralCK_RadialDerivatives
import Definitions.Def_CK_GeneralCK_EntropyParabola

-- ===== source module GeneralCK.PsiParentDominance =====
section

/-!
# Analytic factor-eight parent dominance at small bias

This proves the full factor-eight parent argument on `0<q<=1/10` and
`8E<=q`, with no numerical subdivision or common child entropy cap.
-/
namespace GeneralCK.PsiParentDominance
open Set

private theorem entropy_logit_upper {v : ℝ} (hv : 0 < v) (hvhalf : v < 1 / 2) :
    H v * Real.log 2 ≤ v * (Real.log ((1 - v) / v) + 2) := by
  have hvc : 0 < 1 - v := by linarith
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hvc)
  have hm := mul_le_mul_of_nonneg_left hl hvc.le
  have he : (1 - v) * ((1 - v)⁻¹ - 1) = v := by field_simp; ring
  rw [he] at hm
  rw [Real.log_inv] at hm
  rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy,
    Real.log_div hvc.ne' hv.ne']
  simp only [Real.log_inv]
  have hl2 : -Real.log (1 - v) ≤ 2 * v := by
    have hneg : 0 ≤ -Real.log (1 - v) := by
      exact neg_nonneg.mpr (Real.log_nonpos hvc.le (by linarith))
    nlinarith
  nlinarith

/-- Elementary contact upper bound, valid for all positive radii/entropies. -/
theorem F_le_logarithmic {q E : ℝ} (hq : 0 < q) (hE : 0 < E) :
    F q E ≤ 2 * q * Real.log (2 + 3 * q / E) / Real.log 2 := by
  let v := radialContact q E
  let w := Real.sqrt ((1 - v) / v)
  have hv : 0 < v := radialContact_pos hq hE
  have hvhalf : v < 1 / 2 := radialContact_lt_half hq hE
  have hvc : 0 < 1 - v := by linarith
  have hr : 0 < (1 - v) / v := div_pos hvc hv
  have hw : 0 < w := Real.sqrt_pos.mpr hr
  have hwsq : w ^ 2 = (1 - v) / v := Real.sq_sqrt hr.le
  have hwprod : v * w ^ 2 = 1 - v := by rw [hwsq]; field_simp
  have hw1 : 1 < w := by nlinarith
  have hwlog : 2 * Real.log w = Real.log ((1 - v) / v) := by
    rw [show Real.log w = Real.log ((1 - v) / v) / 2 from Real.log_sqrt hr.le]
    ring
  have hlog := Real.log_le_sub_one_of_pos hw
  have hH := entropy_logit_upper hv hvhalf
  rw [← hwlog] at hH
  have hH' : H v * Real.log 2 ≤ 2 * v * w := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hv.le]
  have heq : q * H v = E * (1 - 2 * v) := radialContact_equation hq hE
  have hbound := mul_le_mul_of_nonneg_left hH' hq.le
  have hidentity : q * (H v * Real.log 2) =
      E * v * Real.log 2 * (w ^ 2 - 1) := by
    calc
      _ = E * (1 - 2 * v) * Real.log 2 := by rw [← mul_assoc, heq]
      _ = _ := by linear_combination -E * Real.log 2 * hwprod
  rw [hidentity] at hbound
  have hcancel : E * Real.log 2 * (w ^ 2 - 1) ≤ 2 * q * w := by
    apply (mul_le_mul_iff_right₀ hv).mp
    nlinarith only [hbound]
  have hL : (2 / 3 : ℝ) < Real.log 2 := by
    have hh := Certificates.PilotData.log_two.1
    norm_num at hh
    linarith
  have hx : 0 < q / E := div_pos hq hE
  have hwbig : w ≤ 2 + 3 * q / E := by
    by_contra hno
    have hgt : 2 + 3 * q / E < w := lt_of_not_ge hno
    have he : E * (q / E) = q := mul_div_cancel₀ q hE.ne'
    have hmul := mul_pos (show 0 < E * (w ^ 2 - 1) from
        mul_pos hE (by nlinarith only [hw1, sq_nonneg (w - 1)]))
      (show 0 < Real.log 2 - 2 / 3 by linarith)
    have hstep : E * (w ^ 2 - 1) < 3 * q * w := by nlinarith only [hcancel, hmul]
    have hsq : (2 + 3 * q / E) * w < w ^ 2 := by
      simpa only [pow_two] using mul_lt_mul_of_pos_right hgt hw
    have hh := mul_lt_mul_of_pos_left hsq hE
    have hhe : E * ((2 + 3 * q / E) * w) = 2 * E * w + 3 * q * w := by
      field_simp
    rw [hhe] at hh
    nlinarith only [hstep, hh, hE, mul_pos hE (show 0 < w - 1 by linarith)]
  have hlogbound := Real.log_le_log hw hwbig
  unfold F
  rw [if_neg hq.ne']
  change q * J v ≤ _
  unfold J
  rw [← hwlog]
  have hh := mul_le_mul_of_nonneg_left hlogbound
    (show 0 ≤ 2 * q / Real.log 2 by positivity)
  convert! hh using 1 <;> ring

private theorem logarithmic_tail_comparison {x : ℝ} (hx : 32 ≤ x) :
    Real.log (2 + 3 * x) < 5 * Real.log (1 + x / 20) := by
  have hy : 0 ≤ x - 32 := by linarith
  have he : (1 + x / 20) ^ 5 - (2 + 3 * x) =
      (x - 32) ^ 5 / 3200000 + 13 * (x - 32) ^ 4 / 160000 +
      169 * (x - 32) ^ 3 / 20000 + 2197 * (x - 32) ^ 2 / 5000 +
      21061 * (x - 32) / 2500 + 65043 / 3125 := by ring
  have hp : 0 < (1 + x / 20) ^ 5 - (2 + 3 * x) := by
    rw [he]
    positivity
  have hh := Real.log_lt_log (by linarith : 0 < 2 + 3 * x)
    (show 2 + 3 * x < (1 + x / 20) ^ 5 by linarith)
  rw [Real.log_pow] at hh
  simpa using hh

/-- Concavity retains a useful factor of the small parent bias. -/
theorem logarithmic_bias_scale {q x : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 10)
    (hx : 0 ≤ x) :
    10 * q * Real.log (1 + x / 20) ≤ Real.log (1 + q * x / 2) := by
  have hxp : (0 : ℝ) < 1 + x / 20 := by linarith
  have hh := strictConcaveOn_log_Ioi.concaveOn.2
    hxp
    (show (1 : ℝ) ∈ Ioi 0 from by norm_num)
    (show 0 ≤ 10 * q by positivity) (show 0 ≤ 1 - 10 * q by linarith)
    (show 10 * q + (1 - 10 * q) = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hh
  have he : 10 * q * (1 + x / 20) + (1 - 10 * q) * 1 = 1 + q * x / 2 := by ring
  rwa [he] at hh

/-- A complete analytic parent-dominance tail, independently of the child
means and entropy split. This is a true region theorem, not a scalar premise.
The strict inequality includes `q=1/10` and `32E=q`. -/
theorem parent_dominance_ratio32 {q E : ℝ} (hE : 0 < E)
    (hq : 0 < q) (hq' : q ≤ 1 / 10) (hratio : 32 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  let C := 1 - H ((1 - q) / 2)
  let x := q / E
  have hx : 32 ≤ x := (le_div_iff₀ hE).mpr hratio
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hCup : C ≤ q ^ 2 := by
    have hh := H_gt_parabola (p := (1 - q) / 2) (by linarith) (by linarith)
    dsimp [C]
    nlinarith only [hh]
  have hL : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hClow : q ^ 2 / 2 ≤ C := by
    have hh := SmallMean.Cn_ge_half_sq hq.le (by linarith : q ≤ 1)
    change q ^ 2 / 2 ≤ Real.log 2 * C at hh
    exact hh.trans (by simpa using mul_le_mul_of_nonneg_right hL hC)
  have hphysical : E + C ≤ 1 := by
    have hsmall := mul_nonneg hq.le (show 0 ≤ 1 / 10 - q by linarith)
    nlinarith only [hCup, hsmall, hratio, hq']
  have hgain := eta_increment_ge_linear_log hE hC hphysical
  have hlogratio : Real.log (1 + q * x / 2) ≤ Real.log (1 + C / E) := by
    have hx0 : 0 ≤ x := by linarith
    apply Real.log_le_log (by positivity)
    have hh := div_le_div_of_nonneg_right hClow hE.le
    dsimp [x]
    convert! add_le_add_left hh 1 using 1 <;> ring
  have hscale := logarithmic_bias_scale hq.le hq' (by linarith : 0 ≤ x)
  have hpoly := logarithmic_tail_comparison hx
  have hF : F q E < eta E - eta (E + C) := by
    calc
      F q E ≤ 2 * q * Real.log (2 + 3 * x) / Real.log 2 := by
        simpa only [x, mul_div_assoc] using F_le_logarithmic hq hE
      _ < 10 * q * Real.log (1 + x / 20) / Real.log 2 := by
        apply div_lt_div_of_pos_right _ log_two_pos
        have hh := mul_lt_mul_of_pos_left hpoly (show 0 < 2 * q by positivity)
        nlinarith only [hh]
      _ ≤ Real.log (1 + q * x / 2) / Real.log 2 :=
        div_le_div_of_nonneg_right hscale log_two_pos.le
      _ ≤ Real.log (1 + C / E) / Real.log 2 :=
        div_le_div_of_nonneg_right hlogratio log_two_pos.le
      _ ≤ eta E - eta (E + C) := by linarith only [hgain, hC]
  have habs : |1 - 2 * ((1 - q) / 2)| = q := by
    rw [show 1 - 2 * ((1 - q) / 2) = q by ring, abs_of_pos hq]
  unfold phi psi
  rw [habs]
  have he : E + 1 - H ((1 - q) / 2) = E + C := by dsimp [C]; ring
  rw [he]
  linarith only [hF]

theorem parent_dominance_ratio32_of_mean {m E : ℝ} (hE : 0 < E)
    (hq : 0 < 1 - 2 * m) (hq' : 1 - 2 * m ≤ 1 / 10)
    (hratio : 32 * E ≤ 1 - 2 * m) : psi m E < phi m E := by
  have h := parent_dominance_ratio32 hE hq hq' hratio
  simpa only [show (1 - (1 - 2 * m)) / 2 = m by ring] using h

private theorem entropy_logit_upper_tight {v : ℝ} (hv : 0 < v) (hv65 : v ≤ 1 / 65) :
    H v * Real.log 2 ≤ v * (Real.log ((1 - v) / v) + 65 / 64) := by
  have hvc : 0 < 1 - v := by linarith
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hvc)
  have hm := mul_le_mul_of_nonneg_left hl hvc.le
  have he : (1 - v) * ((1 - v)⁻¹ - 1) = v := by field_simp; ring
  rw [he, Real.log_inv] at hm
  have hneg : 0 ≤ -Real.log (1 - v) :=
    neg_nonneg.mpr (Real.log_nonpos hvc.le (by linarith))
  have hl2 : -Real.log (1 - v) ≤ 65 / 64 * v := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv65) hneg]
  rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy,
    Real.log_div hvc.ne' hv.ne']
  simp only [Real.log_inv]
  nlinarith only [hl2]

/-- A sharper elementary contact bound on the entire ratio-eight tail. -/
theorem F_le_logarithmic_ratio8 {q E : ℝ} (hq : 0 < q) (hE : 0 < E)
    (h8 : 8 * E ≤ q) :
    F q E ≤ 2 * q * Real.log (q / E) / Real.log 2 := by
  let v := radialContact q E
  let w := Real.sqrt ((1 - v) / v)
  let x := q / E
  have hx : 8 ≤ x := (le_div_iff₀ hE).mpr h8
  have hxe : E * x = q := mul_div_cancel₀ q hE.ne'
  have hv : 0 < v := radialContact_pos hq hE
  have hvhalf : v < 1 / 2 := radialContact_lt_half hq hE
  have hr : 0 < (1 - v) / v := div_pos (by linarith) hv
  have hw : 0 < w := Real.sqrt_pos.mpr hr
  have hwsq : w ^ 2 = (1 - v) / v := Real.sq_sqrt hr.le
  have hwprod : v * w ^ 2 = 1 - v := by rw [hwsq]; field_simp
  have hwlog : 2 * Real.log w = Real.log ((1 - v) / v) := by
    rw [show Real.log w = Real.log ((1 - v) / v) / 2 from Real.log_sqrt hr.le]
    ring
  have hL : (2 / 3 : ℝ) < Real.log 2 := by
    have hh := Certificates.PilotData.log_two.1
    norm_num at hh
    linarith
  have hwx : w ≤ x := by
    by_contra hn
    have hxw : x < w := lt_of_not_ge hn
    have hw8 : 8 ≤ w := by linarith
    have hw64 : 64 ≤ w ^ 2 := by nlinarith only [hw8, sq_nonneg (w - 8)]
    have hv65 : v ≤ 1 / 65 := by
      have hh := mul_le_mul_of_nonneg_left hw64 hv.le
      nlinarith only [hh, hwprod]
    have hH := entropy_logit_upper_tight hv hv65
    rw [← hwlog] at hH
    have hlog := Real.log_le_sub_one_of_pos (show 0 < w / 8 by positivity)
    rw [Real.log_div hw.ne' (by norm_num : (8 : ℝ) ≠ 0),
      show Real.log 8 = 3 * Real.log 2 by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num] at hlog
    have hH' : H v * Real.log 2 ≤ v * (6 * Real.log 2 + w / 4 - 63 / 64) := by
      nlinarith [mul_le_mul_of_nonneg_left hlog hv.le]
    have hbound := mul_le_mul_of_nonneg_left hH' hq.le
    have heq : q * H v = E * (1 - 2 * v) := radialContact_equation hq hE
    have hi : q * (H v * Real.log 2) = E * v * Real.log 2 * (w ^ 2 - 1) := by
      calc
        _ = E * (1 - 2 * v) * Real.log 2 := by rw [← mul_assoc, heq]
        _ = _ := by linear_combination -E * Real.log 2 * hwprod
    rw [hi, ← hxe] at hbound
    have hcancel : Real.log 2 * (w ^ 2 - 1) ≤ x * (6 * Real.log 2 + w / 4 - 63 / 64) := by
      apply (mul_le_mul_iff_right₀ (mul_pos hE hv)).mp
      nlinarith only [hbound]
    have hcoef : 0 < 6 * Real.log 2 + w / 4 - 63 / 64 := by linarith
    have hstrict := mul_lt_mul_of_pos_right hxw hcoef
    have hbase : 0 ≤ w ^ 2 - 6 * w - 1 := by
      nlinarith only [hw8, sq_nonneg (w - 8)]
    have hLmul := mul_le_mul_of_nonneg_right hL.le hbase
    have hy : 0 ≤ w - 8 := by linarith
    have hpoly : 0 < (5 / 12 : ℝ) * (w - 8) ^ 2 + (701 / 192) * (w - 8) + 15 / 8 := by
      positivity
    nlinarith only [hcancel, hstrict, hLmul, hpoly]
  have hlogs := Real.log_le_log hw hwx
  have hh := mul_le_mul_of_nonneg_left hlogs (show 0 ≤ 2 * q / Real.log 2 by positivity)
  unfold F
  rw [if_neg hq.ne']
  change q * J v ≤ _
  unfold J
  rw [← hwlog]
  convert! hh using 1 <;> ring

private theorem logarithmic_eight_comparison {x : ℝ} (hx : 8 ≤ x) :
    Real.log x < 5 * Real.log (1 + x / 14) := by
  have hy : 0 ≤ x - 8 := by linarith
  have he : (1 + x / 14) ^ 5 - x =
      (x - 8) ^ 5 / 537824 + 55 * (x - 8) ^ 4 / 268912 +
      605 * (x - 8) ^ 3 / 67228 + 6655 * (x - 8) ^ 2 / 33614 +
      39591 * (x - 8) / 33614 + 26595 / 16807 := by ring
  have hp : 0 < (1 + x / 14) ^ 5 - x := by rw [he]; positivity
  have hh := Real.log_lt_log (by linarith : 0 < x)
    (show x < (1 + x / 14) ^ 5 by linarith)
  rw [Real.log_pow] at hh
  simpa using hh

/-- The full factor-eight parent criterion on the small-bias range is
analytic: no numerical partition, entropy inverse certificate, or child cap
is needed. The larger bias interval `(1/10,2/5]` remains separate. -/
theorem parent_dominance_ratio8_small_bias {q E : ℝ} (hE : 0 < E)
    (hq : 0 < q) (hq' : q ≤ 1 / 10) (hratio : 8 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  let C := 1 - H ((1 - q) / 2)
  let x := q / E
  have hx : 8 ≤ x := (le_div_iff₀ hE).mpr hratio
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hCup : C ≤ q ^ 2 := by
    have hh := H_gt_parabola (p := (1 - q) / 2) (by linarith) (by linarith)
    dsimp [C]
    nlinarith only [hh]
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have hh := Certificates.PilotData.log_two.2
    norm_num at hh
    linarith
  have hClow : 5 * q ^ 2 / 7 ≤ C := by
    have hh := SmallMean.Cn_ge_half_sq hq.le (by linarith : q ≤ 1)
    change q ^ 2 / 2 ≤ Real.log 2 * C at hh
    have hm := mul_le_mul_of_nonneg_right hL hC
    nlinarith only [hh, hm]
  have hphysical : E + C ≤ 1 := by
    have hsmall := mul_nonneg hq.le (show 0 ≤ 1 / 10 - q by linarith)
    nlinarith only [hCup, hsmall, hratio, hq']
  have hgain := eta_increment_ge_linear_log hE hC hphysical
  have hx0 : 0 ≤ x := by linarith
  have hlogratio : Real.log (1 + q * (10 * x / 7) / 2) ≤ Real.log (1 + C / E) := by
    apply Real.log_le_log (by positivity)
    have hh := div_le_div_of_nonneg_right hClow hE.le
    dsimp [x]
    convert! add_le_add_left hh 1 using 1 <;> ring
  have hscale := logarithmic_bias_scale hq.le hq'
    (show 0 ≤ 10 * x / 7 by positivity)
  have he : 1 + (10 * x / 7) / 20 = 1 + x / 14 := by ring
  rw [he] at hscale
  have hpoly := logarithmic_eight_comparison hx
  have hF : F q E < eta E - eta (E + C) := by
    calc
      F q E ≤ 2 * q * Real.log x / Real.log 2 := F_le_logarithmic_ratio8 hq hE hratio
      _ < 10 * q * Real.log (1 + x / 14) / Real.log 2 := by
        apply div_lt_div_of_pos_right _ log_two_pos
        have hh := mul_lt_mul_of_pos_left hpoly (show 0 < 2 * q by positivity)
        nlinarith only [hh]
      _ ≤ Real.log (1 + q * (10 * x / 7) / 2) / Real.log 2 :=
        div_le_div_of_nonneg_right hscale log_two_pos.le
      _ ≤ Real.log (1 + C / E) / Real.log 2 :=
        div_le_div_of_nonneg_right hlogratio log_two_pos.le
      _ ≤ eta E - eta (E + C) := by linarith only [hgain, hC]
  have habs : |1 - 2 * ((1 - q) / 2)| = q := by
    rw [show 1 - 2 * ((1 - q) / 2) = q by ring, abs_of_pos hq]
  unfold phi psi
  rw [habs]
  have he : E + 1 - H ((1 - q) / 2) = E + C := by dsimp [C]; ring
  rw [he]
  linarith only [hF]

theorem parent_dominance_ratio8_small_bias_of_mean {m E : ℝ} (hE : 0 < E)
    (hq : 0 < 1 - 2 * m) (hq' : 1 - 2 * m ≤ 1 / 10)
    (hratio : 8 * E ≤ 1 - 2 * m) : psi m E < phi m E := by
  have h := parent_dominance_ratio8_small_bias hE hq hq' hratio
  simpa only [show (1 - (1 - 2 * m)) / 2 = m by ring] using h

/-- A strict active-psi parent in the small-bias range must lie on the
other side of the factor-eight line, with the correct strict boundary. -/
theorem activePsi_entropy_gt_eighth {m E : ℝ} (hE : 0 < E)
    (hq : 0 < 1 - 2 * m) (hq' : 1 - 2 * m ≤ 1 / 10)
    (hactive : phi m E < psi m E) : (1 - 2 * m) / 8 < E := by
  by_contra hn
  have hratio : 8 * E ≤ 1 - 2 * m := by linarith
  have h := parent_dominance_ratio8_small_bias_of_mean hE hq hq' hratio
  exact (not_lt_of_ge h.le) hactive

end GeneralCK.PsiParentDominance

#print axioms GeneralCK.PsiParentDominance.F_le_logarithmic
#print axioms GeneralCK.PsiParentDominance.parent_dominance_ratio32
#print axioms GeneralCK.PsiParentDominance.parent_dominance_ratio32_of_mean
#print axioms GeneralCK.PsiParentDominance.F_le_logarithmic_ratio8
#print axioms GeneralCK.PsiParentDominance.parent_dominance_ratio8_small_bias
#print axioms GeneralCK.PsiParentDominance.parent_dominance_ratio8_small_bias_of_mean
#print axioms GeneralCK.PsiParentDominance.activePsi_entropy_gt_eighth

end


