-- Prove2me | Definitions.Def_CK_CKLaneN4_LU_Origin
-- name    : CK_CKLaneN4_LU_Origin
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T12:46:36.636323+00:00
-- url     : https://prove2.me/theorems/4e525004-bbb2-4af0-a54c-b12877775138
-- title:
--   Courtade–Kumar proof module `CKLaneN4.LU.Origin` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.LU.Origin` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.LU.Origin` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.LU.Origin (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/LU/Origin.lean)

import Definitions.Def_CK_CKLaneN4_LU_Convex

-- ===== source module CKLaneN4.LU.Origin =====
section
/-
Lane N4b — the left-upper value near the origin: `0 < a < b ≤ 1/256 ⇒ 0 ≤ Gexpr a b`.

Crude but complete analytic bounds (u = entropyInverse h, h = (H a + H b)/2, a ≤ u ≤ b):
* interiorCost ≥ 0;
* radialContact (1/2 - a) h ≤ 4u (from H(4u) ≥ (9/4) H(u)), hence 2F(1/2-a,h) - eta h ≥ -3;
* radialContact (b - a) h ≥ 1/4 (from H b ≥ 8 b), hence F(b-a,h) ≤ 2 b;
* kfun b / 2 ≥ (127/128)·7/2 (J b ≥ J(1/256) ≥ 7).
-/

set_option autoImplicit false

namespace CKLaneN4.LU

open GeneralCK Set

theorem log2_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem binEntropy_eq' (x : ℝ) :
    Real.binEntropy x = -(x * Real.log x) - (1 - x) * Real.log (1 - x) := by
  simp only [Real.binEntropy, Real.log_inv]
  ring

theorem H_mul_log (x : ℝ) : H x * Real.log 2 = -(x * Real.log x) - (1 - x) * Real.log (1 - x) := by
  unfold H
  rw [div_mul_cancel₀ _ log2_pos'.ne', binEntropy_eq']

theorem H_mul_log_lower {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    -(x * Real.log x) ≤ H x * Real.log 2 := by
  rw [H_mul_log]
  have : Real.log (1 - x) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  nlinarith

theorem H_mul_log_upper {x : ℝ} (hx1 : x < 1) :
    H x * Real.log 2 ≤ -(x * Real.log x) + x := by
  rw [H_mul_log]
  have h1x : 0 < 1 - x := by linarith
  have hl := Real.log_le_sub_one_of_pos (inv_pos.2 h1x)
  rw [Real.log_inv] at hl
  have hm := mul_le_mul_of_nonneg_left hl h1x.le
  have e : (1 - x) * ((1 - x)⁻¹ - 1) = x := by field_simp; ring
  rw [e] at hm
  linarith

/-- `-log x ≥ 8 log 2` for `0 < x ≤ 1/256`. -/
theorem neglog_ge {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1 / 256) : 8 * Real.log 2 ≤ -Real.log x := by
  have h := Real.log_le_log hx hx1
  have e : Real.log (1 / 256 : ℝ) = -(8 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    push_cast; ring
  linarith

theorem H_four_mul {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1 / 256) : 9 / 4 * H u ≤ H (4 * u) := by
  have hL := log2_pos'
  have hL' : (3 : ℝ) / 8 < Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at this
    linarith
  have hlo := H_mul_log_lower (x := 4 * u) (by linarith) (by linarith)
  have hup := H_mul_log_upper (x := u) (by linarith)
  have hl4 : Real.log (4 * u) = 2 * Real.log 2 + Real.log u := by
    rw [Real.log_mul (by norm_num) hu.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hℓ := neglog_ge hu hu1
  rw [hl4] at hlo
  -- L H(4u) ≥ 4u(ℓ - 2L) ≥ (9/4)(uℓ + u) ≥ (9/4) L H(u)
  have key : 9 / 4 * (H u * Real.log 2) ≤ H (4 * u) * Real.log 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hℓ hu.le]
  have := (mul_le_mul_iff_of_pos_right hL).1 (by linarith [key] :
    9 / 4 * H u * Real.log 2 ≤ H (4 * u) * Real.log 2)
  linarith

theorem J_four_mul {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1 / 7) : J u - 3 ≤ J (4 * u) := by
  have hL := log2_pos'
  unfold J
  have h1 : 0 < (1 - u) / u := div_pos (by linarith) hu
  have h2 : 0 < (1 - 4 * u) / (4 * u) := div_pos (by linarith) (by linarith)
  have hcmp : (1 - u) / u / 8 ≤ (1 - 4 * u) / (4 * u) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hl := Real.log_le_log (by positivity) hcmp
  rw [Real.log_div h1.ne' (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at hl
  push_cast at hl
  rw [div_sub' (ne_of_gt hL), div_le_div_iff_of_pos_right hL]
  linarith

theorem J_quarter_le : J (1 / 4) ≤ 2 := by
  have hL := log2_pos'
  unfold J
  rw [div_le_iff₀ hL]
  have : Real.log ((1 - 1 / 4) / (1 / 4) : ℝ) ≤ Real.log 4 :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at this
  push_cast at this
  linarith

theorem J_256_ge : 7 ≤ J (1 / 256) := by
  have hL := log2_pos'
  unfold J
  rw [le_div_iff₀ hL]
  have : Real.log 128 ≤ Real.log ((1 - 1 / 256) / (1 / 256) : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow] at this
  push_cast at this
  linarith

theorem origin_nonneg {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 256) :
    0 ≤ Gexpr a b := by
  have hL := log2_pos'
  have hb0 : 0 < b := ha.trans hab
  have hbh : b < 1 / 2 := by linarith
  set h := hAvg a b with hh
  have hHa := H_nonneg ha.le (by linarith : a ≤ 1)
  have hHb := H_pos hb0 (by linarith : b < 1)
  have hHab : H a ≤ H b := H_strictMonoOn.monotoneOn ⟨ha.le, by linarith⟩ ⟨hb0.le, hbh.le⟩ hab.le
  have hhpos : 0 < h := by rw [hh]; unfold hAvg; linarith
  have hhle : h ≤ H b := by rw [hh]; unfold hAvg; linarith
  have hhge : H a ≤ h := by rw [hh]; unfold hAvg; linarith
  have hh1 : h ≤ 1 := hhle.trans (H_le_one b)
  -- u = entropyInverse h
  set u := entropyInverse h with hu
  obtain ⟨hu0, hu_half, hHu⟩ := entropyInverse_spec hhpos.le hh1
  have hupos : 0 < u := entropyInverse_pos hhpos hh1
  have hub : u ≤ b := by
    have := entropyInverse_mono hhpos.le (H_le_one b) hhle
    rwa [entropyInverse_H_lower hb0.le hbh.le] at this
  have hau : a ≤ u := by
    have := entropyInverse_mono hHa (hh1) hhge
    rwa [entropyInverse_H_lower ha.le (by linarith)] at this
  have hu256 : u ≤ 1 / 256 := hub.trans hb
  -- eta
  have heta : eta h = (1 - 2 * u) * J u := eta_eq_profile hhpos.le hh1
  -- contact of (1/2 - a) is ≤ 4u
  have hz : 0 < 1 / 2 - a := by linarith
  have h4u : 4 * u ≤ 1 / 2 := by linarith
  have hcont : radialContact (1 / 2 - a) h ≤ 4 * u := by
    rw [radialContact_le_iff hz hhpos (by linarith) h4u]
    have h94 := H_four_mul hupos hu256
    have hHu' : H u = h := by rw [hu]; exact hHu
    have hHu0 : 0 ≤ H u := H_nonneg hupos.le (by linarith)
    have hm : (1 / 2 - a) * (9 / 4 * H u) ≤ (1 / 2 - a) * H (4 * u) :=
      mul_le_mul_of_nonneg_left h94 hz.le
    have ha' : a ≤ 1 / 256 := by linarith
    have hbr : (0 : ℝ) ≤ (1 / 2 - a) * (9 / 4) - 1 + 8 * u := by nlinarith
    have hprod := mul_nonneg hHu0 hbr
    rw [← hHu']
    nlinarith [hm, hprod]
  have hcpos := radialContact_pos hz hhpos
  have hJ4 : J (4 * u) ≤ J (radialContact (1 / 2 - a) h) := J_antitone hcpos h4u hcont
  have hJu4 := J_four_mul hupos (by linarith)
  have hJu0 : 0 ≤ J u := J_nonneg hupos hu_half
  have hF1 : (1 / 2 - a) * J (4 * u) ≤ F (1 / 2 - a) h := by
    simp only [F, hz.ne', if_false]
    exact mul_le_mul_of_nonneg_left hJ4 hz.le
  -- contact of (b - a) is ≥ 1/4
  have hd : 0 < b - a := by linarith
  have hHb8 : 8 * b ≤ H b := by
    have hlo := H_mul_log_lower hb0 (by linarith : b < 1)
    have hℓ := neglog_ge hb0 hb
    have hm := mul_le_mul_of_nonneg_left hℓ hb0.le
    have : 8 * b * Real.log 2 ≤ H b * Real.log 2 := by linarith
    exact (mul_le_mul_iff_of_pos_right hL).1 this
  have hcont2 : 1 / 4 ≤ radialContact (b - a) h := by
    rw [le_radialContact_iff hd hhpos (by norm_num) (by norm_num)]
    have hq := H_le_one (1 / 4)
    have hq0 : 0 ≤ H (1 / 4) := H_nonneg (by norm_num) (by norm_num)
    have : (b - a) * H (1 / 4) ≤ (b - a) := by nlinarith
    rw [hh]; unfold hAvg; linarith
  have hc2lt := radialContact_lt_half hd hhpos
  have hJq : J (radialContact (b - a) h) ≤ J (1 / 4) :=
    J_antitone (by norm_num) hc2lt.le hcont2
  have hF2 : F (b - a) h ≤ 2 * b := by
    simp only [F, hd.ne', if_false]
    have := mul_le_mul_of_nonneg_left (hJq.trans J_quarter_le) hd.le
    linarith
  -- kfun
  have hJb : 7 ≤ J b := J_256_ge.trans (J_antitone hb0 (by norm_num) hb)
  have hk : 127 / 128 * 7 ≤ kfun b := by
    unfold kfun
    have : (127 / 128 : ℝ) ≤ 1 - 2 * b := by linarith
    exact mul_le_mul this hJb (by norm_num) (by linarith)
  -- interior cost
  have hic : 0 ≤ interiorCost a b := by
    unfold interiorCost
    have := J_antitone ha hbh.le hab.le
    have : 0 ≤ (b - a) * (J a - J b) := mul_nonneg hd.le (by linarith)
    linarith
  -- assemble
  have hmain : -3 ≤ 2 * F (1 / 2 - a) h - eta h := by
    rw [heta]
    have h2a : 0 ≤ 1 - 2 * a := by linarith
    have hA : (1 - 2 * a) * (J u - 3) ≤ (1 - 2 * a) * J (4 * u) :=
      mul_le_mul_of_nonneg_left hJu4 h2a
    have hB : 0 ≤ (2 * u - 2 * a) * J u := mul_nonneg (by linarith) hJu0
    linarith [hF1, hA, hB, ha]
  unfold Gexpr Cfun Vfun
  rw [← hh]
  linarith [hic, hmain, hk, hF2, hb]

end CKLaneN4.LU

end


