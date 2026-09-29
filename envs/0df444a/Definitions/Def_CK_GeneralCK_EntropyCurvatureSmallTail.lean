-- Prove2me | Definitions.Def_CK_GeneralCK_EntropyCurvatureSmallTail
-- name    : CK_GeneralCK_EntropyCurvatureSmallTail
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:39:41.132303+00:00
-- url     : https://prove2.me/theorems/20624d45-3c91-4aa4-85a0-5ed0ecb70c95
-- title:
--   Courtade–Kumar proof module `GeneralCK.EntropyCurvatureSmallTail` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.EntropyCurvatureSmallTail` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.EntropyCurvatureSmallTail` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.EntropyCurvatureSmallTail (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EntropyCurvatureSmallTail.lean)

import Definitions.Def_CK_GeneralCK_EntropyCurvatureDefs
import Definitions.Def_CK_GeneralCK_SmallMeanAnalytic
import Definitions.Def_CK_GeneralCK_MixedTails

namespace GeneralCK.EntropyCurvature

/-- A conservative rational bound is enough at the small-radius endpoint. -/
theorem polyP_small_lower {x t B : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 12)
    (hx : t ≤ x) (hx' : x ≤ 2 * t) (hB : 2 / 3 ≤ B) (hB' : B ≤ 1) :
    (5 / 27) * t^3 ≤ polyP x t B := by
  have hx0 : 0 ≤ x := ht.trans hx
  have hB0 : 0 ≤ B := by linarith
  have ht2 : t^2 ≤ 1 / 144 := by nlinarith
  have hN : t^3 ≤ x * (1 + t^2) - t := by
    have hh := mul_le_mul_of_nonneg_right hx (show 0 ≤ 1 + t^2 by positivity)
    nlinarith
  have hB3 : (8 / 27 : ℝ) ≤ B^3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2 / 3) hB 3
    norm_num at hh
    exact hh
  have hx3 : x^3 ≤ 8 * t^3 := by
    have hh := pow_le_pow_left₀ hx0 hx' 3
    nlinarith
  have hpos : (8 / 27) * t^3 ≤ B^3 * (x * (1 + t^2) - t) :=
    mul_le_mul hB3 hN (by positivity) (by positivity)
  have hneg : x^3 * t^2 * (2 * B - t^2) ≤ 16 * t^5 := by
    calc
      _ ≤ x^3 * t^2 * 2 := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ ≤ (8 * t^3) * t^2 * 2 := by gcongr
      _ = _ := by ring
  have htail : 16 * t^5 ≤ (1 / 9) * t^3 := by
    have hh := mul_le_mul_of_nonneg_right ht2 (show 0 ≤ 16 * t^3 by positivity)
    nlinarith
  unfold polyP
  linarith

theorem polyR_small_pos {x t B : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 12)
    (hx : t ≤ x) (hx' : x ≤ 2 * t) (hB : 2 / 3 ≤ B) (hB' : B ≤ 1) :
    0 < polyR x t B := by
  have hx0 : 0 ≤ x := ht.trans hx
  have hx1 : x ≤ 1 / 6 := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hB2 : B^2 ≤ 1 := by nlinarith
  have hB3 : (8 / 27 : ℝ) ≤ B^3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2 / 3) hB 3
    norm_num at hh
    exact hh
  have ht2 : t^2 ≤ 1 / 144 := by nlinarith
  have ht3 : t^3 ≤ 1 / 1728 := by
    have hh := pow_le_pow_left₀ ht ht' 3
    norm_num at hh
    exact hh
  have ht5 : t^5 ≤ 1 / 248832 := by
    have hh := pow_le_pow_left₀ ht ht' 5
    norm_num at hh
    exact hh
  have hmain : (32 / 27 : ℝ) ≤ 4 * B^3 * (1 + t^2) := by
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ 1 + t^2 by nlinarith) (show 0 ≤ 4 * B^3 by positivity)
    nlinarith
  have hn₁ : 2 * B^2 * t^3 * x ≤ 1 / 5184 := by
    calc _ ≤ (2 : ℝ) * 1 * (1 / 1728) * (1 / 6) := by gcongr
         _ = _ := by norm_num
  have hn₂ : 8 * B^2 * t^2 ≤ 1 / 18 := by
    calc _ ≤ (8 : ℝ) * 1 * (1 / 144) := by gcongr
         _ = _ := by norm_num
  have hn₃ : 6 * B^2 * t * x ≤ 1 / 12 := by
    calc _ ≤ (6 : ℝ) * 1 * (1 / 12) * (1 / 6) := by gcongr
         _ = _ := by norm_num
  have hn₄ : B * t^5 * x ≤ 1 / 1492992 := by
    calc _ ≤ (1 : ℝ) * (1 / 248832) * (1 / 6) := by gcongr
         _ = _ := by norm_num
  have hn₅ : 3 * t^5 * x ≤ 1 / 497664 := by
    calc _ ≤ (3 : ℝ) * (1 / 248832) * (1 / 6) := by gcongr
         _ = _ := by norm_num
  have hp₁ : 0 ≤ 3 * B * t^4 := by positivity
  have hp₂ : 0 ≤ 9 * B * t^3 * x := by positivity
  unfold polyR
  linarith

theorem small_tail {v : ℝ} (hv : 0 < v) (hl : 11 / 24 ≤ v) (hu : v < 1 / 2) :
    0 < P v ∧ 0 < R v := by
  have ht : 0 < 1 - 2 * v := by linarith
  have ht' : 1 - 2 * v ≤ 1 / 12 := by linarith
  have he : xi v = SmallMean.A (1 - 2 * v) := by
    rw [SmallMean.A_eq_J, show (1 - (1 - 2 * v)) / 2 = v by ring]
    unfold xi
    ring
  have hx : 1 - 2 * v ≤ xi v := by
    rw [he]
    exact SmallMean.A_lower ht.le (by linarith)
  have hx' : xi v ≤ 2 * (1 - 2 * v) := by
    rw [he]
    apply (SmallMean.A_upper ht.le (by linarith)).trans
    apply (div_le_iff₀ (show 0 < 1 - (1 - 2 * v)^2 by nlinarith)).2
    have hh : (1 - 2 * v)^2 ≤ 1 / 144 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hh ht.le
    nlinarith
  have hB : (2 / 3 : ℝ) ≤ Certificates.Mixed.kap v := by
    have hp : 0 < v * (1 - v) := mul_pos hv (by linarith)
    have hlp := Real.log_le_log hp (show v * (1 - v) ≤ 1 / 4 by nlinarith [sq_nonneg (v - 1 / 2)])
    have hlq : Real.log (1 / 4 : ℝ) = -2 * Real.log 2 := by
      rw [show (1 / 4 : ℝ) = ((2 : ℝ)^2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
      ring
    rw [hlq] at hlp
    have hlog := Certificates.Mixed.log_two_gt_69
    unfold Certificates.Mixed.kap
    linarith
  have hB' : Certificates.Mixed.kap v ≤ 1 :=
    Certificates.Mixed.Tails.kap_le_one_right (by linarith) hu.le
  constructor
  · have hp := polyP_small_lower ht.le ht' hx hx' hB hB'
    have hpos : 0 < (5 / 27 : ℝ) * (1 - 2 * v)^3 := by positivity
    exact hpos.trans_le hp
  · exact polyR_small_pos ht.le ht' hx hx' hB hB'

end GeneralCK.EntropyCurvature


