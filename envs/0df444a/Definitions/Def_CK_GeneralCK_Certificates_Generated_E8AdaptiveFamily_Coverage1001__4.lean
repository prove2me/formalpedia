-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage1001__4
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage1001__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:13:48.011187+00:00
-- url     : https://prove2.me/theorems/861bdcaa-fe92-4aef-84fb-5a0af0f622d8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1001 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1002, GeneralCK.Certific…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1001 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1002, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1003, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1010)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1001 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1002, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1003, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1010)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1001 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1002, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1003, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1010) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1001 (+3 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1002, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1003, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1010).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0197
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0198
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0199
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0200
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0201
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0202
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0370
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0371
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0372
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0373
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0374
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0375
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0376
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0377
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0378
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0379
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0380
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0069
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0070
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0071
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0072
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0073
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0203
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0204
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0205
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0381
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0382
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0383
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0384
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0385
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0386
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0387
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0388
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0389
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0390
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0391

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1001 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1001

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_1001100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (5/64) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/40)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1001101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (27/320) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/160)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1001110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (29/320) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/80)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1001111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/320) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/32)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (33/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/20)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/128) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-17/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (37/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (39/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-19/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (41/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/16)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (43/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/128) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010113 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/640) (-253/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/320)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10011120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (57/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/80)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10011121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (59/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10011130 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (61/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/32)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10011131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (-3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx1001 | hx1001
  · rcases le_total tau.im (-3/8 : ℝ) with hy1001 | hy1001
    · have hs10010 : InSquare (1/16) (-31/80) (1/80) tau := by
        convert childLL hs hx1001 hy1001 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx10010 | hx10010
      · rcases le_total tau.im (-31/80 : ℝ) with hy10010 | hy10010
        · have hs100100 : InSquare (9/160) (-63/160) (1/160) tau := by
            convert childLL hs10010 hx10010 hy10010 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx100100 | hx100100
          · rcases le_total tau.im (-63/160 : ℝ) with hy100100 | hy100100
            · have hs1001000 : InSquare (17/320) (-127/320) (1/320) tau := by
                convert childLL hs100100 hx100100 hy100100 using 1 <;> norm_num
              rcases le_total tau.re (17/320 : ℝ) with hx1001000 | hx1001000
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001000 | hy1001000
                · have hs10010000 : InSquare (33/640) (-51/128) (1/640) tau := by
                    convert childLL hs1001000 hx1001000 hy1001000 using 1 <;> norm_num
                  exact (outside_10010000 htau hs10010000).elim
                · have hs10010002 : InSquare (33/640) (-253/640) (1/640) tau := by
                    convert childUL hs1001000 hx1001000 hy1001000 using 1 <;> norm_num
                  exact Batch0370.cell2960.sound htau (by
                    simp only [Batch0370.cell2960, Batch0370.tau2960, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001000 | hy1001000
                · have hs10010001 : InSquare (7/128) (-51/128) (1/640) tau := by
                    convert childLR hs1001000 hx1001000 hy1001000 using 1 <;> norm_num
                  exact (outside_10010001 htau hs10010001).elim
                · have hs10010003 : InSquare (7/128) (-253/640) (1/640) tau := by
                    convert childUR hs1001000 hx1001000 hy1001000 using 1 <;> norm_num
                  exact Batch0370.cell2961.sound htau (by
                    simp only [Batch0370.cell2961, Batch0370.tau2961, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010003 (by positivity) using 1 <;> norm_num)
            · have hs1001002 : InSquare (17/320) (-25/64) (1/320) tau := by
                convert childUL hs100100 hx100100 hy100100 using 1 <;> norm_num
              rcases le_total tau.re (17/320 : ℝ) with hx1001002 | hx1001002
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001002 | hy1001002
                · have hs10010020 : InSquare (33/640) (-251/640) (1/640) tau := by
                    convert childLL hs1001002 hx1001002 hy1001002 using 1 <;> norm_num
                  exact Batch0370.cell2964.sound htau (by
                    simp only [Batch0370.cell2964, Batch0370.tau2964, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010020 (by positivity) using 1 <;> norm_num)
                · have hs10010022 : InSquare (33/640) (-249/640) (1/640) tau := by
                    convert childUL hs1001002 hx1001002 hy1001002 using 1 <;> norm_num
                  exact Batch0370.cell2966.sound htau (by
                    simp only [Batch0370.cell2966, Batch0370.tau2966, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001002 | hy1001002
                · have hs10010021 : InSquare (7/128) (-251/640) (1/640) tau := by
                    convert childLR hs1001002 hx1001002 hy1001002 using 1 <;> norm_num
                  exact Batch0370.cell2965.sound htau (by
                    simp only [Batch0370.cell2965, Batch0370.tau2965, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010021 (by positivity) using 1 <;> norm_num)
                · have hs10010023 : InSquare (7/128) (-249/640) (1/640) tau := by
                    convert childUR hs1001002 hx1001002 hy1001002 using 1 <;> norm_num
                  exact Batch0370.cell2967.sound htau (by
                    simp only [Batch0370.cell2967, Batch0370.tau2967, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy100100 | hy100100
            · have hs1001001 : InSquare (19/320) (-127/320) (1/320) tau := by
                convert childLR hs100100 hx100100 hy100100 using 1 <;> norm_num
              rcases le_total tau.re (19/320 : ℝ) with hx1001001 | hx1001001
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001001 | hy1001001
                · have hs10010010 : InSquare (37/640) (-51/128) (1/640) tau := by
                    convert childLL hs1001001 hx1001001 hy1001001 using 1 <;> norm_num
                  exact (outside_10010010 htau hs10010010).elim
                · have hs10010012 : InSquare (37/640) (-253/640) (1/640) tau := by
                    convert childUL hs1001001 hx1001001 hy1001001 using 1 <;> norm_num
                  exact Batch0370.cell2962.sound htau (by
                    simp only [Batch0370.cell2962, Batch0370.tau2962, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001001 | hy1001001
                · have hs10010011 : InSquare (39/640) (-51/128) (1/640) tau := by
                    convert childLR hs1001001 hx1001001 hy1001001 using 1 <;> norm_num
                  exact (outside_10010011 htau hs10010011).elim
                · have hs10010013 : InSquare (39/640) (-253/640) (1/640) tau := by
                    convert childUR hs1001001 hx1001001 hy1001001 using 1 <;> norm_num
                  exact Batch0370.cell2963.sound htau (by
                    simp only [Batch0370.cell2963, Batch0370.tau2963, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010013 (by positivity) using 1 <;> norm_num)
            · have hs1001003 : InSquare (19/320) (-25/64) (1/320) tau := by
                convert childUR hs100100 hx100100 hy100100 using 1 <;> norm_num
              rcases le_total tau.re (19/320 : ℝ) with hx1001003 | hx1001003
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001003 | hy1001003
                · have hs10010030 : InSquare (37/640) (-251/640) (1/640) tau := by
                    convert childLL hs1001003 hx1001003 hy1001003 using 1 <;> norm_num
                  exact Batch0371.cell2968.sound htau (by
                    simp only [Batch0371.cell2968, Batch0371.tau2968, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010030 (by positivity) using 1 <;> norm_num)
                · have hs10010032 : InSquare (37/640) (-249/640) (1/640) tau := by
                    convert childUL hs1001003 hx1001003 hy1001003 using 1 <;> norm_num
                  exact Batch0371.cell2970.sound htau (by
                    simp only [Batch0371.cell2970, Batch0371.tau2970, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001003 | hy1001003
                · have hs10010031 : InSquare (39/640) (-251/640) (1/640) tau := by
                    convert childLR hs1001003 hx1001003 hy1001003 using 1 <;> norm_num
                  exact Batch0371.cell2969.sound htau (by
                    simp only [Batch0371.cell2969, Batch0371.tau2969, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010031 (by positivity) using 1 <;> norm_num)
                · have hs10010033 : InSquare (39/640) (-249/640) (1/640) tau := by
                    convert childUR hs1001003 hx1001003 hy1001003 using 1 <;> norm_num
                  exact Batch0371.cell2971.sound htau (by
                    simp only [Batch0371.cell2971, Batch0371.tau2971, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010033 (by positivity) using 1 <;> norm_num)
        · have hs100102 : InSquare (9/160) (-61/160) (1/160) tau := by
            convert childUL hs10010 hx10010 hy10010 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx100102 | hx100102
          · rcases le_total tau.im (-61/160 : ℝ) with hy100102 | hy100102
            · have hs1001020 : InSquare (17/320) (-123/320) (1/320) tau := by
                convert childLL hs100102 hx100102 hy100102 using 1 <;> norm_num
              rcases le_total tau.re (17/320 : ℝ) with hx1001020 | hx1001020
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001020 | hy1001020
                · have hs10010200 : InSquare (33/640) (-247/640) (1/640) tau := by
                    convert childLL hs1001020 hx1001020 hy1001020 using 1 <;> norm_num
                  exact Batch0372.cell2983.sound htau (by
                    simp only [Batch0372.cell2983, Batch0372.tau2983, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010200 (by positivity) using 1 <;> norm_num)
                · have hs10010202 : InSquare (33/640) (-49/128) (1/640) tau := by
                    convert childUL hs1001020 hx1001020 hy1001020 using 1 <;> norm_num
                  exact Batch0373.cell2985.sound htau (by
                    simp only [Batch0373.cell2985, Batch0373.tau2985, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001020 | hy1001020
                · have hs10010201 : InSquare (7/128) (-247/640) (1/640) tau := by
                    convert childLR hs1001020 hx1001020 hy1001020 using 1 <;> norm_num
                  exact Batch0373.cell2984.sound htau (by
                    simp only [Batch0373.cell2984, Batch0373.tau2984, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010201 (by positivity) using 1 <;> norm_num)
                · have hs10010203 : InSquare (7/128) (-49/128) (1/640) tau := by
                    convert childUR hs1001020 hx1001020 hy1001020 using 1 <;> norm_num
                  exact Batch0373.cell2986.sound htau (by
                    simp only [Batch0373.cell2986, Batch0373.tau2986, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010203 (by positivity) using 1 <;> norm_num)
            · have hs1001022 : InSquare (17/320) (-121/320) (1/320) tau := by
                convert childUL hs100102 hx100102 hy100102 using 1 <;> norm_num
              exact Batch0197.cell1582.sound htau (by
                simp only [Batch0197.cell1582, Batch0197.tau1582, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy100102 | hy100102
            · have hs1001021 : InSquare (19/320) (-123/320) (1/320) tau := by
                convert childLR hs100102 hx100102 hy100102 using 1 <;> norm_num
              rcases le_total tau.re (19/320 : ℝ) with hx1001021 | hx1001021
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001021 | hy1001021
                · have hs10010210 : InSquare (37/640) (-247/640) (1/640) tau := by
                    convert childLL hs1001021 hx1001021 hy1001021 using 1 <;> norm_num
                  exact Batch0373.cell2987.sound htau (by
                    simp only [Batch0373.cell2987, Batch0373.tau2987, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010210 (by positivity) using 1 <;> norm_num)
                · have hs10010212 : InSquare (37/640) (-49/128) (1/640) tau := by
                    convert childUL hs1001021 hx1001021 hy1001021 using 1 <;> norm_num
                  exact Batch0373.cell2989.sound htau (by
                    simp only [Batch0373.cell2989, Batch0373.tau2989, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001021 | hy1001021
                · have hs10010211 : InSquare (39/640) (-247/640) (1/640) tau := by
                    convert childLR hs1001021 hx1001021 hy1001021 using 1 <;> norm_num
                  exact Batch0373.cell2988.sound htau (by
                    simp only [Batch0373.cell2988, Batch0373.tau2988, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010211 (by positivity) using 1 <;> norm_num)
                · have hs10010213 : InSquare (39/640) (-49/128) (1/640) tau := by
                    convert childUR hs1001021 hx1001021 hy1001021 using 1 <;> norm_num
                  exact Batch0373.cell2990.sound htau (by
                    simp only [Batch0373.cell2990, Batch0373.tau2990, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010213 (by positivity) using 1 <;> norm_num)
            · have hs1001023 : InSquare (19/320) (-121/320) (1/320) tau := by
                convert childUR hs100102 hx100102 hy100102 using 1 <;> norm_num
              exact Batch0197.cell1583.sound htau (by
                simp only [Batch0197.cell1583, Batch0197.tau1583, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy10010 | hy10010
        · have hs100101 : InSquare (11/160) (-63/160) (1/160) tau := by
            convert childLR hs10010 hx10010 hy10010 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx100101 | hx100101
          · rcases le_total tau.im (-63/160 : ℝ) with hy100101 | hy100101
            · have hs1001010 : InSquare (21/320) (-127/320) (1/320) tau := by
                convert childLL hs100101 hx100101 hy100101 using 1 <;> norm_num
              rcases le_total tau.re (21/320 : ℝ) with hx1001010 | hx1001010
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001010 | hy1001010
                · have hs10010100 : InSquare (41/640) (-51/128) (1/640) tau := by
                    convert childLL hs1001010 hx1001010 hy1001010 using 1 <;> norm_num
                  exact (outside_10010100 htau hs10010100).elim
                · have hs10010102 : InSquare (41/640) (-253/640) (1/640) tau := by
                    convert childUL hs1001010 hx1001010 hy1001010 using 1 <;> norm_num
                  exact Batch0371.cell2972.sound htau (by
                    simp only [Batch0371.cell2972, Batch0371.tau2972, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001010 | hy1001010
                · have hs10010101 : InSquare (43/640) (-51/128) (1/640) tau := by
                    convert childLR hs1001010 hx1001010 hy1001010 using 1 <;> norm_num
                  exact (outside_10010101 htau hs10010101).elim
                · have hs10010103 : InSquare (43/640) (-253/640) (1/640) tau := by
                    convert childUR hs1001010 hx1001010 hy1001010 using 1 <;> norm_num
                  exact Batch0371.cell2973.sound htau (by
                    simp only [Batch0371.cell2973, Batch0371.tau2973, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010103 (by positivity) using 1 <;> norm_num)
            · have hs1001012 : InSquare (21/320) (-25/64) (1/320) tau := by
                convert childUL hs100101 hx100101 hy100101 using 1 <;> norm_num
              rcases le_total tau.re (21/320 : ℝ) with hx1001012 | hx1001012
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001012 | hy1001012
                · have hs10010120 : InSquare (41/640) (-251/640) (1/640) tau := by
                    convert childLL hs1001012 hx1001012 hy1001012 using 1 <;> norm_num
                  exact Batch0371.cell2975.sound htau (by
                    simp only [Batch0371.cell2975, Batch0371.tau2975, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010120 (by positivity) using 1 <;> norm_num)
                · have hs10010122 : InSquare (41/640) (-249/640) (1/640) tau := by
                    convert childUL hs1001012 hx1001012 hy1001012 using 1 <;> norm_num
                  exact Batch0372.cell2977.sound htau (by
                    simp only [Batch0372.cell2977, Batch0372.tau2977, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001012 | hy1001012
                · have hs10010121 : InSquare (43/640) (-251/640) (1/640) tau := by
                    convert childLR hs1001012 hx1001012 hy1001012 using 1 <;> norm_num
                  exact Batch0372.cell2976.sound htau (by
                    simp only [Batch0372.cell2976, Batch0372.tau2976, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010121 (by positivity) using 1 <;> norm_num)
                · have hs10010123 : InSquare (43/640) (-249/640) (1/640) tau := by
                    convert childUR hs1001012 hx1001012 hy1001012 using 1 <;> norm_num
                  exact Batch0372.cell2978.sound htau (by
                    simp only [Batch0372.cell2978, Batch0372.tau2978, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy100101 | hy100101
            · have hs1001011 : InSquare (23/320) (-127/320) (1/320) tau := by
                convert childLR hs100101 hx100101 hy100101 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx1001011 | hx1001011
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001011 | hy1001011
                · have hs10010110 : InSquare (9/128) (-51/128) (1/640) tau := by
                    convert childLL hs1001011 hx1001011 hy1001011 using 1 <;> norm_num
                  exact (outside_10010110 htau hs10010110).elim
                · have hs10010112 : InSquare (9/128) (-253/640) (1/640) tau := by
                    convert childUL hs1001011 hx1001011 hy1001011 using 1 <;> norm_num
                  exact Batch0371.cell2974.sound htau (by
                    simp only [Batch0371.cell2974, Batch0371.tau2974, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001011 | hy1001011
                · have hs10010111 : InSquare (47/640) (-51/128) (1/640) tau := by
                    convert childLR hs1001011 hx1001011 hy1001011 using 1 <;> norm_num
                  exact (outside_10010111 htau hs10010111).elim
                · have hs10010113 : InSquare (47/640) (-253/640) (1/640) tau := by
                    convert childUR hs1001011 hx1001011 hy1001011 using 1 <;> norm_num
                  exact (outside_10010113 htau hs10010113).elim
            · have hs1001013 : InSquare (23/320) (-25/64) (1/320) tau := by
                convert childUR hs100101 hx100101 hy100101 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx1001013 | hx1001013
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001013 | hy1001013
                · have hs10010130 : InSquare (9/128) (-251/640) (1/640) tau := by
                    convert childLL hs1001013 hx1001013 hy1001013 using 1 <;> norm_num
                  exact Batch0372.cell2979.sound htau (by
                    simp only [Batch0372.cell2979, Batch0372.tau2979, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010130 (by positivity) using 1 <;> norm_num)
                · have hs10010132 : InSquare (9/128) (-249/640) (1/640) tau := by
                    convert childUL hs1001013 hx1001013 hy1001013 using 1 <;> norm_num
                  exact Batch0372.cell2981.sound htau (by
                    simp only [Batch0372.cell2981, Batch0372.tau2981, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001013 | hy1001013
                · have hs10010131 : InSquare (47/640) (-251/640) (1/640) tau := by
                    convert childLR hs1001013 hx1001013 hy1001013 using 1 <;> norm_num
                  exact Batch0372.cell2980.sound htau (by
                    simp only [Batch0372.cell2980, Batch0372.tau2980, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010131 (by positivity) using 1 <;> norm_num)
                · have hs10010133 : InSquare (47/640) (-249/640) (1/640) tau := by
                    convert childUR hs1001013 hx1001013 hy1001013 using 1 <;> norm_num
                  exact Batch0372.cell2982.sound htau (by
                    simp only [Batch0372.cell2982, Batch0372.tau2982, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010133 (by positivity) using 1 <;> norm_num)
        · have hs100103 : InSquare (11/160) (-61/160) (1/160) tau := by
            convert childUR hs10010 hx10010 hy10010 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx100103 | hx100103
          · rcases le_total tau.im (-61/160 : ℝ) with hy100103 | hy100103
            · have hs1001030 : InSquare (21/320) (-123/320) (1/320) tau := by
                convert childLL hs100103 hx100103 hy100103 using 1 <;> norm_num
              rcases le_total tau.re (21/320 : ℝ) with hx1001030 | hx1001030
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001030 | hy1001030
                · have hs10010300 : InSquare (41/640) (-247/640) (1/640) tau := by
                    convert childLL hs1001030 hx1001030 hy1001030 using 1 <;> norm_num
                  exact Batch0373.cell2991.sound htau (by
                    simp only [Batch0373.cell2991, Batch0373.tau2991, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010300 (by positivity) using 1 <;> norm_num)
                · have hs10010302 : InSquare (41/640) (-49/128) (1/640) tau := by
                    convert childUL hs1001030 hx1001030 hy1001030 using 1 <;> norm_num
                  exact Batch0374.cell2993.sound htau (by
                    simp only [Batch0374.cell2993, Batch0374.tau2993, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001030 | hy1001030
                · have hs10010301 : InSquare (43/640) (-247/640) (1/640) tau := by
                    convert childLR hs1001030 hx1001030 hy1001030 using 1 <;> norm_num
                  exact Batch0374.cell2992.sound htau (by
                    simp only [Batch0374.cell2992, Batch0374.tau2992, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010301 (by positivity) using 1 <;> norm_num)
                · have hs10010303 : InSquare (43/640) (-49/128) (1/640) tau := by
                    convert childUR hs1001030 hx1001030 hy1001030 using 1 <;> norm_num
                  exact Batch0374.cell2994.sound htau (by
                    simp only [Batch0374.cell2994, Batch0374.tau2994, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010303 (by positivity) using 1 <;> norm_num)
            · have hs1001032 : InSquare (21/320) (-121/320) (1/320) tau := by
                convert childUL hs100103 hx100103 hy100103 using 1 <;> norm_num
              exact Batch0198.cell1584.sound htau (by
                simp only [Batch0198.cell1584, Batch0198.tau1584, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy100103 | hy100103
            · have hs1001031 : InSquare (23/320) (-123/320) (1/320) tau := by
                convert childLR hs100103 hx100103 hy100103 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx1001031 | hx1001031
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001031 | hy1001031
                · have hs10010310 : InSquare (9/128) (-247/640) (1/640) tau := by
                    convert childLL hs1001031 hx1001031 hy1001031 using 1 <;> norm_num
                  exact Batch0374.cell2995.sound htau (by
                    simp only [Batch0374.cell2995, Batch0374.tau2995, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010310 (by positivity) using 1 <;> norm_num)
                · have hs10010312 : InSquare (9/128) (-49/128) (1/640) tau := by
                    convert childUL hs1001031 hx1001031 hy1001031 using 1 <;> norm_num
                  exact Batch0374.cell2997.sound htau (by
                    simp only [Batch0374.cell2997, Batch0374.tau2997, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001031 | hy1001031
                · have hs10010311 : InSquare (47/640) (-247/640) (1/640) tau := by
                    convert childLR hs1001031 hx1001031 hy1001031 using 1 <;> norm_num
                  exact Batch0374.cell2996.sound htau (by
                    simp only [Batch0374.cell2996, Batch0374.tau2996, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010311 (by positivity) using 1 <;> norm_num)
                · have hs10010313 : InSquare (47/640) (-49/128) (1/640) tau := by
                    convert childUR hs1001031 hx1001031 hy1001031 using 1 <;> norm_num
                  exact Batch0374.cell2998.sound htau (by
                    simp only [Batch0374.cell2998, Batch0374.tau2998, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010313 (by positivity) using 1 <;> norm_num)
            · have hs1001033 : InSquare (23/320) (-121/320) (1/320) tau := by
                convert childUR hs100103 hx100103 hy100103 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx1001033 | hx1001033
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001033 | hy1001033
                · have hs10010330 : InSquare (9/128) (-243/640) (1/640) tau := by
                    convert childLL hs1001033 hx1001033 hy1001033 using 1 <;> norm_num
                  exact Batch0374.cell2999.sound htau (by
                    simp only [Batch0374.cell2999, Batch0374.tau2999, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010330 (by positivity) using 1 <;> norm_num)
                · have hs10010332 : InSquare (9/128) (-241/640) (1/640) tau := by
                    convert childUL hs1001033 hx1001033 hy1001033 using 1 <;> norm_num
                  exact Batch0375.cell3001.sound htau (by
                    simp only [Batch0375.cell3001, Batch0375.tau3001, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001033 | hy1001033
                · have hs10010331 : InSquare (47/640) (-243/640) (1/640) tau := by
                    convert childLR hs1001033 hx1001033 hy1001033 using 1 <;> norm_num
                  exact Batch0375.cell3000.sound htau (by
                    simp only [Batch0375.cell3000, Batch0375.tau3000, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010331 (by positivity) using 1 <;> norm_num)
                · have hs10010333 : InSquare (47/640) (-241/640) (1/640) tau := by
                    convert childUR hs1001033 hx1001033 hy1001033 using 1 <;> norm_num
                  exact Batch0375.cell3002.sound htau (by
                    simp only [Batch0375.cell3002, Batch0375.tau3002, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010333 (by positivity) using 1 <;> norm_num)
    · have hs10012 : InSquare (1/16) (-29/80) (1/80) tau := by
        convert childUL hs hx1001 hy1001 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx10012 | hx10012
      · rcases le_total tau.im (-29/80 : ℝ) with hy10012 | hy10012
        · have hs100120 : InSquare (9/160) (-59/160) (1/160) tau := by
            convert childLL hs10012 hx10012 hy10012 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx100120 | hx100120
          · rcases le_total tau.im (-59/160 : ℝ) with hy100120 | hy100120
            · have hs1001200 : InSquare (17/320) (-119/320) (1/320) tau := by
                convert childLL hs100120 hx100120 hy100120 using 1 <;> norm_num
              exact Batch0198.cell1585.sound htau (by
                simp only [Batch0198.cell1585, Batch0198.tau1585, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001200 (by positivity) using 1 <;> norm_num)
            · have hs1001202 : InSquare (17/320) (-117/320) (1/320) tau := by
                convert childUL hs100120 hx100120 hy100120 using 1 <;> norm_num
              exact Batch0198.cell1587.sound htau (by
                simp only [Batch0198.cell1587, Batch0198.tau1587, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy100120 | hy100120
            · have hs1001201 : InSquare (19/320) (-119/320) (1/320) tau := by
                convert childLR hs100120 hx100120 hy100120 using 1 <;> norm_num
              exact Batch0198.cell1586.sound htau (by
                simp only [Batch0198.cell1586, Batch0198.tau1586, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001201 (by positivity) using 1 <;> norm_num)
            · have hs1001203 : InSquare (19/320) (-117/320) (1/320) tau := by
                convert childUR hs100120 hx100120 hy100120 using 1 <;> norm_num
              exact Batch0198.cell1588.sound htau (by
                simp only [Batch0198.cell1588, Batch0198.tau1588, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001203 (by positivity) using 1 <;> norm_num)
        · have hs100122 : InSquare (9/160) (-57/160) (1/160) tau := by
            convert childUL hs10012 hx10012 hy10012 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx100122 | hx100122
          · rcases le_total tau.im (-57/160 : ℝ) with hy100122 | hy100122
            · have hs1001220 : InSquare (17/320) (-23/64) (1/320) tau := by
                convert childLL hs100122 hx100122 hy100122 using 1 <;> norm_num
              exact Batch0199.cell1593.sound htau (by
                simp only [Batch0199.cell1593, Batch0199.tau1593, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001220 (by positivity) using 1 <;> norm_num)
            · have hs1001222 : InSquare (17/320) (-113/320) (1/320) tau := by
                convert childUL hs100122 hx100122 hy100122 using 1 <;> norm_num
              exact Batch0199.cell1595.sound htau (by
                simp only [Batch0199.cell1595, Batch0199.tau1595, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy100122 | hy100122
            · have hs1001221 : InSquare (19/320) (-23/64) (1/320) tau := by
                convert childLR hs100122 hx100122 hy100122 using 1 <;> norm_num
              exact Batch0199.cell1594.sound htau (by
                simp only [Batch0199.cell1594, Batch0199.tau1594, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001221 (by positivity) using 1 <;> norm_num)
            · have hs1001223 : InSquare (19/320) (-113/320) (1/320) tau := by
                convert childUR hs100122 hx100122 hy100122 using 1 <;> norm_num
              exact Batch0199.cell1596.sound htau (by
                simp only [Batch0199.cell1596, Batch0199.tau1596, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy10012 | hy10012
        · have hs100121 : InSquare (11/160) (-59/160) (1/160) tau := by
            convert childLR hs10012 hx10012 hy10012 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx100121 | hx100121
          · rcases le_total tau.im (-59/160 : ℝ) with hy100121 | hy100121
            · have hs1001210 : InSquare (21/320) (-119/320) (1/320) tau := by
                convert childLL hs100121 hx100121 hy100121 using 1 <;> norm_num
              exact Batch0198.cell1589.sound htau (by
                simp only [Batch0198.cell1589, Batch0198.tau1589, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001210 (by positivity) using 1 <;> norm_num)
            · have hs1001212 : InSquare (21/320) (-117/320) (1/320) tau := by
                convert childUL hs100121 hx100121 hy100121 using 1 <;> norm_num
              exact Batch0198.cell1591.sound htau (by
                simp only [Batch0198.cell1591, Batch0198.tau1591, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy100121 | hy100121
            · have hs1001211 : InSquare (23/320) (-119/320) (1/320) tau := by
                convert childLR hs100121 hx100121 hy100121 using 1 <;> norm_num
              exact Batch0198.cell1590.sound htau (by
                simp only [Batch0198.cell1590, Batch0198.tau1590, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001211 (by positivity) using 1 <;> norm_num)
            · have hs1001213 : InSquare (23/320) (-117/320) (1/320) tau := by
                convert childUR hs100121 hx100121 hy100121 using 1 <;> norm_num
              exact Batch0199.cell1592.sound htau (by
                simp only [Batch0199.cell1592, Batch0199.tau1592, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001213 (by positivity) using 1 <;> norm_num)
        · have hs100123 : InSquare (11/160) (-57/160) (1/160) tau := by
            convert childUR hs10012 hx10012 hy10012 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx100123 | hx100123
          · rcases le_total tau.im (-57/160 : ℝ) with hy100123 | hy100123
            · have hs1001230 : InSquare (21/320) (-23/64) (1/320) tau := by
                convert childLL hs100123 hx100123 hy100123 using 1 <;> norm_num
              exact Batch0199.cell1597.sound htau (by
                simp only [Batch0199.cell1597, Batch0199.tau1597, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001230 (by positivity) using 1 <;> norm_num)
            · have hs1001232 : InSquare (21/320) (-113/320) (1/320) tau := by
                convert childUL hs100123 hx100123 hy100123 using 1 <;> norm_num
              exact Batch0199.cell1599.sound htau (by
                simp only [Batch0199.cell1599, Batch0199.tau1599, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy100123 | hy100123
            · have hs1001231 : InSquare (23/320) (-23/64) (1/320) tau := by
                convert childLR hs100123 hx100123 hy100123 using 1 <;> norm_num
              exact Batch0199.cell1598.sound htau (by
                simp only [Batch0199.cell1598, Batch0199.tau1598, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001231 (by positivity) using 1 <;> norm_num)
            · have hs1001233 : InSquare (23/320) (-113/320) (1/320) tau := by
                convert childUR hs100123 hx100123 hy100123 using 1 <;> norm_num
              exact Batch0200.cell1600.sound htau (by
                simp only [Batch0200.cell1600, Batch0200.tau1600, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/8 : ℝ) with hy1001 | hy1001
    · have hs10011 : InSquare (7/80) (-31/80) (1/80) tau := by
        convert childLR hs hx1001 hy1001 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx10011 | hx10011
      · rcases le_total tau.im (-31/80 : ℝ) with hy10011 | hy10011
        · have hs100110 : InSquare (13/160) (-63/160) (1/160) tau := by
            convert childLL hs10011 hx10011 hy10011 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx100110 | hx100110
          · rcases le_total tau.im (-63/160 : ℝ) with hy100110 | hy100110
            · have hs1001100 : InSquare (5/64) (-127/320) (1/320) tau := by
                convert childLL hs100110 hx100110 hy100110 using 1 <;> norm_num
              exact (outside_1001100 htau hs1001100).elim
            · have hs1001102 : InSquare (5/64) (-25/64) (1/320) tau := by
                convert childUL hs100110 hx100110 hy100110 using 1 <;> norm_num
              rcases le_total tau.re (5/64 : ℝ) with hx1001102 | hx1001102
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001102 | hy1001102
                · have hs10011020 : InSquare (49/640) (-251/640) (1/640) tau := by
                    convert childLL hs1001102 hx1001102 hy1001102 using 1 <;> norm_num
                  exact Batch0375.cell3003.sound htau (by
                    simp only [Batch0375.cell3003, Batch0375.tau3003, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011020 (by positivity) using 1 <;> norm_num)
                · have hs10011022 : InSquare (49/640) (-249/640) (1/640) tau := by
                    convert childUL hs1001102 hx1001102 hy1001102 using 1 <;> norm_num
                  exact Batch0375.cell3005.sound htau (by
                    simp only [Batch0375.cell3005, Batch0375.tau3005, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001102 | hy1001102
                · have hs10011021 : InSquare (51/640) (-251/640) (1/640) tau := by
                    convert childLR hs1001102 hx1001102 hy1001102 using 1 <;> norm_num
                  exact Batch0375.cell3004.sound htau (by
                    simp only [Batch0375.cell3004, Batch0375.tau3004, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011021 (by positivity) using 1 <;> norm_num)
                · have hs10011023 : InSquare (51/640) (-249/640) (1/640) tau := by
                    convert childUR hs1001102 hx1001102 hy1001102 using 1 <;> norm_num
                  exact Batch0375.cell3006.sound htau (by
                    simp only [Batch0375.cell3006, Batch0375.tau3006, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy100110 | hy100110
            · have hs1001101 : InSquare (27/320) (-127/320) (1/320) tau := by
                convert childLR hs100110 hx100110 hy100110 using 1 <;> norm_num
              exact (outside_1001101 htau hs1001101).elim
            · have hs1001103 : InSquare (27/320) (-25/64) (1/320) tau := by
                convert childUR hs100110 hx100110 hy100110 using 1 <;> norm_num
              rcases le_total tau.re (27/320 : ℝ) with hx1001103 | hx1001103
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001103 | hy1001103
                · have hs10011030 : InSquare (53/640) (-251/640) (1/640) tau := by
                    convert childLL hs1001103 hx1001103 hy1001103 using 1 <;> norm_num
                  exact Batch0375.cell3007.sound htau (by
                    simp only [Batch0375.cell3007, Batch0375.tau3007, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011030 (by positivity) using 1 <;> norm_num)
                · have hs10011032 : InSquare (53/640) (-249/640) (1/640) tau := by
                    convert childUL hs1001103 hx1001103 hy1001103 using 1 <;> norm_num
                  exact Batch0376.cell3009.sound htau (by
                    simp only [Batch0376.cell3009, Batch0376.tau3009, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001103 | hy1001103
                · have hs10011031 : InSquare (11/128) (-251/640) (1/640) tau := by
                    convert childLR hs1001103 hx1001103 hy1001103 using 1 <;> norm_num
                  exact Batch0376.cell3008.sound htau (by
                    simp only [Batch0376.cell3008, Batch0376.tau3008, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011031 (by positivity) using 1 <;> norm_num)
                · have hs10011033 : InSquare (11/128) (-249/640) (1/640) tau := by
                    convert childUR hs1001103 hx1001103 hy1001103 using 1 <;> norm_num
                  exact Batch0376.cell3010.sound htau (by
                    simp only [Batch0376.cell3010, Batch0376.tau3010, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011033 (by positivity) using 1 <;> norm_num)
        · have hs100112 : InSquare (13/160) (-61/160) (1/160) tau := by
            convert childUL hs10011 hx10011 hy10011 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx100112 | hx100112
          · rcases le_total tau.im (-61/160 : ℝ) with hy100112 | hy100112
            · have hs1001120 : InSquare (5/64) (-123/320) (1/320) tau := by
                convert childLL hs100112 hx100112 hy100112 using 1 <;> norm_num
              rcases le_total tau.re (5/64 : ℝ) with hx1001120 | hx1001120
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001120 | hy1001120
                · have hs10011200 : InSquare (49/640) (-247/640) (1/640) tau := by
                    convert childLL hs1001120 hx1001120 hy1001120 using 1 <;> norm_num
                  exact Batch0376.cell3015.sound htau (by
                    simp only [Batch0376.cell3015, Batch0376.tau3015, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011200 (by positivity) using 1 <;> norm_num)
                · have hs10011202 : InSquare (49/640) (-49/128) (1/640) tau := by
                    convert childUL hs1001120 hx1001120 hy1001120 using 1 <;> norm_num
                  exact Batch0377.cell3017.sound htau (by
                    simp only [Batch0377.cell3017, Batch0377.tau3017, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001120 | hy1001120
                · have hs10011201 : InSquare (51/640) (-247/640) (1/640) tau := by
                    convert childLR hs1001120 hx1001120 hy1001120 using 1 <;> norm_num
                  exact Batch0377.cell3016.sound htau (by
                    simp only [Batch0377.cell3016, Batch0377.tau3016, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011201 (by positivity) using 1 <;> norm_num)
                · have hs10011203 : InSquare (51/640) (-49/128) (1/640) tau := by
                    convert childUR hs1001120 hx1001120 hy1001120 using 1 <;> norm_num
                  exact Batch0377.cell3018.sound htau (by
                    simp only [Batch0377.cell3018, Batch0377.tau3018, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011203 (by positivity) using 1 <;> norm_num)
            · have hs1001122 : InSquare (5/64) (-121/320) (1/320) tau := by
                convert childUL hs100112 hx100112 hy100112 using 1 <;> norm_num
              rcases le_total tau.re (5/64 : ℝ) with hx1001122 | hx1001122
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001122 | hy1001122
                · have hs10011220 : InSquare (49/640) (-243/640) (1/640) tau := by
                    convert childLL hs1001122 hx1001122 hy1001122 using 1 <;> norm_num
                  exact Batch0377.cell3023.sound htau (by
                    simp only [Batch0377.cell3023, Batch0377.tau3023, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011220 (by positivity) using 1 <;> norm_num)
                · have hs10011222 : InSquare (49/640) (-241/640) (1/640) tau := by
                    convert childUL hs1001122 hx1001122 hy1001122 using 1 <;> norm_num
                  exact Batch0378.cell3025.sound htau (by
                    simp only [Batch0378.cell3025, Batch0378.tau3025, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001122 | hy1001122
                · have hs10011221 : InSquare (51/640) (-243/640) (1/640) tau := by
                    convert childLR hs1001122 hx1001122 hy1001122 using 1 <;> norm_num
                  exact Batch0378.cell3024.sound htau (by
                    simp only [Batch0378.cell3024, Batch0378.tau3024, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011221 (by positivity) using 1 <;> norm_num)
                · have hs10011223 : InSquare (51/640) (-241/640) (1/640) tau := by
                    convert childUR hs1001122 hx1001122 hy1001122 using 1 <;> norm_num
                  exact Batch0378.cell3026.sound htau (by
                    simp only [Batch0378.cell3026, Batch0378.tau3026, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy100112 | hy100112
            · have hs1001121 : InSquare (27/320) (-123/320) (1/320) tau := by
                convert childLR hs100112 hx100112 hy100112 using 1 <;> norm_num
              rcases le_total tau.re (27/320 : ℝ) with hx1001121 | hx1001121
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001121 | hy1001121
                · have hs10011210 : InSquare (53/640) (-247/640) (1/640) tau := by
                    convert childLL hs1001121 hx1001121 hy1001121 using 1 <;> norm_num
                  exact Batch0377.cell3019.sound htau (by
                    simp only [Batch0377.cell3019, Batch0377.tau3019, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011210 (by positivity) using 1 <;> norm_num)
                · have hs10011212 : InSquare (53/640) (-49/128) (1/640) tau := by
                    convert childUL hs1001121 hx1001121 hy1001121 using 1 <;> norm_num
                  exact Batch0377.cell3021.sound htau (by
                    simp only [Batch0377.cell3021, Batch0377.tau3021, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001121 | hy1001121
                · have hs10011211 : InSquare (11/128) (-247/640) (1/640) tau := by
                    convert childLR hs1001121 hx1001121 hy1001121 using 1 <;> norm_num
                  exact Batch0377.cell3020.sound htau (by
                    simp only [Batch0377.cell3020, Batch0377.tau3020, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011211 (by positivity) using 1 <;> norm_num)
                · have hs10011213 : InSquare (11/128) (-49/128) (1/640) tau := by
                    convert childUR hs1001121 hx1001121 hy1001121 using 1 <;> norm_num
                  exact Batch0377.cell3022.sound htau (by
                    simp only [Batch0377.cell3022, Batch0377.tau3022, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011213 (by positivity) using 1 <;> norm_num)
            · have hs1001123 : InSquare (27/320) (-121/320) (1/320) tau := by
                convert childUR hs100112 hx100112 hy100112 using 1 <;> norm_num
              rcases le_total tau.re (27/320 : ℝ) with hx1001123 | hx1001123
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001123 | hy1001123
                · have hs10011230 : InSquare (53/640) (-243/640) (1/640) tau := by
                    convert childLL hs1001123 hx1001123 hy1001123 using 1 <;> norm_num
                  exact Batch0378.cell3027.sound htau (by
                    simp only [Batch0378.cell3027, Batch0378.tau3027, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011230 (by positivity) using 1 <;> norm_num)
                · have hs10011232 : InSquare (53/640) (-241/640) (1/640) tau := by
                    convert childUL hs1001123 hx1001123 hy1001123 using 1 <;> norm_num
                  exact Batch0378.cell3029.sound htau (by
                    simp only [Batch0378.cell3029, Batch0378.tau3029, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001123 | hy1001123
                · have hs10011231 : InSquare (11/128) (-243/640) (1/640) tau := by
                    convert childLR hs1001123 hx1001123 hy1001123 using 1 <;> norm_num
                  exact Batch0378.cell3028.sound htau (by
                    simp only [Batch0378.cell3028, Batch0378.tau3028, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011231 (by positivity) using 1 <;> norm_num)
                · have hs10011233 : InSquare (11/128) (-241/640) (1/640) tau := by
                    convert childUR hs1001123 hx1001123 hy1001123 using 1 <;> norm_num
                  exact Batch0378.cell3030.sound htau (by
                    simp only [Batch0378.cell3030, Batch0378.tau3030, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy10011 | hy10011
        · have hs100111 : InSquare (3/32) (-63/160) (1/160) tau := by
            convert childLR hs10011 hx10011 hy10011 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx100111 | hx100111
          · rcases le_total tau.im (-63/160 : ℝ) with hy100111 | hy100111
            · have hs1001110 : InSquare (29/320) (-127/320) (1/320) tau := by
                convert childLL hs100111 hx100111 hy100111 using 1 <;> norm_num
              exact (outside_1001110 htau hs1001110).elim
            · have hs1001112 : InSquare (29/320) (-25/64) (1/320) tau := by
                convert childUL hs100111 hx100111 hy100111 using 1 <;> norm_num
              rcases le_total tau.re (29/320 : ℝ) with hx1001112 | hx1001112
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001112 | hy1001112
                · have hs10011120 : InSquare (57/640) (-251/640) (1/640) tau := by
                    convert childLL hs1001112 hx1001112 hy1001112 using 1 <;> norm_num
                  exact (outside_10011120 htau hs10011120).elim
                · have hs10011122 : InSquare (57/640) (-249/640) (1/640) tau := by
                    convert childUL hs1001112 hx1001112 hy1001112 using 1 <;> norm_num
                  exact Batch0376.cell3011.sound htau (by
                    simp only [Batch0376.cell3011, Batch0376.tau3011, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001112 | hy1001112
                · have hs10011121 : InSquare (59/640) (-251/640) (1/640) tau := by
                    convert childLR hs1001112 hx1001112 hy1001112 using 1 <;> norm_num
                  exact (outside_10011121 htau hs10011121).elim
                · have hs10011123 : InSquare (59/640) (-249/640) (1/640) tau := by
                    convert childUR hs1001112 hx1001112 hy1001112 using 1 <;> norm_num
                  exact Batch0376.cell3012.sound htau (by
                    simp only [Batch0376.cell3012, Batch0376.tau3012, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy100111 | hy100111
            · have hs1001111 : InSquare (31/320) (-127/320) (1/320) tau := by
                convert childLR hs100111 hx100111 hy100111 using 1 <;> norm_num
              exact (outside_1001111 htau hs1001111).elim
            · have hs1001113 : InSquare (31/320) (-25/64) (1/320) tau := by
                convert childUR hs100111 hx100111 hy100111 using 1 <;> norm_num
              rcases le_total tau.re (31/320 : ℝ) with hx1001113 | hx1001113
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001113 | hy1001113
                · have hs10011130 : InSquare (61/640) (-251/640) (1/640) tau := by
                    convert childLL hs1001113 hx1001113 hy1001113 using 1 <;> norm_num
                  exact (outside_10011130 htau hs10011130).elim
                · have hs10011132 : InSquare (61/640) (-249/640) (1/640) tau := by
                    convert childUL hs1001113 hx1001113 hy1001113 using 1 <;> norm_num
                  exact Batch0376.cell3013.sound htau (by
                    simp only [Batch0376.cell3013, Batch0376.tau3013, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001113 | hy1001113
                · have hs10011131 : InSquare (63/640) (-251/640) (1/640) tau := by
                    convert childLR hs1001113 hx1001113 hy1001113 using 1 <;> norm_num
                  exact (outside_10011131 htau hs10011131).elim
                · have hs10011133 : InSquare (63/640) (-249/640) (1/640) tau := by
                    convert childUR hs1001113 hx1001113 hy1001113 using 1 <;> norm_num
                  exact Batch0376.cell3014.sound htau (by
                    simp only [Batch0376.cell3014, Batch0376.tau3014, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011133 (by positivity) using 1 <;> norm_num)
        · have hs100113 : InSquare (3/32) (-61/160) (1/160) tau := by
            convert childUR hs10011 hx10011 hy10011 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx100113 | hx100113
          · rcases le_total tau.im (-61/160 : ℝ) with hy100113 | hy100113
            · have hs1001130 : InSquare (29/320) (-123/320) (1/320) tau := by
                convert childLL hs100113 hx100113 hy100113 using 1 <;> norm_num
              rcases le_total tau.re (29/320 : ℝ) with hx1001130 | hx1001130
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001130 | hy1001130
                · have hs10011300 : InSquare (57/640) (-247/640) (1/640) tau := by
                    convert childLL hs1001130 hx1001130 hy1001130 using 1 <;> norm_num
                  exact Batch0378.cell3031.sound htau (by
                    simp only [Batch0378.cell3031, Batch0378.tau3031, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011300 (by positivity) using 1 <;> norm_num)
                · have hs10011302 : InSquare (57/640) (-49/128) (1/640) tau := by
                    convert childUL hs1001130 hx1001130 hy1001130 using 1 <;> norm_num
                  exact Batch0379.cell3033.sound htau (by
                    simp only [Batch0379.cell3033, Batch0379.tau3033, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001130 | hy1001130
                · have hs10011301 : InSquare (59/640) (-247/640) (1/640) tau := by
                    convert childLR hs1001130 hx1001130 hy1001130 using 1 <;> norm_num
                  exact Batch0379.cell3032.sound htau (by
                    simp only [Batch0379.cell3032, Batch0379.tau3032, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011301 (by positivity) using 1 <;> norm_num)
                · have hs10011303 : InSquare (59/640) (-49/128) (1/640) tau := by
                    convert childUR hs1001130 hx1001130 hy1001130 using 1 <;> norm_num
                  exact Batch0379.cell3034.sound htau (by
                    simp only [Batch0379.cell3034, Batch0379.tau3034, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011303 (by positivity) using 1 <;> norm_num)
            · have hs1001132 : InSquare (29/320) (-121/320) (1/320) tau := by
                convert childUL hs100113 hx100113 hy100113 using 1 <;> norm_num
              rcases le_total tau.re (29/320 : ℝ) with hx1001132 | hx1001132
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001132 | hy1001132
                · have hs10011320 : InSquare (57/640) (-243/640) (1/640) tau := by
                    convert childLL hs1001132 hx1001132 hy1001132 using 1 <;> norm_num
                  exact Batch0379.cell3039.sound htau (by
                    simp only [Batch0379.cell3039, Batch0379.tau3039, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011320 (by positivity) using 1 <;> norm_num)
                · have hs10011322 : InSquare (57/640) (-241/640) (1/640) tau := by
                    convert childUL hs1001132 hx1001132 hy1001132 using 1 <;> norm_num
                  exact Batch0380.cell3041.sound htau (by
                    simp only [Batch0380.cell3041, Batch0380.tau3041, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001132 | hy1001132
                · have hs10011321 : InSquare (59/640) (-243/640) (1/640) tau := by
                    convert childLR hs1001132 hx1001132 hy1001132 using 1 <;> norm_num
                  exact Batch0380.cell3040.sound htau (by
                    simp only [Batch0380.cell3040, Batch0380.tau3040, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011321 (by positivity) using 1 <;> norm_num)
                · have hs10011323 : InSquare (59/640) (-241/640) (1/640) tau := by
                    convert childUR hs1001132 hx1001132 hy1001132 using 1 <;> norm_num
                  exact Batch0380.cell3042.sound htau (by
                    simp only [Batch0380.cell3042, Batch0380.tau3042, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy100113 | hy100113
            · have hs1001131 : InSquare (31/320) (-123/320) (1/320) tau := by
                convert childLR hs100113 hx100113 hy100113 using 1 <;> norm_num
              rcases le_total tau.re (31/320 : ℝ) with hx1001131 | hx1001131
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001131 | hy1001131
                · have hs10011310 : InSquare (61/640) (-247/640) (1/640) tau := by
                    convert childLL hs1001131 hx1001131 hy1001131 using 1 <;> norm_num
                  exact Batch0379.cell3035.sound htau (by
                    simp only [Batch0379.cell3035, Batch0379.tau3035, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011310 (by positivity) using 1 <;> norm_num)
                · have hs10011312 : InSquare (61/640) (-49/128) (1/640) tau := by
                    convert childUL hs1001131 hx1001131 hy1001131 using 1 <;> norm_num
                  exact Batch0379.cell3037.sound htau (by
                    simp only [Batch0379.cell3037, Batch0379.tau3037, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001131 | hy1001131
                · have hs10011311 : InSquare (63/640) (-247/640) (1/640) tau := by
                    convert childLR hs1001131 hx1001131 hy1001131 using 1 <;> norm_num
                  exact Batch0379.cell3036.sound htau (by
                    simp only [Batch0379.cell3036, Batch0379.tau3036, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011311 (by positivity) using 1 <;> norm_num)
                · have hs10011313 : InSquare (63/640) (-49/128) (1/640) tau := by
                    convert childUR hs1001131 hx1001131 hy1001131 using 1 <;> norm_num
                  exact Batch0379.cell3038.sound htau (by
                    simp only [Batch0379.cell3038, Batch0379.tau3038, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011313 (by positivity) using 1 <;> norm_num)
            · have hs1001133 : InSquare (31/320) (-121/320) (1/320) tau := by
                convert childUR hs100113 hx100113 hy100113 using 1 <;> norm_num
              rcases le_total tau.re (31/320 : ℝ) with hx1001133 | hx1001133
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001133 | hy1001133
                · have hs10011330 : InSquare (61/640) (-243/640) (1/640) tau := by
                    convert childLL hs1001133 hx1001133 hy1001133 using 1 <;> norm_num
                  exact Batch0380.cell3043.sound htau (by
                    simp only [Batch0380.cell3043, Batch0380.tau3043, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011330 (by positivity) using 1 <;> norm_num)
                · have hs10011332 : InSquare (61/640) (-241/640) (1/640) tau := by
                    convert childUL hs1001133 hx1001133 hy1001133 using 1 <;> norm_num
                  exact Batch0380.cell3045.sound htau (by
                    simp only [Batch0380.cell3045, Batch0380.tau3045, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001133 | hy1001133
                · have hs10011331 : InSquare (63/640) (-243/640) (1/640) tau := by
                    convert childLR hs1001133 hx1001133 hy1001133 using 1 <;> norm_num
                  exact Batch0380.cell3044.sound htau (by
                    simp only [Batch0380.cell3044, Batch0380.tau3044, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011331 (by positivity) using 1 <;> norm_num)
                · have hs10011333 : InSquare (63/640) (-241/640) (1/640) tau := by
                    convert childUR hs1001133 hx1001133 hy1001133 using 1 <;> norm_num
                  exact Batch0380.cell3046.sound htau (by
                    simp only [Batch0380.cell3046, Batch0380.tau3046, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011333 (by positivity) using 1 <;> norm_num)
    · have hs10013 : InSquare (7/80) (-29/80) (1/80) tau := by
        convert childUR hs hx1001 hy1001 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx10013 | hx10013
      · rcases le_total tau.im (-29/80 : ℝ) with hy10013 | hy10013
        · have hs100130 : InSquare (13/160) (-59/160) (1/160) tau := by
            convert childLL hs10013 hx10013 hy10013 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx100130 | hx100130
          · rcases le_total tau.im (-59/160 : ℝ) with hy100130 | hy100130
            · have hs1001300 : InSquare (5/64) (-119/320) (1/320) tau := by
                convert childLL hs100130 hx100130 hy100130 using 1 <;> norm_num
              exact Batch0200.cell1601.sound htau (by
                simp only [Batch0200.cell1601, Batch0200.tau1601, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001300 (by positivity) using 1 <;> norm_num)
            · have hs1001302 : InSquare (5/64) (-117/320) (1/320) tau := by
                convert childUL hs100130 hx100130 hy100130 using 1 <;> norm_num
              exact Batch0200.cell1603.sound htau (by
                simp only [Batch0200.cell1603, Batch0200.tau1603, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy100130 | hy100130
            · have hs1001301 : InSquare (27/320) (-119/320) (1/320) tau := by
                convert childLR hs100130 hx100130 hy100130 using 1 <;> norm_num
              exact Batch0200.cell1602.sound htau (by
                simp only [Batch0200.cell1602, Batch0200.tau1602, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001301 (by positivity) using 1 <;> norm_num)
            · have hs1001303 : InSquare (27/320) (-117/320) (1/320) tau := by
                convert childUR hs100130 hx100130 hy100130 using 1 <;> norm_num
              exact Batch0200.cell1604.sound htau (by
                simp only [Batch0200.cell1604, Batch0200.tau1604, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001303 (by positivity) using 1 <;> norm_num)
        · have hs100132 : InSquare (13/160) (-57/160) (1/160) tau := by
            convert childUL hs10013 hx10013 hy10013 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx100132 | hx100132
          · rcases le_total tau.im (-57/160 : ℝ) with hy100132 | hy100132
            · have hs1001320 : InSquare (5/64) (-23/64) (1/320) tau := by
                convert childLL hs100132 hx100132 hy100132 using 1 <;> norm_num
              exact Batch0201.cell1609.sound htau (by
                simp only [Batch0201.cell1609, Batch0201.tau1609, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001320 (by positivity) using 1 <;> norm_num)
            · have hs1001322 : InSquare (5/64) (-113/320) (1/320) tau := by
                convert childUL hs100132 hx100132 hy100132 using 1 <;> norm_num
              exact Batch0201.cell1611.sound htau (by
                simp only [Batch0201.cell1611, Batch0201.tau1611, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy100132 | hy100132
            · have hs1001321 : InSquare (27/320) (-23/64) (1/320) tau := by
                convert childLR hs100132 hx100132 hy100132 using 1 <;> norm_num
              exact Batch0201.cell1610.sound htau (by
                simp only [Batch0201.cell1610, Batch0201.tau1610, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001321 (by positivity) using 1 <;> norm_num)
            · have hs1001323 : InSquare (27/320) (-113/320) (1/320) tau := by
                convert childUR hs100132 hx100132 hy100132 using 1 <;> norm_num
              exact Batch0201.cell1612.sound htau (by
                simp only [Batch0201.cell1612, Batch0201.tau1612, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy10013 | hy10013
        · have hs100131 : InSquare (3/32) (-59/160) (1/160) tau := by
            convert childLR hs10013 hx10013 hy10013 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx100131 | hx100131
          · rcases le_total tau.im (-59/160 : ℝ) with hy100131 | hy100131
            · have hs1001310 : InSquare (29/320) (-119/320) (1/320) tau := by
                convert childLL hs100131 hx100131 hy100131 using 1 <;> norm_num
              exact Batch0200.cell1605.sound htau (by
                simp only [Batch0200.cell1605, Batch0200.tau1605, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001310 (by positivity) using 1 <;> norm_num)
            · have hs1001312 : InSquare (29/320) (-117/320) (1/320) tau := by
                convert childUL hs100131 hx100131 hy100131 using 1 <;> norm_num
              exact Batch0200.cell1607.sound htau (by
                simp only [Batch0200.cell1607, Batch0200.tau1607, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy100131 | hy100131
            · have hs1001311 : InSquare (31/320) (-119/320) (1/320) tau := by
                convert childLR hs100131 hx100131 hy100131 using 1 <;> norm_num
              exact Batch0200.cell1606.sound htau (by
                simp only [Batch0200.cell1606, Batch0200.tau1606, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001311 (by positivity) using 1 <;> norm_num)
            · have hs1001313 : InSquare (31/320) (-117/320) (1/320) tau := by
                convert childUR hs100131 hx100131 hy100131 using 1 <;> norm_num
              exact Batch0201.cell1608.sound htau (by
                simp only [Batch0201.cell1608, Batch0201.tau1608, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001313 (by positivity) using 1 <;> norm_num)
        · have hs100133 : InSquare (3/32) (-57/160) (1/160) tau := by
            convert childUR hs10013 hx10013 hy10013 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx100133 | hx100133
          · rcases le_total tau.im (-57/160 : ℝ) with hy100133 | hy100133
            · have hs1001330 : InSquare (29/320) (-23/64) (1/320) tau := by
                convert childLL hs100133 hx100133 hy100133 using 1 <;> norm_num
              exact Batch0201.cell1613.sound htau (by
                simp only [Batch0201.cell1613, Batch0201.tau1613, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001330 (by positivity) using 1 <;> norm_num)
            · have hs1001332 : InSquare (29/320) (-113/320) (1/320) tau := by
                convert childUL hs100133 hx100133 hy100133 using 1 <;> norm_num
              exact Batch0201.cell1615.sound htau (by
                simp only [Batch0201.cell1615, Batch0201.tau1615, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy100133 | hy100133
            · have hs1001331 : InSquare (31/320) (-23/64) (1/320) tau := by
                convert childLR hs100133 hx100133 hy100133 using 1 <;> norm_num
              exact Batch0201.cell1614.sound htau (by
                simp only [Batch0201.cell1614, Batch0201.tau1614, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001331 (by positivity) using 1 <;> norm_num)
            · have hs1001333 : InSquare (31/320) (-113/320) (1/320) tau := by
                convert childUR hs100133 hx100133 hy100133 using 1 <;> norm_num
              exact Batch0202.cell1616.sound htau (by
                simp only [Batch0202.cell1616, Batch0202.tau1616, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1001

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1002 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1002

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/40 : ℝ) with hx1002 | hx1002
  · rcases le_total tau.im (-13/40 : ℝ) with hy1002 | hy1002
    · have hs10020 : InSquare (1/80) (-27/80) (1/80) tau := by
        convert childLL hs hx1002 hy1002 using 1 <;> norm_num
      rcases le_total tau.re (1/80 : ℝ) with hx10020 | hx10020
      · rcases le_total tau.im (-27/80 : ℝ) with hy10020 | hy10020
        · have hs100200 : InSquare (1/160) (-11/32) (1/160) tau := by
            convert childLL hs10020 hx10020 hy10020 using 1 <;> norm_num
          exact Batch0069.cell0559.sound htau (by
            simp only [Batch0069.cell0559, Batch0069.tau0559, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100200 (by positivity) using 1 <;> norm_num)
        · have hs100202 : InSquare (1/160) (-53/160) (1/160) tau := by
            convert childUL hs10020 hx10020 hy10020 using 1 <;> norm_num
          exact Batch0070.cell0561.sound htau (by
            simp only [Batch0070.cell0561, Batch0070.tau0561, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10020 | hy10020
        · have hs100201 : InSquare (3/160) (-11/32) (1/160) tau := by
            convert childLR hs10020 hx10020 hy10020 using 1 <;> norm_num
          exact Batch0070.cell0560.sound htau (by
            simp only [Batch0070.cell0560, Batch0070.tau0560, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100201 (by positivity) using 1 <;> norm_num)
        · have hs100203 : InSquare (3/160) (-53/160) (1/160) tau := by
            convert childUR hs10020 hx10020 hy10020 using 1 <;> norm_num
          exact Batch0070.cell0562.sound htau (by
            simp only [Batch0070.cell0562, Batch0070.tau0562, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100203 (by positivity) using 1 <;> norm_num)
    · have hs10022 : InSquare (1/80) (-5/16) (1/80) tau := by
        convert childUL hs hx1002 hy1002 using 1 <;> norm_num
      rcases le_total tau.re (1/80 : ℝ) with hx10022 | hx10022
      · rcases le_total tau.im (-5/16 : ℝ) with hy10022 | hy10022
        · have hs100220 : InSquare (1/160) (-51/160) (1/160) tau := by
            convert childLL hs10022 hx10022 hy10022 using 1 <;> norm_num
          exact Batch0070.cell0567.sound htau (by
            simp only [Batch0070.cell0567, Batch0070.tau0567, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100220 (by positivity) using 1 <;> norm_num)
        · have hs100222 : InSquare (1/160) (-49/160) (1/160) tau := by
            convert childUL hs10022 hx10022 hy10022 using 1 <;> norm_num
          exact Batch0071.cell0569.sound htau (by
            simp only [Batch0071.cell0569, Batch0071.tau0569, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10022 | hy10022
        · have hs100221 : InSquare (3/160) (-51/160) (1/160) tau := by
            convert childLR hs10022 hx10022 hy10022 using 1 <;> norm_num
          exact Batch0071.cell0568.sound htau (by
            simp only [Batch0071.cell0568, Batch0071.tau0568, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100221 (by positivity) using 1 <;> norm_num)
        · have hs100223 : InSquare (3/160) (-49/160) (1/160) tau := by
            convert childUR hs10022 hx10022 hy10022 using 1 <;> norm_num
          exact Batch0071.cell0570.sound htau (by
            simp only [Batch0071.cell0570, Batch0071.tau0570, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy1002 | hy1002
    · have hs10021 : InSquare (3/80) (-27/80) (1/80) tau := by
        convert childLR hs hx1002 hy1002 using 1 <;> norm_num
      rcases le_total tau.re (3/80 : ℝ) with hx10021 | hx10021
      · rcases le_total tau.im (-27/80 : ℝ) with hy10021 | hy10021
        · have hs100210 : InSquare (1/32) (-11/32) (1/160) tau := by
            convert childLL hs10021 hx10021 hy10021 using 1 <;> norm_num
          exact Batch0070.cell0563.sound htau (by
            simp only [Batch0070.cell0563, Batch0070.tau0563, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100210 (by positivity) using 1 <;> norm_num)
        · have hs100212 : InSquare (1/32) (-53/160) (1/160) tau := by
            convert childUL hs10021 hx10021 hy10021 using 1 <;> norm_num
          exact Batch0070.cell0565.sound htau (by
            simp only [Batch0070.cell0565, Batch0070.tau0565, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10021 | hy10021
        · have hs100211 : InSquare (7/160) (-11/32) (1/160) tau := by
            convert childLR hs10021 hx10021 hy10021 using 1 <;> norm_num
          exact Batch0070.cell0564.sound htau (by
            simp only [Batch0070.cell0564, Batch0070.tau0564, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100211 (by positivity) using 1 <;> norm_num)
        · have hs100213 : InSquare (7/160) (-53/160) (1/160) tau := by
            convert childUR hs10021 hx10021 hy10021 using 1 <;> norm_num
          exact Batch0070.cell0566.sound htau (by
            simp only [Batch0070.cell0566, Batch0070.tau0566, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100213 (by positivity) using 1 <;> norm_num)
    · have hs10023 : InSquare (3/80) (-5/16) (1/80) tau := by
        convert childUR hs hx1002 hy1002 using 1 <;> norm_num
      rcases le_total tau.re (3/80 : ℝ) with hx10023 | hx10023
      · rcases le_total tau.im (-5/16 : ℝ) with hy10023 | hy10023
        · have hs100230 : InSquare (1/32) (-51/160) (1/160) tau := by
            convert childLL hs10023 hx10023 hy10023 using 1 <;> norm_num
          exact Batch0071.cell0571.sound htau (by
            simp only [Batch0071.cell0571, Batch0071.tau0571, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100230 (by positivity) using 1 <;> norm_num)
        · have hs100232 : InSquare (1/32) (-49/160) (1/160) tau := by
            convert childUL hs10023 hx10023 hy10023 using 1 <;> norm_num
          exact Batch0071.cell0573.sound htau (by
            simp only [Batch0071.cell0573, Batch0071.tau0573, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10023 | hy10023
        · have hs100231 : InSquare (7/160) (-51/160) (1/160) tau := by
            convert childLR hs10023 hx10023 hy10023 using 1 <;> norm_num
          exact Batch0071.cell0572.sound htau (by
            simp only [Batch0071.cell0572, Batch0071.tau0572, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100231 (by positivity) using 1 <;> norm_num)
        · have hs100233 : InSquare (7/160) (-49/160) (1/160) tau := by
            convert childUR hs10023 hx10023 hy10023 using 1 <;> norm_num
          exact Batch0071.cell0574.sound htau (by
            simp only [Batch0071.cell0574, Batch0071.tau0574, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1002

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1003 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1003

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx1003 | hx1003
  · rcases le_total tau.im (-13/40 : ℝ) with hy1003 | hy1003
    · have hs10030 : InSquare (1/16) (-27/80) (1/80) tau := by
        convert childLL hs hx1003 hy1003 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx10030 | hx10030
      · rcases le_total tau.im (-27/80 : ℝ) with hy10030 | hy10030
        · have hs100300 : InSquare (9/160) (-11/32) (1/160) tau := by
            convert childLL hs10030 hx10030 hy10030 using 1 <;> norm_num
          exact Batch0071.cell0575.sound htau (by
            simp only [Batch0071.cell0575, Batch0071.tau0575, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100300 (by positivity) using 1 <;> norm_num)
        · have hs100302 : InSquare (9/160) (-53/160) (1/160) tau := by
            convert childUL hs10030 hx10030 hy10030 using 1 <;> norm_num
          exact Batch0072.cell0576.sound htau (by
            simp only [Batch0072.cell0576, Batch0072.tau0576, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10030 | hy10030
        · have hs100301 : InSquare (11/160) (-11/32) (1/160) tau := by
            convert childLR hs10030 hx10030 hy10030 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx100301 | hx100301
          · rcases le_total tau.im (-11/32 : ℝ) with hy100301 | hy100301
            · have hs1003010 : InSquare (21/320) (-111/320) (1/320) tau := by
                convert childLL hs100301 hx100301 hy100301 using 1 <;> norm_num
              exact Batch0202.cell1617.sound htau (by
                simp only [Batch0202.cell1617, Batch0202.tau1617, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003010 (by positivity) using 1 <;> norm_num)
            · have hs1003012 : InSquare (21/320) (-109/320) (1/320) tau := by
                convert childUL hs100301 hx100301 hy100301 using 1 <;> norm_num
              exact Batch0202.cell1619.sound htau (by
                simp only [Batch0202.cell1619, Batch0202.tau1619, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy100301 | hy100301
            · have hs1003011 : InSquare (23/320) (-111/320) (1/320) tau := by
                convert childLR hs100301 hx100301 hy100301 using 1 <;> norm_num
              exact Batch0202.cell1618.sound htau (by
                simp only [Batch0202.cell1618, Batch0202.tau1618, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003011 (by positivity) using 1 <;> norm_num)
            · have hs1003013 : InSquare (23/320) (-109/320) (1/320) tau := by
                convert childUR hs100301 hx100301 hy100301 using 1 <;> norm_num
              exact Batch0202.cell1620.sound htau (by
                simp only [Batch0202.cell1620, Batch0202.tau1620, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003013 (by positivity) using 1 <;> norm_num)
        · have hs100303 : InSquare (11/160) (-53/160) (1/160) tau := by
            convert childUR hs10030 hx10030 hy10030 using 1 <;> norm_num
          exact Batch0072.cell0577.sound htau (by
            simp only [Batch0072.cell0577, Batch0072.tau0577, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100303 (by positivity) using 1 <;> norm_num)
    · have hs10032 : InSquare (1/16) (-5/16) (1/80) tau := by
        convert childUL hs hx1003 hy1003 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx10032 | hx10032
      · rcases le_total tau.im (-5/16 : ℝ) with hy10032 | hy10032
        · have hs100320 : InSquare (9/160) (-51/160) (1/160) tau := by
            convert childLL hs10032 hx10032 hy10032 using 1 <;> norm_num
          exact Batch0072.cell0580.sound htau (by
            simp only [Batch0072.cell0580, Batch0072.tau0580, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100320 (by positivity) using 1 <;> norm_num)
        · have hs100322 : InSquare (9/160) (-49/160) (1/160) tau := by
            convert childUL hs10032 hx10032 hy10032 using 1 <;> norm_num
          exact Batch0072.cell0582.sound htau (by
            simp only [Batch0072.cell0582, Batch0072.tau0582, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10032 | hy10032
        · have hs100321 : InSquare (11/160) (-51/160) (1/160) tau := by
            convert childLR hs10032 hx10032 hy10032 using 1 <;> norm_num
          exact Batch0072.cell0581.sound htau (by
            simp only [Batch0072.cell0581, Batch0072.tau0581, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100321 (by positivity) using 1 <;> norm_num)
        · have hs100323 : InSquare (11/160) (-49/160) (1/160) tau := by
            convert childUR hs10032 hx10032 hy10032 using 1 <;> norm_num
          exact Batch0072.cell0583.sound htau (by
            simp only [Batch0072.cell0583, Batch0072.tau0583, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy1003 | hy1003
    · have hs10031 : InSquare (7/80) (-27/80) (1/80) tau := by
        convert childLR hs hx1003 hy1003 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx10031 | hx10031
      · rcases le_total tau.im (-27/80 : ℝ) with hy10031 | hy10031
        · have hs100310 : InSquare (13/160) (-11/32) (1/160) tau := by
            convert childLL hs10031 hx10031 hy10031 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx100310 | hx100310
          · rcases le_total tau.im (-11/32 : ℝ) with hy100310 | hy100310
            · have hs1003100 : InSquare (5/64) (-111/320) (1/320) tau := by
                convert childLL hs100310 hx100310 hy100310 using 1 <;> norm_num
              exact Batch0202.cell1621.sound htau (by
                simp only [Batch0202.cell1621, Batch0202.tau1621, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003100 (by positivity) using 1 <;> norm_num)
            · have hs1003102 : InSquare (5/64) (-109/320) (1/320) tau := by
                convert childUL hs100310 hx100310 hy100310 using 1 <;> norm_num
              exact Batch0202.cell1623.sound htau (by
                simp only [Batch0202.cell1623, Batch0202.tau1623, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy100310 | hy100310
            · have hs1003101 : InSquare (27/320) (-111/320) (1/320) tau := by
                convert childLR hs100310 hx100310 hy100310 using 1 <;> norm_num
              exact Batch0202.cell1622.sound htau (by
                simp only [Batch0202.cell1622, Batch0202.tau1622, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003101 (by positivity) using 1 <;> norm_num)
            · have hs1003103 : InSquare (27/320) (-109/320) (1/320) tau := by
                convert childUR hs100310 hx100310 hy100310 using 1 <;> norm_num
              exact Batch0203.cell1624.sound htau (by
                simp only [Batch0203.cell1624, Batch0203.tau1624, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003103 (by positivity) using 1 <;> norm_num)
        · have hs100312 : InSquare (13/160) (-53/160) (1/160) tau := by
            convert childUL hs10031 hx10031 hy10031 using 1 <;> norm_num
          exact Batch0072.cell0578.sound htau (by
            simp only [Batch0072.cell0578, Batch0072.tau0578, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10031 | hy10031
        · have hs100311 : InSquare (3/32) (-11/32) (1/160) tau := by
            convert childLR hs10031 hx10031 hy10031 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx100311 | hx100311
          · rcases le_total tau.im (-11/32 : ℝ) with hy100311 | hy100311
            · have hs1003110 : InSquare (29/320) (-111/320) (1/320) tau := by
                convert childLL hs100311 hx100311 hy100311 using 1 <;> norm_num
              exact Batch0203.cell1625.sound htau (by
                simp only [Batch0203.cell1625, Batch0203.tau1625, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003110 (by positivity) using 1 <;> norm_num)
            · have hs1003112 : InSquare (29/320) (-109/320) (1/320) tau := by
                convert childUL hs100311 hx100311 hy100311 using 1 <;> norm_num
              exact Batch0203.cell1627.sound htau (by
                simp only [Batch0203.cell1627, Batch0203.tau1627, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy100311 | hy100311
            · have hs1003111 : InSquare (31/320) (-111/320) (1/320) tau := by
                convert childLR hs100311 hx100311 hy100311 using 1 <;> norm_num
              exact Batch0203.cell1626.sound htau (by
                simp only [Batch0203.cell1626, Batch0203.tau1626, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003111 (by positivity) using 1 <;> norm_num)
            · have hs1003113 : InSquare (31/320) (-109/320) (1/320) tau := by
                convert childUR hs100311 hx100311 hy100311 using 1 <;> norm_num
              exact Batch0203.cell1628.sound htau (by
                simp only [Batch0203.cell1628, Batch0203.tau1628, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003113 (by positivity) using 1 <;> norm_num)
        · have hs100313 : InSquare (3/32) (-53/160) (1/160) tau := by
            convert childUR hs10031 hx10031 hy10031 using 1 <;> norm_num
          exact Batch0072.cell0579.sound htau (by
            simp only [Batch0072.cell0579, Batch0072.tau0579, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100313 (by positivity) using 1 <;> norm_num)
    · have hs10033 : InSquare (7/80) (-5/16) (1/80) tau := by
        convert childUR hs hx1003 hy1003 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx10033 | hx10033
      · rcases le_total tau.im (-5/16 : ℝ) with hy10033 | hy10033
        · have hs100330 : InSquare (13/160) (-51/160) (1/160) tau := by
            convert childLL hs10033 hx10033 hy10033 using 1 <;> norm_num
          exact Batch0073.cell0584.sound htau (by
            simp only [Batch0073.cell0584, Batch0073.tau0584, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100330 (by positivity) using 1 <;> norm_num)
        · have hs100332 : InSquare (13/160) (-49/160) (1/160) tau := by
            convert childUL hs10033 hx10033 hy10033 using 1 <;> norm_num
          exact Batch0073.cell0586.sound htau (by
            simp only [Batch0073.cell0586, Batch0073.tau0586, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10033 | hy10033
        · have hs100331 : InSquare (3/32) (-51/160) (1/160) tau := by
            convert childLR hs10033 hx10033 hy10033 using 1 <;> norm_num
          exact Batch0073.cell0585.sound htau (by
            simp only [Batch0073.cell0585, Batch0073.tau0585, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100331 (by positivity) using 1 <;> norm_num)
        · have hs100333 : InSquare (3/32) (-49/160) (1/160) tau := by
            convert childUR hs10033 hx10033 hy10033 using 1 <;> norm_num
          exact Batch0073.cell0587.sound htau (by
            simp only [Batch0073.cell0587, Batch0073.tau0587, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1003

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1010 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1010

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_101000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (17/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/10)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_101001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (19/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_101010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (21/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/8)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_101011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1010120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (41/320) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/8)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1010121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (43/320) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1010130 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/64) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/80)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1010131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/320) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1010133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/320) (-121/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/160)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10100300 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (73/640) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/80)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10100301 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (15/128) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-37/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10100310 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (77/640) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-19/160)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10100311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (79/640) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-39/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10100313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (79/640) (-49/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-39/320)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10101230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (17/128) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/160)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10101231 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (87/640) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-43/320)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10101320 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (89/640) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/80)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10101321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/640) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/64)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10101323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/640) (-241/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/64)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (-3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx1010 | hx1010
  · rcases le_total tau.im (-3/8 : ℝ) with hy1010 | hy1010
    · have hs10100 : InSquare (9/80) (-31/80) (1/80) tau := by
        convert childLL hs hx1010 hy1010 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx10100 | hx10100
      · rcases le_total tau.im (-31/80 : ℝ) with hy10100 | hy10100
        · have hs101000 : InSquare (17/160) (-63/160) (1/160) tau := by
            convert childLL hs10100 hx10100 hy10100 using 1 <;> norm_num
          exact (outside_101000 htau hs101000).elim
        · have hs101002 : InSquare (17/160) (-61/160) (1/160) tau := by
            convert childUL hs10100 hx10100 hy10100 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx101002 | hx101002
          · rcases le_total tau.im (-61/160 : ℝ) with hy101002 | hy101002
            · have hs1010020 : InSquare (33/320) (-123/320) (1/320) tau := by
                convert childLL hs101002 hx101002 hy101002 using 1 <;> norm_num
              rcases le_total tau.re (33/320 : ℝ) with hx1010020 | hx1010020
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010020 | hy1010020
                · have hs10100200 : InSquare (13/128) (-247/640) (1/640) tau := by
                    convert childLL hs1010020 hx1010020 hy1010020 using 1 <;> norm_num
                  exact Batch0380.cell3047.sound htau (by
                    simp only [Batch0380.cell3047, Batch0380.tau3047, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100200 (by positivity) using 1 <;> norm_num)
                · have hs10100202 : InSquare (13/128) (-49/128) (1/640) tau := by
                    convert childUL hs1010020 hx1010020 hy1010020 using 1 <;> norm_num
                  exact Batch0381.cell3049.sound htau (by
                    simp only [Batch0381.cell3049, Batch0381.tau3049, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010020 | hy1010020
                · have hs10100201 : InSquare (67/640) (-247/640) (1/640) tau := by
                    convert childLR hs1010020 hx1010020 hy1010020 using 1 <;> norm_num
                  exact Batch0381.cell3048.sound htau (by
                    simp only [Batch0381.cell3048, Batch0381.tau3048, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100201 (by positivity) using 1 <;> norm_num)
                · have hs10100203 : InSquare (67/640) (-49/128) (1/640) tau := by
                    convert childUR hs1010020 hx1010020 hy1010020 using 1 <;> norm_num
                  exact Batch0381.cell3050.sound htau (by
                    simp only [Batch0381.cell3050, Batch0381.tau3050, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100203 (by positivity) using 1 <;> norm_num)
            · have hs1010022 : InSquare (33/320) (-121/320) (1/320) tau := by
                convert childUL hs101002 hx101002 hy101002 using 1 <;> norm_num
              rcases le_total tau.re (33/320 : ℝ) with hx1010022 | hx1010022
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010022 | hy1010022
                · have hs10100220 : InSquare (13/128) (-243/640) (1/640) tau := by
                    convert childLL hs1010022 hx1010022 hy1010022 using 1 <;> norm_num
                  exact Batch0381.cell3055.sound htau (by
                    simp only [Batch0381.cell3055, Batch0381.tau3055, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100220 (by positivity) using 1 <;> norm_num)
                · have hs10100222 : InSquare (13/128) (-241/640) (1/640) tau := by
                    convert childUL hs1010022 hx1010022 hy1010022 using 1 <;> norm_num
                  exact Batch0382.cell3057.sound htau (by
                    simp only [Batch0382.cell3057, Batch0382.tau3057, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010022 | hy1010022
                · have hs10100221 : InSquare (67/640) (-243/640) (1/640) tau := by
                    convert childLR hs1010022 hx1010022 hy1010022 using 1 <;> norm_num
                  exact Batch0382.cell3056.sound htau (by
                    simp only [Batch0382.cell3056, Batch0382.tau3056, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100221 (by positivity) using 1 <;> norm_num)
                · have hs10100223 : InSquare (67/640) (-241/640) (1/640) tau := by
                    convert childUR hs1010022 hx1010022 hy1010022 using 1 <;> norm_num
                  exact Batch0382.cell3058.sound htau (by
                    simp only [Batch0382.cell3058, Batch0382.tau3058, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy101002 | hy101002
            · have hs1010021 : InSquare (7/64) (-123/320) (1/320) tau := by
                convert childLR hs101002 hx101002 hy101002 using 1 <;> norm_num
              rcases le_total tau.re (7/64 : ℝ) with hx1010021 | hx1010021
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010021 | hy1010021
                · have hs10100210 : InSquare (69/640) (-247/640) (1/640) tau := by
                    convert childLL hs1010021 hx1010021 hy1010021 using 1 <;> norm_num
                  exact Batch0381.cell3051.sound htau (by
                    simp only [Batch0381.cell3051, Batch0381.tau3051, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100210 (by positivity) using 1 <;> norm_num)
                · have hs10100212 : InSquare (69/640) (-49/128) (1/640) tau := by
                    convert childUL hs1010021 hx1010021 hy1010021 using 1 <;> norm_num
                  exact Batch0381.cell3053.sound htau (by
                    simp only [Batch0381.cell3053, Batch0381.tau3053, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010021 | hy1010021
                · have hs10100211 : InSquare (71/640) (-247/640) (1/640) tau := by
                    convert childLR hs1010021 hx1010021 hy1010021 using 1 <;> norm_num
                  exact Batch0381.cell3052.sound htau (by
                    simp only [Batch0381.cell3052, Batch0381.tau3052, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100211 (by positivity) using 1 <;> norm_num)
                · have hs10100213 : InSquare (71/640) (-49/128) (1/640) tau := by
                    convert childUR hs1010021 hx1010021 hy1010021 using 1 <;> norm_num
                  exact Batch0381.cell3054.sound htau (by
                    simp only [Batch0381.cell3054, Batch0381.tau3054, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100213 (by positivity) using 1 <;> norm_num)
            · have hs1010023 : InSquare (7/64) (-121/320) (1/320) tau := by
                convert childUR hs101002 hx101002 hy101002 using 1 <;> norm_num
              rcases le_total tau.re (7/64 : ℝ) with hx1010023 | hx1010023
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010023 | hy1010023
                · have hs10100230 : InSquare (69/640) (-243/640) (1/640) tau := by
                    convert childLL hs1010023 hx1010023 hy1010023 using 1 <;> norm_num
                  exact Batch0382.cell3059.sound htau (by
                    simp only [Batch0382.cell3059, Batch0382.tau3059, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100230 (by positivity) using 1 <;> norm_num)
                · have hs10100232 : InSquare (69/640) (-241/640) (1/640) tau := by
                    convert childUL hs1010023 hx1010023 hy1010023 using 1 <;> norm_num
                  exact Batch0382.cell3061.sound htau (by
                    simp only [Batch0382.cell3061, Batch0382.tau3061, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010023 | hy1010023
                · have hs10100231 : InSquare (71/640) (-243/640) (1/640) tau := by
                    convert childLR hs1010023 hx1010023 hy1010023 using 1 <;> norm_num
                  exact Batch0382.cell3060.sound htau (by
                    simp only [Batch0382.cell3060, Batch0382.tau3060, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100231 (by positivity) using 1 <;> norm_num)
                · have hs10100233 : InSquare (71/640) (-241/640) (1/640) tau := by
                    convert childUR hs1010023 hx1010023 hy1010023 using 1 <;> norm_num
                  exact Batch0382.cell3062.sound htau (by
                    simp only [Batch0382.cell3062, Batch0382.tau3062, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy10100 | hy10100
        · have hs101001 : InSquare (19/160) (-63/160) (1/160) tau := by
            convert childLR hs10100 hx10100 hy10100 using 1 <;> norm_num
          exact (outside_101001 htau hs101001).elim
        · have hs101003 : InSquare (19/160) (-61/160) (1/160) tau := by
            convert childUR hs10100 hx10100 hy10100 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx101003 | hx101003
          · rcases le_total tau.im (-61/160 : ℝ) with hy101003 | hy101003
            · have hs1010030 : InSquare (37/320) (-123/320) (1/320) tau := by
                convert childLL hs101003 hx101003 hy101003 using 1 <;> norm_num
              rcases le_total tau.re (37/320 : ℝ) with hx1010030 | hx1010030
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010030 | hy1010030
                · have hs10100300 : InSquare (73/640) (-247/640) (1/640) tau := by
                    convert childLL hs1010030 hx1010030 hy1010030 using 1 <;> norm_num
                  exact (outside_10100300 htau hs10100300).elim
                · have hs10100302 : InSquare (73/640) (-49/128) (1/640) tau := by
                    convert childUL hs1010030 hx1010030 hy1010030 using 1 <;> norm_num
                  exact Batch0382.cell3063.sound htau (by
                    simp only [Batch0382.cell3063, Batch0382.tau3063, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010030 | hy1010030
                · have hs10100301 : InSquare (15/128) (-247/640) (1/640) tau := by
                    convert childLR hs1010030 hx1010030 hy1010030 using 1 <;> norm_num
                  exact (outside_10100301 htau hs10100301).elim
                · have hs10100303 : InSquare (15/128) (-49/128) (1/640) tau := by
                    convert childUR hs1010030 hx1010030 hy1010030 using 1 <;> norm_num
                  exact Batch0383.cell3064.sound htau (by
                    simp only [Batch0383.cell3064, Batch0383.tau3064, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100303 (by positivity) using 1 <;> norm_num)
            · have hs1010032 : InSquare (37/320) (-121/320) (1/320) tau := by
                convert childUL hs101003 hx101003 hy101003 using 1 <;> norm_num
              rcases le_total tau.re (37/320 : ℝ) with hx1010032 | hx1010032
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010032 | hy1010032
                · have hs10100320 : InSquare (73/640) (-243/640) (1/640) tau := by
                    convert childLL hs1010032 hx1010032 hy1010032 using 1 <;> norm_num
                  exact Batch0383.cell3066.sound htau (by
                    simp only [Batch0383.cell3066, Batch0383.tau3066, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100320 (by positivity) using 1 <;> norm_num)
                · have hs10100322 : InSquare (73/640) (-241/640) (1/640) tau := by
                    convert childUL hs1010032 hx1010032 hy1010032 using 1 <;> norm_num
                  exact Batch0383.cell3068.sound htau (by
                    simp only [Batch0383.cell3068, Batch0383.tau3068, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010032 | hy1010032
                · have hs10100321 : InSquare (15/128) (-243/640) (1/640) tau := by
                    convert childLR hs1010032 hx1010032 hy1010032 using 1 <;> norm_num
                  exact Batch0383.cell3067.sound htau (by
                    simp only [Batch0383.cell3067, Batch0383.tau3067, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100321 (by positivity) using 1 <;> norm_num)
                · have hs10100323 : InSquare (15/128) (-241/640) (1/640) tau := by
                    convert childUR hs1010032 hx1010032 hy1010032 using 1 <;> norm_num
                  exact Batch0383.cell3069.sound htau (by
                    simp only [Batch0383.cell3069, Batch0383.tau3069, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy101003 | hy101003
            · have hs1010031 : InSquare (39/320) (-123/320) (1/320) tau := by
                convert childLR hs101003 hx101003 hy101003 using 1 <;> norm_num
              rcases le_total tau.re (39/320 : ℝ) with hx1010031 | hx1010031
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010031 | hy1010031
                · have hs10100310 : InSquare (77/640) (-247/640) (1/640) tau := by
                    convert childLL hs1010031 hx1010031 hy1010031 using 1 <;> norm_num
                  exact (outside_10100310 htau hs10100310).elim
                · have hs10100312 : InSquare (77/640) (-49/128) (1/640) tau := by
                    convert childUL hs1010031 hx1010031 hy1010031 using 1 <;> norm_num
                  exact Batch0383.cell3065.sound htau (by
                    simp only [Batch0383.cell3065, Batch0383.tau3065, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010031 | hy1010031
                · have hs10100311 : InSquare (79/640) (-247/640) (1/640) tau := by
                    convert childLR hs1010031 hx1010031 hy1010031 using 1 <;> norm_num
                  exact (outside_10100311 htau hs10100311).elim
                · have hs10100313 : InSquare (79/640) (-49/128) (1/640) tau := by
                    convert childUR hs1010031 hx1010031 hy1010031 using 1 <;> norm_num
                  exact (outside_10100313 htau hs10100313).elim
            · have hs1010033 : InSquare (39/320) (-121/320) (1/320) tau := by
                convert childUR hs101003 hx101003 hy101003 using 1 <;> norm_num
              rcases le_total tau.re (39/320 : ℝ) with hx1010033 | hx1010033
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010033 | hy1010033
                · have hs10100330 : InSquare (77/640) (-243/640) (1/640) tau := by
                    convert childLL hs1010033 hx1010033 hy1010033 using 1 <;> norm_num
                  exact Batch0383.cell3070.sound htau (by
                    simp only [Batch0383.cell3070, Batch0383.tau3070, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100330 (by positivity) using 1 <;> norm_num)
                · have hs10100332 : InSquare (77/640) (-241/640) (1/640) tau := by
                    convert childUL hs1010033 hx1010033 hy1010033 using 1 <;> norm_num
                  exact Batch0384.cell3072.sound htau (by
                    simp only [Batch0384.cell3072, Batch0384.tau3072, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010033 | hy1010033
                · have hs10100331 : InSquare (79/640) (-243/640) (1/640) tau := by
                    convert childLR hs1010033 hx1010033 hy1010033 using 1 <;> norm_num
                  exact Batch0383.cell3071.sound htau (by
                    simp only [Batch0383.cell3071, Batch0383.tau3071, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100331 (by positivity) using 1 <;> norm_num)
                · have hs10100333 : InSquare (79/640) (-241/640) (1/640) tau := by
                    convert childUR hs1010033 hx1010033 hy1010033 using 1 <;> norm_num
                  exact Batch0384.cell3073.sound htau (by
                    simp only [Batch0384.cell3073, Batch0384.tau3073, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100333 (by positivity) using 1 <;> norm_num)
    · have hs10102 : InSquare (9/80) (-29/80) (1/80) tau := by
        convert childUL hs hx1010 hy1010 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx10102 | hx10102
      · rcases le_total tau.im (-29/80 : ℝ) with hy10102 | hy10102
        · have hs101020 : InSquare (17/160) (-59/160) (1/160) tau := by
            convert childLL hs10102 hx10102 hy10102 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx101020 | hx101020
          · rcases le_total tau.im (-59/160 : ℝ) with hy101020 | hy101020
            · have hs1010200 : InSquare (33/320) (-119/320) (1/320) tau := by
                convert childLL hs101020 hx101020 hy101020 using 1 <;> norm_num
              rcases le_total tau.re (33/320 : ℝ) with hx1010200 | hx1010200
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010200 | hy1010200
                · have hs10102000 : InSquare (13/128) (-239/640) (1/640) tau := by
                    convert childLL hs1010200 hx1010200 hy1010200 using 1 <;> norm_num
                  exact Batch0385.cell3081.sound htau (by
                    simp only [Batch0385.cell3081, Batch0385.tau3081, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102000 (by positivity) using 1 <;> norm_num)
                · have hs10102002 : InSquare (13/128) (-237/640) (1/640) tau := by
                    convert childUL hs1010200 hx1010200 hy1010200 using 1 <;> norm_num
                  exact Batch0385.cell3083.sound htau (by
                    simp only [Batch0385.cell3083, Batch0385.tau3083, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010200 | hy1010200
                · have hs10102001 : InSquare (67/640) (-239/640) (1/640) tau := by
                    convert childLR hs1010200 hx1010200 hy1010200 using 1 <;> norm_num
                  exact Batch0385.cell3082.sound htau (by
                    simp only [Batch0385.cell3082, Batch0385.tau3082, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102001 (by positivity) using 1 <;> norm_num)
                · have hs10102003 : InSquare (67/640) (-237/640) (1/640) tau := by
                    convert childUR hs1010200 hx1010200 hy1010200 using 1 <;> norm_num
                  exact Batch0385.cell3084.sound htau (by
                    simp only [Batch0385.cell3084, Batch0385.tau3084, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102003 (by positivity) using 1 <;> norm_num)
            · have hs1010202 : InSquare (33/320) (-117/320) (1/320) tau := by
                convert childUL hs101020 hx101020 hy101020 using 1 <;> norm_num
              exact Batch0203.cell1629.sound htau (by
                simp only [Batch0203.cell1629, Batch0203.tau1629, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy101020 | hy101020
            · have hs1010201 : InSquare (7/64) (-119/320) (1/320) tau := by
                convert childLR hs101020 hx101020 hy101020 using 1 <;> norm_num
              rcases le_total tau.re (7/64 : ℝ) with hx1010201 | hx1010201
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010201 | hy1010201
                · have hs10102010 : InSquare (69/640) (-239/640) (1/640) tau := by
                    convert childLL hs1010201 hx1010201 hy1010201 using 1 <;> norm_num
                  exact Batch0385.cell3085.sound htau (by
                    simp only [Batch0385.cell3085, Batch0385.tau3085, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102010 (by positivity) using 1 <;> norm_num)
                · have hs10102012 : InSquare (69/640) (-237/640) (1/640) tau := by
                    convert childUL hs1010201 hx1010201 hy1010201 using 1 <;> norm_num
                  exact Batch0385.cell3087.sound htau (by
                    simp only [Batch0385.cell3087, Batch0385.tau3087, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010201 | hy1010201
                · have hs10102011 : InSquare (71/640) (-239/640) (1/640) tau := by
                    convert childLR hs1010201 hx1010201 hy1010201 using 1 <;> norm_num
                  exact Batch0385.cell3086.sound htau (by
                    simp only [Batch0385.cell3086, Batch0385.tau3086, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102011 (by positivity) using 1 <;> norm_num)
                · have hs10102013 : InSquare (71/640) (-237/640) (1/640) tau := by
                    convert childUR hs1010201 hx1010201 hy1010201 using 1 <;> norm_num
                  exact Batch0386.cell3088.sound htau (by
                    simp only [Batch0386.cell3088, Batch0386.tau3088, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102013 (by positivity) using 1 <;> norm_num)
            · have hs1010203 : InSquare (7/64) (-117/320) (1/320) tau := by
                convert childUR hs101020 hx101020 hy101020 using 1 <;> norm_num
              exact Batch0203.cell1630.sound htau (by
                simp only [Batch0203.cell1630, Batch0203.tau1630, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010203 (by positivity) using 1 <;> norm_num)
        · have hs101022 : InSquare (17/160) (-57/160) (1/160) tau := by
            convert childUL hs10102 hx10102 hy10102 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx101022 | hx101022
          · rcases le_total tau.im (-57/160 : ℝ) with hy101022 | hy101022
            · have hs1010220 : InSquare (33/320) (-23/64) (1/320) tau := by
                convert childLL hs101022 hx101022 hy101022 using 1 <;> norm_num
              exact Batch0204.cell1633.sound htau (by
                simp only [Batch0204.cell1633, Batch0204.tau1633, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010220 (by positivity) using 1 <;> norm_num)
            · have hs1010222 : InSquare (33/320) (-113/320) (1/320) tau := by
                convert childUL hs101022 hx101022 hy101022 using 1 <;> norm_num
              exact Batch0204.cell1635.sound htau (by
                simp only [Batch0204.cell1635, Batch0204.tau1635, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101022 | hy101022
            · have hs1010221 : InSquare (7/64) (-23/64) (1/320) tau := by
                convert childLR hs101022 hx101022 hy101022 using 1 <;> norm_num
              exact Batch0204.cell1634.sound htau (by
                simp only [Batch0204.cell1634, Batch0204.tau1634, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010221 (by positivity) using 1 <;> norm_num)
            · have hs1010223 : InSquare (7/64) (-113/320) (1/320) tau := by
                convert childUR hs101022 hx101022 hy101022 using 1 <;> norm_num
              exact Batch0204.cell1636.sound htau (by
                simp only [Batch0204.cell1636, Batch0204.tau1636, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy10102 | hy10102
        · have hs101021 : InSquare (19/160) (-59/160) (1/160) tau := by
            convert childLR hs10102 hx10102 hy10102 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx101021 | hx101021
          · rcases le_total tau.im (-59/160 : ℝ) with hy101021 | hy101021
            · have hs1010210 : InSquare (37/320) (-119/320) (1/320) tau := by
                convert childLL hs101021 hx101021 hy101021 using 1 <;> norm_num
              rcases le_total tau.re (37/320 : ℝ) with hx1010210 | hx1010210
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010210 | hy1010210
                · have hs10102100 : InSquare (73/640) (-239/640) (1/640) tau := by
                    convert childLL hs1010210 hx1010210 hy1010210 using 1 <;> norm_num
                  exact Batch0386.cell3089.sound htau (by
                    simp only [Batch0386.cell3089, Batch0386.tau3089, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102100 (by positivity) using 1 <;> norm_num)
                · have hs10102102 : InSquare (73/640) (-237/640) (1/640) tau := by
                    convert childUL hs1010210 hx1010210 hy1010210 using 1 <;> norm_num
                  exact Batch0386.cell3091.sound htau (by
                    simp only [Batch0386.cell3091, Batch0386.tau3091, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010210 | hy1010210
                · have hs10102101 : InSquare (15/128) (-239/640) (1/640) tau := by
                    convert childLR hs1010210 hx1010210 hy1010210 using 1 <;> norm_num
                  exact Batch0386.cell3090.sound htau (by
                    simp only [Batch0386.cell3090, Batch0386.tau3090, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102101 (by positivity) using 1 <;> norm_num)
                · have hs10102103 : InSquare (15/128) (-237/640) (1/640) tau := by
                    convert childUR hs1010210 hx1010210 hy1010210 using 1 <;> norm_num
                  exact Batch0386.cell3092.sound htau (by
                    simp only [Batch0386.cell3092, Batch0386.tau3092, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102103 (by positivity) using 1 <;> norm_num)
            · have hs1010212 : InSquare (37/320) (-117/320) (1/320) tau := by
                convert childUL hs101021 hx101021 hy101021 using 1 <;> norm_num
              exact Batch0203.cell1631.sound htau (by
                simp only [Batch0203.cell1631, Batch0203.tau1631, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy101021 | hy101021
            · have hs1010211 : InSquare (39/320) (-119/320) (1/320) tau := by
                convert childLR hs101021 hx101021 hy101021 using 1 <;> norm_num
              rcases le_total tau.re (39/320 : ℝ) with hx1010211 | hx1010211
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010211 | hy1010211
                · have hs10102110 : InSquare (77/640) (-239/640) (1/640) tau := by
                    convert childLL hs1010211 hx1010211 hy1010211 using 1 <;> norm_num
                  exact Batch0386.cell3093.sound htau (by
                    simp only [Batch0386.cell3093, Batch0386.tau3093, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102110 (by positivity) using 1 <;> norm_num)
                · have hs10102112 : InSquare (77/640) (-237/640) (1/640) tau := by
                    convert childUL hs1010211 hx1010211 hy1010211 using 1 <;> norm_num
                  exact Batch0386.cell3095.sound htau (by
                    simp only [Batch0386.cell3095, Batch0386.tau3095, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010211 | hy1010211
                · have hs10102111 : InSquare (79/640) (-239/640) (1/640) tau := by
                    convert childLR hs1010211 hx1010211 hy1010211 using 1 <;> norm_num
                  exact Batch0386.cell3094.sound htau (by
                    simp only [Batch0386.cell3094, Batch0386.tau3094, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102111 (by positivity) using 1 <;> norm_num)
                · have hs10102113 : InSquare (79/640) (-237/640) (1/640) tau := by
                    convert childUR hs1010211 hx1010211 hy1010211 using 1 <;> norm_num
                  exact Batch0387.cell3096.sound htau (by
                    simp only [Batch0387.cell3096, Batch0387.tau3096, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102113 (by positivity) using 1 <;> norm_num)
            · have hs1010213 : InSquare (39/320) (-117/320) (1/320) tau := by
                convert childUR hs101021 hx101021 hy101021 using 1 <;> norm_num
              exact Batch0204.cell1632.sound htau (by
                simp only [Batch0204.cell1632, Batch0204.tau1632, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010213 (by positivity) using 1 <;> norm_num)
        · have hs101023 : InSquare (19/160) (-57/160) (1/160) tau := by
            convert childUR hs10102 hx10102 hy10102 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx101023 | hx101023
          · rcases le_total tau.im (-57/160 : ℝ) with hy101023 | hy101023
            · have hs1010230 : InSquare (37/320) (-23/64) (1/320) tau := by
                convert childLL hs101023 hx101023 hy101023 using 1 <;> norm_num
              exact Batch0204.cell1637.sound htau (by
                simp only [Batch0204.cell1637, Batch0204.tau1637, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010230 (by positivity) using 1 <;> norm_num)
            · have hs1010232 : InSquare (37/320) (-113/320) (1/320) tau := by
                convert childUL hs101023 hx101023 hy101023 using 1 <;> norm_num
              exact Batch0204.cell1639.sound htau (by
                simp only [Batch0204.cell1639, Batch0204.tau1639, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101023 | hy101023
            · have hs1010231 : InSquare (39/320) (-23/64) (1/320) tau := by
                convert childLR hs101023 hx101023 hy101023 using 1 <;> norm_num
              exact Batch0204.cell1638.sound htau (by
                simp only [Batch0204.cell1638, Batch0204.tau1638, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010231 (by positivity) using 1 <;> norm_num)
            · have hs1010233 : InSquare (39/320) (-113/320) (1/320) tau := by
                convert childUR hs101023 hx101023 hy101023 using 1 <;> norm_num
              exact Batch0205.cell1640.sound htau (by
                simp only [Batch0205.cell1640, Batch0205.tau1640, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/8 : ℝ) with hy1010 | hy1010
    · have hs10101 : InSquare (11/80) (-31/80) (1/80) tau := by
        convert childLR hs hx1010 hy1010 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx10101 | hx10101
      · rcases le_total tau.im (-31/80 : ℝ) with hy10101 | hy10101
        · have hs101010 : InSquare (21/160) (-63/160) (1/160) tau := by
            convert childLL hs10101 hx10101 hy10101 using 1 <;> norm_num
          exact (outside_101010 htau hs101010).elim
        · have hs101012 : InSquare (21/160) (-61/160) (1/160) tau := by
            convert childUL hs10101 hx10101 hy10101 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx101012 | hx101012
          · rcases le_total tau.im (-61/160 : ℝ) with hy101012 | hy101012
            · have hs1010120 : InSquare (41/320) (-123/320) (1/320) tau := by
                convert childLL hs101012 hx101012 hy101012 using 1 <;> norm_num
              exact (outside_1010120 htau hs1010120).elim
            · have hs1010122 : InSquare (41/320) (-121/320) (1/320) tau := by
                convert childUL hs101012 hx101012 hy101012 using 1 <;> norm_num
              rcases le_total tau.re (41/320 : ℝ) with hx1010122 | hx1010122
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010122 | hy1010122
                · have hs10101220 : InSquare (81/640) (-243/640) (1/640) tau := by
                    convert childLL hs1010122 hx1010122 hy1010122 using 1 <;> norm_num
                  exact Batch0384.cell3074.sound htau (by
                    simp only [Batch0384.cell3074, Batch0384.tau3074, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10101220 (by positivity) using 1 <;> norm_num)
                · have hs10101222 : InSquare (81/640) (-241/640) (1/640) tau := by
                    convert childUL hs1010122 hx1010122 hy1010122 using 1 <;> norm_num
                  exact Batch0384.cell3076.sound htau (by
                    simp only [Batch0384.cell3076, Batch0384.tau3076, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10101222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010122 | hy1010122
                · have hs10101221 : InSquare (83/640) (-243/640) (1/640) tau := by
                    convert childLR hs1010122 hx1010122 hy1010122 using 1 <;> norm_num
                  exact Batch0384.cell3075.sound htau (by
                    simp only [Batch0384.cell3075, Batch0384.tau3075, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10101221 (by positivity) using 1 <;> norm_num)
                · have hs10101223 : InSquare (83/640) (-241/640) (1/640) tau := by
                    convert childUR hs1010122 hx1010122 hy1010122 using 1 <;> norm_num
                  exact Batch0384.cell3077.sound htau (by
                    simp only [Batch0384.cell3077, Batch0384.tau3077, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10101223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy101012 | hy101012
            · have hs1010121 : InSquare (43/320) (-123/320) (1/320) tau := by
                convert childLR hs101012 hx101012 hy101012 using 1 <;> norm_num
              exact (outside_1010121 htau hs1010121).elim
            · have hs1010123 : InSquare (43/320) (-121/320) (1/320) tau := by
                convert childUR hs101012 hx101012 hy101012 using 1 <;> norm_num
              rcases le_total tau.re (43/320 : ℝ) with hx1010123 | hx1010123
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010123 | hy1010123
                · have hs10101230 : InSquare (17/128) (-243/640) (1/640) tau := by
                    convert childLL hs1010123 hx1010123 hy1010123 using 1 <;> norm_num
                  exact (outside_10101230 htau hs10101230).elim
                · have hs10101232 : InSquare (17/128) (-241/640) (1/640) tau := by
                    convert childUL hs1010123 hx1010123 hy1010123 using 1 <;> norm_num
                  exact Batch0384.cell3078.sound htau (by
                    simp only [Batch0384.cell3078, Batch0384.tau3078, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10101232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010123 | hy1010123
                · have hs10101231 : InSquare (87/640) (-243/640) (1/640) tau := by
                    convert childLR hs1010123 hx1010123 hy1010123 using 1 <;> norm_num
                  exact (outside_10101231 htau hs10101231).elim
                · have hs10101233 : InSquare (87/640) (-241/640) (1/640) tau := by
                    convert childUR hs1010123 hx1010123 hy1010123 using 1 <;> norm_num
                  exact Batch0384.cell3079.sound htau (by
                    simp only [Batch0384.cell3079, Batch0384.tau3079, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10101233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy10101 | hy10101
        · have hs101011 : InSquare (23/160) (-63/160) (1/160) tau := by
            convert childLR hs10101 hx10101 hy10101 using 1 <;> norm_num
          exact (outside_101011 htau hs101011).elim
        · have hs101013 : InSquare (23/160) (-61/160) (1/160) tau := by
            convert childUR hs10101 hx10101 hy10101 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx101013 | hx101013
          · rcases le_total tau.im (-61/160 : ℝ) with hy101013 | hy101013
            · have hs1010130 : InSquare (9/64) (-123/320) (1/320) tau := by
                convert childLL hs101013 hx101013 hy101013 using 1 <;> norm_num
              exact (outside_1010130 htau hs1010130).elim
            · have hs1010132 : InSquare (9/64) (-121/320) (1/320) tau := by
                convert childUL hs101013 hx101013 hy101013 using 1 <;> norm_num
              rcases le_total tau.re (9/64 : ℝ) with hx1010132 | hx1010132
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010132 | hy1010132
                · have hs10101320 : InSquare (89/640) (-243/640) (1/640) tau := by
                    convert childLL hs1010132 hx1010132 hy1010132 using 1 <;> norm_num
                  exact (outside_10101320 htau hs10101320).elim
                · have hs10101322 : InSquare (89/640) (-241/640) (1/640) tau := by
                    convert childUL hs1010132 hx1010132 hy1010132 using 1 <;> norm_num
                  exact Batch0385.cell3080.sound htau (by
                    simp only [Batch0385.cell3080, Batch0385.tau3080, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10101322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010132 | hy1010132
                · have hs10101321 : InSquare (91/640) (-243/640) (1/640) tau := by
                    convert childLR hs1010132 hx1010132 hy1010132 using 1 <;> norm_num
                  exact (outside_10101321 htau hs10101321).elim
                · have hs10101323 : InSquare (91/640) (-241/640) (1/640) tau := by
                    convert childUR hs1010132 hx1010132 hy1010132 using 1 <;> norm_num
                  exact (outside_10101323 htau hs10101323).elim
          · rcases le_total tau.im (-61/160 : ℝ) with hy101013 | hy101013
            · have hs1010131 : InSquare (47/320) (-123/320) (1/320) tau := by
                convert childLR hs101013 hx101013 hy101013 using 1 <;> norm_num
              exact (outside_1010131 htau hs1010131).elim
            · have hs1010133 : InSquare (47/320) (-121/320) (1/320) tau := by
                convert childUR hs101013 hx101013 hy101013 using 1 <;> norm_num
              exact (outside_1010133 htau hs1010133).elim
    · have hs10103 : InSquare (11/80) (-29/80) (1/80) tau := by
        convert childUR hs hx1010 hy1010 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx10103 | hx10103
      · rcases le_total tau.im (-29/80 : ℝ) with hy10103 | hy10103
        · have hs101030 : InSquare (21/160) (-59/160) (1/160) tau := by
            convert childLL hs10103 hx10103 hy10103 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx101030 | hx101030
          · rcases le_total tau.im (-59/160 : ℝ) with hy101030 | hy101030
            · have hs1010300 : InSquare (41/320) (-119/320) (1/320) tau := by
                convert childLL hs101030 hx101030 hy101030 using 1 <;> norm_num
              rcases le_total tau.re (41/320 : ℝ) with hx1010300 | hx1010300
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010300 | hy1010300
                · have hs10103000 : InSquare (81/640) (-239/640) (1/640) tau := by
                    convert childLL hs1010300 hx1010300 hy1010300 using 1 <;> norm_num
                  exact Batch0387.cell3097.sound htau (by
                    simp only [Batch0387.cell3097, Batch0387.tau3097, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103000 (by positivity) using 1 <;> norm_num)
                · have hs10103002 : InSquare (81/640) (-237/640) (1/640) tau := by
                    convert childUL hs1010300 hx1010300 hy1010300 using 1 <;> norm_num
                  exact Batch0387.cell3099.sound htau (by
                    simp only [Batch0387.cell3099, Batch0387.tau3099, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010300 | hy1010300
                · have hs10103001 : InSquare (83/640) (-239/640) (1/640) tau := by
                    convert childLR hs1010300 hx1010300 hy1010300 using 1 <;> norm_num
                  exact Batch0387.cell3098.sound htau (by
                    simp only [Batch0387.cell3098, Batch0387.tau3098, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103001 (by positivity) using 1 <;> norm_num)
                · have hs10103003 : InSquare (83/640) (-237/640) (1/640) tau := by
                    convert childUR hs1010300 hx1010300 hy1010300 using 1 <;> norm_num
                  exact Batch0387.cell3100.sound htau (by
                    simp only [Batch0387.cell3100, Batch0387.tau3100, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103003 (by positivity) using 1 <;> norm_num)
            · have hs1010302 : InSquare (41/320) (-117/320) (1/320) tau := by
                convert childUL hs101030 hx101030 hy101030 using 1 <;> norm_num
              rcases le_total tau.re (41/320 : ℝ) with hx1010302 | hx1010302
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010302 | hy1010302
                · have hs10103020 : InSquare (81/640) (-47/128) (1/640) tau := by
                    convert childLL hs1010302 hx1010302 hy1010302 using 1 <;> norm_num
                  exact Batch0388.cell3105.sound htau (by
                    simp only [Batch0388.cell3105, Batch0388.tau3105, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103020 (by positivity) using 1 <;> norm_num)
                · have hs10103022 : InSquare (81/640) (-233/640) (1/640) tau := by
                    convert childUL hs1010302 hx1010302 hy1010302 using 1 <;> norm_num
                  exact Batch0388.cell3107.sound htau (by
                    simp only [Batch0388.cell3107, Batch0388.tau3107, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010302 | hy1010302
                · have hs10103021 : InSquare (83/640) (-47/128) (1/640) tau := by
                    convert childLR hs1010302 hx1010302 hy1010302 using 1 <;> norm_num
                  exact Batch0388.cell3106.sound htau (by
                    simp only [Batch0388.cell3106, Batch0388.tau3106, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103021 (by positivity) using 1 <;> norm_num)
                · have hs10103023 : InSquare (83/640) (-233/640) (1/640) tau := by
                    convert childUR hs1010302 hx1010302 hy1010302 using 1 <;> norm_num
                  exact Batch0388.cell3108.sound htau (by
                    simp only [Batch0388.cell3108, Batch0388.tau3108, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy101030 | hy101030
            · have hs1010301 : InSquare (43/320) (-119/320) (1/320) tau := by
                convert childLR hs101030 hx101030 hy101030 using 1 <;> norm_num
              rcases le_total tau.re (43/320 : ℝ) with hx1010301 | hx1010301
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010301 | hy1010301
                · have hs10103010 : InSquare (17/128) (-239/640) (1/640) tau := by
                    convert childLL hs1010301 hx1010301 hy1010301 using 1 <;> norm_num
                  exact Batch0387.cell3101.sound htau (by
                    simp only [Batch0387.cell3101, Batch0387.tau3101, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103010 (by positivity) using 1 <;> norm_num)
                · have hs10103012 : InSquare (17/128) (-237/640) (1/640) tau := by
                    convert childUL hs1010301 hx1010301 hy1010301 using 1 <;> norm_num
                  exact Batch0387.cell3103.sound htau (by
                    simp only [Batch0387.cell3103, Batch0387.tau3103, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010301 | hy1010301
                · have hs10103011 : InSquare (87/640) (-239/640) (1/640) tau := by
                    convert childLR hs1010301 hx1010301 hy1010301 using 1 <;> norm_num
                  exact Batch0387.cell3102.sound htau (by
                    simp only [Batch0387.cell3102, Batch0387.tau3102, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103011 (by positivity) using 1 <;> norm_num)
                · have hs10103013 : InSquare (87/640) (-237/640) (1/640) tau := by
                    convert childUR hs1010301 hx1010301 hy1010301 using 1 <;> norm_num
                  exact Batch0388.cell3104.sound htau (by
                    simp only [Batch0388.cell3104, Batch0388.tau3104, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103013 (by positivity) using 1 <;> norm_num)
            · have hs1010303 : InSquare (43/320) (-117/320) (1/320) tau := by
                convert childUR hs101030 hx101030 hy101030 using 1 <;> norm_num
              rcases le_total tau.re (43/320 : ℝ) with hx1010303 | hx1010303
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010303 | hy1010303
                · have hs10103030 : InSquare (17/128) (-47/128) (1/640) tau := by
                    convert childLL hs1010303 hx1010303 hy1010303 using 1 <;> norm_num
                  exact Batch0388.cell3109.sound htau (by
                    simp only [Batch0388.cell3109, Batch0388.tau3109, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103030 (by positivity) using 1 <;> norm_num)
                · have hs10103032 : InSquare (17/128) (-233/640) (1/640) tau := by
                    convert childUL hs1010303 hx1010303 hy1010303 using 1 <;> norm_num
                  exact Batch0388.cell3111.sound htau (by
                    simp only [Batch0388.cell3111, Batch0388.tau3111, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010303 | hy1010303
                · have hs10103031 : InSquare (87/640) (-47/128) (1/640) tau := by
                    convert childLR hs1010303 hx1010303 hy1010303 using 1 <;> norm_num
                  exact Batch0388.cell3110.sound htau (by
                    simp only [Batch0388.cell3110, Batch0388.tau3110, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103031 (by positivity) using 1 <;> norm_num)
                · have hs10103033 : InSquare (87/640) (-233/640) (1/640) tau := by
                    convert childUR hs1010303 hx1010303 hy1010303 using 1 <;> norm_num
                  exact Batch0389.cell3112.sound htau (by
                    simp only [Batch0389.cell3112, Batch0389.tau3112, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103033 (by positivity) using 1 <;> norm_num)
        · have hs101032 : InSquare (21/160) (-57/160) (1/160) tau := by
            convert childUL hs10103 hx10103 hy10103 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx101032 | hx101032
          · rcases le_total tau.im (-57/160 : ℝ) with hy101032 | hy101032
            · have hs1010320 : InSquare (41/320) (-23/64) (1/320) tau := by
                convert childLL hs101032 hx101032 hy101032 using 1 <;> norm_num
              exact Batch0205.cell1641.sound htau (by
                simp only [Batch0205.cell1641, Batch0205.tau1641, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010320 (by positivity) using 1 <;> norm_num)
            · have hs1010322 : InSquare (41/320) (-113/320) (1/320) tau := by
                convert childUL hs101032 hx101032 hy101032 using 1 <;> norm_num
              exact Batch0205.cell1643.sound htau (by
                simp only [Batch0205.cell1643, Batch0205.tau1643, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101032 | hy101032
            · have hs1010321 : InSquare (43/320) (-23/64) (1/320) tau := by
                convert childLR hs101032 hx101032 hy101032 using 1 <;> norm_num
              exact Batch0205.cell1642.sound htau (by
                simp only [Batch0205.cell1642, Batch0205.tau1642, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010321 (by positivity) using 1 <;> norm_num)
            · have hs1010323 : InSquare (43/320) (-113/320) (1/320) tau := by
                convert childUR hs101032 hx101032 hy101032 using 1 <;> norm_num
              exact Batch0205.cell1644.sound htau (by
                simp only [Batch0205.cell1644, Batch0205.tau1644, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy10103 | hy10103
        · have hs101031 : InSquare (23/160) (-59/160) (1/160) tau := by
            convert childLR hs10103 hx10103 hy10103 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx101031 | hx101031
          · rcases le_total tau.im (-59/160 : ℝ) with hy101031 | hy101031
            · have hs1010310 : InSquare (9/64) (-119/320) (1/320) tau := by
                convert childLL hs101031 hx101031 hy101031 using 1 <;> norm_num
              rcases le_total tau.re (9/64 : ℝ) with hx1010310 | hx1010310
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010310 | hy1010310
                · have hs10103100 : InSquare (89/640) (-239/640) (1/640) tau := by
                    convert childLL hs1010310 hx1010310 hy1010310 using 1 <;> norm_num
                  exact Batch0389.cell3113.sound htau (by
                    simp only [Batch0389.cell3113, Batch0389.tau3113, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103100 (by positivity) using 1 <;> norm_num)
                · have hs10103102 : InSquare (89/640) (-237/640) (1/640) tau := by
                    convert childUL hs1010310 hx1010310 hy1010310 using 1 <;> norm_num
                  exact Batch0389.cell3115.sound htau (by
                    simp only [Batch0389.cell3115, Batch0389.tau3115, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010310 | hy1010310
                · have hs10103101 : InSquare (91/640) (-239/640) (1/640) tau := by
                    convert childLR hs1010310 hx1010310 hy1010310 using 1 <;> norm_num
                  exact Batch0389.cell3114.sound htau (by
                    simp only [Batch0389.cell3114, Batch0389.tau3114, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103101 (by positivity) using 1 <;> norm_num)
                · have hs10103103 : InSquare (91/640) (-237/640) (1/640) tau := by
                    convert childUR hs1010310 hx1010310 hy1010310 using 1 <;> norm_num
                  exact Batch0389.cell3116.sound htau (by
                    simp only [Batch0389.cell3116, Batch0389.tau3116, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103103 (by positivity) using 1 <;> norm_num)
            · have hs1010312 : InSquare (9/64) (-117/320) (1/320) tau := by
                convert childUL hs101031 hx101031 hy101031 using 1 <;> norm_num
              rcases le_total tau.re (9/64 : ℝ) with hx1010312 | hx1010312
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010312 | hy1010312
                · have hs10103120 : InSquare (89/640) (-47/128) (1/640) tau := by
                    convert childLL hs1010312 hx1010312 hy1010312 using 1 <;> norm_num
                  exact Batch0390.cell3121.sound htau (by
                    simp only [Batch0390.cell3121, Batch0390.tau3121, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103120 (by positivity) using 1 <;> norm_num)
                · have hs10103122 : InSquare (89/640) (-233/640) (1/640) tau := by
                    convert childUL hs1010312 hx1010312 hy1010312 using 1 <;> norm_num
                  exact Batch0390.cell3123.sound htau (by
                    simp only [Batch0390.cell3123, Batch0390.tau3123, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010312 | hy1010312
                · have hs10103121 : InSquare (91/640) (-47/128) (1/640) tau := by
                    convert childLR hs1010312 hx1010312 hy1010312 using 1 <;> norm_num
                  exact Batch0390.cell3122.sound htau (by
                    simp only [Batch0390.cell3122, Batch0390.tau3122, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103121 (by positivity) using 1 <;> norm_num)
                · have hs10103123 : InSquare (91/640) (-233/640) (1/640) tau := by
                    convert childUR hs1010312 hx1010312 hy1010312 using 1 <;> norm_num
                  exact Batch0390.cell3124.sound htau (by
                    simp only [Batch0390.cell3124, Batch0390.tau3124, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy101031 | hy101031
            · have hs1010311 : InSquare (47/320) (-119/320) (1/320) tau := by
                convert childLR hs101031 hx101031 hy101031 using 1 <;> norm_num
              rcases le_total tau.re (47/320 : ℝ) with hx1010311 | hx1010311
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010311 | hy1010311
                · have hs10103110 : InSquare (93/640) (-239/640) (1/640) tau := by
                    convert childLL hs1010311 hx1010311 hy1010311 using 1 <;> norm_num
                  exact Batch0389.cell3117.sound htau (by
                    simp only [Batch0389.cell3117, Batch0389.tau3117, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103110 (by positivity) using 1 <;> norm_num)
                · have hs10103112 : InSquare (93/640) (-237/640) (1/640) tau := by
                    convert childUL hs1010311 hx1010311 hy1010311 using 1 <;> norm_num
                  exact Batch0389.cell3119.sound htau (by
                    simp only [Batch0389.cell3119, Batch0389.tau3119, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010311 | hy1010311
                · have hs10103111 : InSquare (19/128) (-239/640) (1/640) tau := by
                    convert childLR hs1010311 hx1010311 hy1010311 using 1 <;> norm_num
                  exact Batch0389.cell3118.sound htau (by
                    simp only [Batch0389.cell3118, Batch0389.tau3118, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103111 (by positivity) using 1 <;> norm_num)
                · have hs10103113 : InSquare (19/128) (-237/640) (1/640) tau := by
                    convert childUR hs1010311 hx1010311 hy1010311 using 1 <;> norm_num
                  exact Batch0390.cell3120.sound htau (by
                    simp only [Batch0390.cell3120, Batch0390.tau3120, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103113 (by positivity) using 1 <;> norm_num)
            · have hs1010313 : InSquare (47/320) (-117/320) (1/320) tau := by
                convert childUR hs101031 hx101031 hy101031 using 1 <;> norm_num
              rcases le_total tau.re (47/320 : ℝ) with hx1010313 | hx1010313
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010313 | hy1010313
                · have hs10103130 : InSquare (93/640) (-47/128) (1/640) tau := by
                    convert childLL hs1010313 hx1010313 hy1010313 using 1 <;> norm_num
                  exact Batch0390.cell3125.sound htau (by
                    simp only [Batch0390.cell3125, Batch0390.tau3125, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103130 (by positivity) using 1 <;> norm_num)
                · have hs10103132 : InSquare (93/640) (-233/640) (1/640) tau := by
                    convert childUL hs1010313 hx1010313 hy1010313 using 1 <;> norm_num
                  exact Batch0390.cell3127.sound htau (by
                    simp only [Batch0390.cell3127, Batch0390.tau3127, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010313 | hy1010313
                · have hs10103131 : InSquare (19/128) (-47/128) (1/640) tau := by
                    convert childLR hs1010313 hx1010313 hy1010313 using 1 <;> norm_num
                  exact Batch0390.cell3126.sound htau (by
                    simp only [Batch0390.cell3126, Batch0390.tau3126, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103131 (by positivity) using 1 <;> norm_num)
                · have hs10103133 : InSquare (19/128) (-233/640) (1/640) tau := by
                    convert childUR hs1010313 hx1010313 hy1010313 using 1 <;> norm_num
                  exact Batch0391.cell3128.sound htau (by
                    simp only [Batch0391.cell3128, Batch0391.tau3128, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103133 (by positivity) using 1 <;> norm_num)
        · have hs101033 : InSquare (23/160) (-57/160) (1/160) tau := by
            convert childUR hs10103 hx10103 hy10103 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx101033 | hx101033
          · rcases le_total tau.im (-57/160 : ℝ) with hy101033 | hy101033
            · have hs1010330 : InSquare (9/64) (-23/64) (1/320) tau := by
                convert childLL hs101033 hx101033 hy101033 using 1 <;> norm_num
              exact Batch0205.cell1645.sound htau (by
                simp only [Batch0205.cell1645, Batch0205.tau1645, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010330 (by positivity) using 1 <;> norm_num)
            · have hs1010332 : InSquare (9/64) (-113/320) (1/320) tau := by
                convert childUL hs101033 hx101033 hy101033 using 1 <;> norm_num
              exact Batch0205.cell1646.sound htau (by
                simp only [Batch0205.cell1646, Batch0205.tau1646, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101033 | hy101033
            · have hs1010331 : InSquare (47/320) (-23/64) (1/320) tau := by
                convert childLR hs101033 hx101033 hy101033 using 1 <;> norm_num
              rcases le_total tau.re (47/320 : ℝ) with hx1010331 | hx1010331
              · rcases le_total tau.im (-23/64 : ℝ) with hy1010331 | hy1010331
                · have hs10103310 : InSquare (93/640) (-231/640) (1/640) tau := by
                    convert childLL hs1010331 hx1010331 hy1010331 using 1 <;> norm_num
                  exact Batch0391.cell3129.sound htau (by
                    simp only [Batch0391.cell3129, Batch0391.tau3129, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103310 (by positivity) using 1 <;> norm_num)
                · have hs10103312 : InSquare (93/640) (-229/640) (1/640) tau := by
                    convert childUL hs1010331 hx1010331 hy1010331 using 1 <;> norm_num
                  exact Batch0391.cell3131.sound htau (by
                    simp only [Batch0391.cell3131, Batch0391.tau3131, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy1010331 | hy1010331
                · have hs10103311 : InSquare (19/128) (-231/640) (1/640) tau := by
                    convert childLR hs1010331 hx1010331 hy1010331 using 1 <;> norm_num
                  exact Batch0391.cell3130.sound htau (by
                    simp only [Batch0391.cell3130, Batch0391.tau3130, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103311 (by positivity) using 1 <;> norm_num)
                · have hs10103313 : InSquare (19/128) (-229/640) (1/640) tau := by
                    convert childUR hs1010331 hx1010331 hy1010331 using 1 <;> norm_num
                  exact Batch0391.cell3132.sound htau (by
                    simp only [Batch0391.cell3132, Batch0391.tau3132, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103313 (by positivity) using 1 <;> norm_num)
            · have hs1010333 : InSquare (47/320) (-113/320) (1/320) tau := by
                convert childUR hs101033 hx101033 hy101033 using 1 <;> norm_num
              exact Batch0205.cell1647.sound htau (by
                simp only [Batch0205.cell1647, Batch0205.tau1647, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1010

end


