-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage1102__7
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage1102__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:17:29.769237+00:00
-- url     : https://prove2.me/theorems/fc94e885-2051-4476-b536-b4684160629d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1102 (+6 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1103, GeneralCK.Certific…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1102 (+6 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1103, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1120, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1121, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1122, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1123, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1130)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1102 (+6 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1103, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1120, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1121, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1122, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1123, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1130)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1102 (+6 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1103, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1120, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1121, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1122, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1123, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1130) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1102 (+6 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1103, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1120, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1121, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1122, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1123, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1130).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0217
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0218
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0219
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0220
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0221
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0398
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0399
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0400
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0222
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0080
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0081
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0223
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0224
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0225
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0082
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0226
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0227
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0228
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0229
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0230
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0231
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0083
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0084
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0085
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0086
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0232

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1102 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1102

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_110210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (37/160) (-11/32) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/40)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_110211 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (39/160) (-11/32) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-19/80)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_110213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (39/160) (-53/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-19/80)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1102001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (67/320) (-111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (33/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-33/160)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1102010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (69/320) (-111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-17/80)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1102011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (71/320) (-111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/32)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1102013 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (71/320) (-109/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/32)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1102120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (73/320) (-107/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/40)]
  have himSq : (53/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+53/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1102121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (15/64) (-107/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-37/160)]
  have himSq : (53/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+53/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1102311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (79/320) (-103/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-39/160)]
  have himSq : (51/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+51/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11020000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (129/640) (-223/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/5 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/5)]
  have himSq : (111/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+111/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11020001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (131/640) (-223/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/64)]
  have himSq : (111/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+111/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11020120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (137/640) (-219/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-17/80)]
  have himSq : (109/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+109/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11020121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (139/640) (-219/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (69/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-69/320)]
  have himSq : (109/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+109/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11020123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (139/640) (-217/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (69/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-69/320)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11020311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (143/640) (-43/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (71/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-71/320)]
  have himSq : (107/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+107/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11021230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (149/640) (-211/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-37/160)]
  have himSq : (21/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11021231 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (151/640) (-211/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (15/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-15/64)]
  have himSq : (21/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11021233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (151/640) (-209/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (15/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-15/64)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx1102 | hx1102
  · rcases le_total tau.im (-13/40 : ℝ) with hy1102 | hy1102
    · have hs11020 : InSquare (17/80) (-27/80) (1/80) tau := by
        convert childLL hs hx1102 hy1102 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx11020 | hx11020
      · rcases le_total tau.im (-27/80 : ℝ) with hy11020 | hy11020
        · have hs110200 : InSquare (33/160) (-11/32) (1/160) tau := by
            convert childLL hs11020 hx11020 hy11020 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx110200 | hx110200
          · rcases le_total tau.im (-11/32 : ℝ) with hy110200 | hy110200
            · have hs1102000 : InSquare (13/64) (-111/320) (1/320) tau := by
                convert childLL hs110200 hx110200 hy110200 using 1 <;> norm_num
              rcases le_total tau.re (13/64 : ℝ) with hx1102000 | hx1102000
              · rcases le_total tau.im (-111/320 : ℝ) with hy1102000 | hy1102000
                · have hs11020000 : InSquare (129/640) (-223/640) (1/640) tau := by
                    convert childLL hs1102000 hx1102000 hy1102000 using 1 <;> norm_num
                  exact (outside_11020000 htau hs11020000).elim
                · have hs11020002 : InSquare (129/640) (-221/640) (1/640) tau := by
                    convert childUL hs1102000 hx1102000 hy1102000 using 1 <;> norm_num
                  exact Batch0398.cell3189.sound htau (by
                    simp only [Batch0398.cell3189, Batch0398.tau3189, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-111/320 : ℝ) with hy1102000 | hy1102000
                · have hs11020001 : InSquare (131/640) (-223/640) (1/640) tau := by
                    convert childLR hs1102000 hx1102000 hy1102000 using 1 <;> norm_num
                  exact (outside_11020001 htau hs11020001).elim
                · have hs11020003 : InSquare (131/640) (-221/640) (1/640) tau := by
                    convert childUR hs1102000 hx1102000 hy1102000 using 1 <;> norm_num
                  exact Batch0398.cell3190.sound htau (by
                    simp only [Batch0398.cell3190, Batch0398.tau3190, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020003 (by positivity) using 1 <;> norm_num)
            · have hs1102002 : InSquare (13/64) (-109/320) (1/320) tau := by
                convert childUL hs110200 hx110200 hy110200 using 1 <;> norm_num
              rcases le_total tau.re (13/64 : ℝ) with hx1102002 | hx1102002
              · rcases le_total tau.im (-109/320 : ℝ) with hy1102002 | hy1102002
                · have hs11020020 : InSquare (129/640) (-219/640) (1/640) tau := by
                    convert childLL hs1102002 hx1102002 hy1102002 using 1 <;> norm_num
                  exact Batch0398.cell3191.sound htau (by
                    simp only [Batch0398.cell3191, Batch0398.tau3191, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020020 (by positivity) using 1 <;> norm_num)
                · have hs11020022 : InSquare (129/640) (-217/640) (1/640) tau := by
                    convert childUL hs1102002 hx1102002 hy1102002 using 1 <;> norm_num
                  exact Batch0399.cell3193.sound htau (by
                    simp only [Batch0399.cell3193, Batch0399.tau3193, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-109/320 : ℝ) with hy1102002 | hy1102002
                · have hs11020021 : InSquare (131/640) (-219/640) (1/640) tau := by
                    convert childLR hs1102002 hx1102002 hy1102002 using 1 <;> norm_num
                  exact Batch0399.cell3192.sound htau (by
                    simp only [Batch0399.cell3192, Batch0399.tau3192, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020021 (by positivity) using 1 <;> norm_num)
                · have hs11020023 : InSquare (131/640) (-217/640) (1/640) tau := by
                    convert childUR hs1102002 hx1102002 hy1102002 using 1 <;> norm_num
                  exact Batch0399.cell3194.sound htau (by
                    simp only [Batch0399.cell3194, Batch0399.tau3194, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy110200 | hy110200
            · have hs1102001 : InSquare (67/320) (-111/320) (1/320) tau := by
                convert childLR hs110200 hx110200 hy110200 using 1 <;> norm_num
              exact (outside_1102001 htau hs1102001).elim
            · have hs1102003 : InSquare (67/320) (-109/320) (1/320) tau := by
                convert childUR hs110200 hx110200 hy110200 using 1 <;> norm_num
              rcases le_total tau.re (67/320 : ℝ) with hx1102003 | hx1102003
              · rcases le_total tau.im (-109/320 : ℝ) with hy1102003 | hy1102003
                · have hs11020030 : InSquare (133/640) (-219/640) (1/640) tau := by
                    convert childLL hs1102003 hx1102003 hy1102003 using 1 <;> norm_num
                  exact Batch0399.cell3195.sound htau (by
                    simp only [Batch0399.cell3195, Batch0399.tau3195, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020030 (by positivity) using 1 <;> norm_num)
                · have hs11020032 : InSquare (133/640) (-217/640) (1/640) tau := by
                    convert childUL hs1102003 hx1102003 hy1102003 using 1 <;> norm_num
                  exact Batch0399.cell3197.sound htau (by
                    simp only [Batch0399.cell3197, Batch0399.tau3197, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-109/320 : ℝ) with hy1102003 | hy1102003
                · have hs11020031 : InSquare (27/128) (-219/640) (1/640) tau := by
                    convert childLR hs1102003 hx1102003 hy1102003 using 1 <;> norm_num
                  exact Batch0399.cell3196.sound htau (by
                    simp only [Batch0399.cell3196, Batch0399.tau3196, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020031 (by positivity) using 1 <;> norm_num)
                · have hs11020033 : InSquare (27/128) (-217/640) (1/640) tau := by
                    convert childUR hs1102003 hx1102003 hy1102003 using 1 <;> norm_num
                  exact Batch0399.cell3198.sound htau (by
                    simp only [Batch0399.cell3198, Batch0399.tau3198, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020033 (by positivity) using 1 <;> norm_num)
        · have hs110202 : InSquare (33/160) (-53/160) (1/160) tau := by
            convert childUL hs11020 hx11020 hy11020 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx110202 | hx110202
          · rcases le_total tau.im (-53/160 : ℝ) with hy110202 | hy110202
            · have hs1102020 : InSquare (13/64) (-107/320) (1/320) tau := by
                convert childLL hs110202 hx110202 hy110202 using 1 <;> norm_num
              exact Batch0217.cell1737.sound htau (by
                simp only [Batch0217.cell1737, Batch0217.tau1737, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102020 (by positivity) using 1 <;> norm_num)
            · have hs1102022 : InSquare (13/64) (-21/64) (1/320) tau := by
                convert childUL hs110202 hx110202 hy110202 using 1 <;> norm_num
              exact Batch0217.cell1739.sound htau (by
                simp only [Batch0217.cell1739, Batch0217.tau1739, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy110202 | hy110202
            · have hs1102021 : InSquare (67/320) (-107/320) (1/320) tau := by
                convert childLR hs110202 hx110202 hy110202 using 1 <;> norm_num
              exact Batch0217.cell1738.sound htau (by
                simp only [Batch0217.cell1738, Batch0217.tau1738, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102021 (by positivity) using 1 <;> norm_num)
            · have hs1102023 : InSquare (67/320) (-21/64) (1/320) tau := by
                convert childUR hs110202 hx110202 hy110202 using 1 <;> norm_num
              exact Batch0217.cell1740.sound htau (by
                simp only [Batch0217.cell1740, Batch0217.tau1740, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy11020 | hy11020
        · have hs110201 : InSquare (7/32) (-11/32) (1/160) tau := by
            convert childLR hs11020 hx11020 hy11020 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx110201 | hx110201
          · rcases le_total tau.im (-11/32 : ℝ) with hy110201 | hy110201
            · have hs1102010 : InSquare (69/320) (-111/320) (1/320) tau := by
                convert childLL hs110201 hx110201 hy110201 using 1 <;> norm_num
              exact (outside_1102010 htau hs1102010).elim
            · have hs1102012 : InSquare (69/320) (-109/320) (1/320) tau := by
                convert childUL hs110201 hx110201 hy110201 using 1 <;> norm_num
              rcases le_total tau.re (69/320 : ℝ) with hx1102012 | hx1102012
              · rcases le_total tau.im (-109/320 : ℝ) with hy1102012 | hy1102012
                · have hs11020120 : InSquare (137/640) (-219/640) (1/640) tau := by
                    convert childLL hs1102012 hx1102012 hy1102012 using 1 <;> norm_num
                  exact (outside_11020120 htau hs11020120).elim
                · have hs11020122 : InSquare (137/640) (-217/640) (1/640) tau := by
                    convert childUL hs1102012 hx1102012 hy1102012 using 1 <;> norm_num
                  exact Batch0399.cell3199.sound htau (by
                    simp only [Batch0399.cell3199, Batch0399.tau3199, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-109/320 : ℝ) with hy1102012 | hy1102012
                · have hs11020121 : InSquare (139/640) (-219/640) (1/640) tau := by
                    convert childLR hs1102012 hx1102012 hy1102012 using 1 <;> norm_num
                  exact (outside_11020121 htau hs11020121).elim
                · have hs11020123 : InSquare (139/640) (-217/640) (1/640) tau := by
                    convert childUR hs1102012 hx1102012 hy1102012 using 1 <;> norm_num
                  exact (outside_11020123 htau hs11020123).elim
          · rcases le_total tau.im (-11/32 : ℝ) with hy110201 | hy110201
            · have hs1102011 : InSquare (71/320) (-111/320) (1/320) tau := by
                convert childLR hs110201 hx110201 hy110201 using 1 <;> norm_num
              exact (outside_1102011 htau hs1102011).elim
            · have hs1102013 : InSquare (71/320) (-109/320) (1/320) tau := by
                convert childUR hs110201 hx110201 hy110201 using 1 <;> norm_num
              exact (outside_1102013 htau hs1102013).elim
        · have hs110203 : InSquare (7/32) (-53/160) (1/160) tau := by
            convert childUR hs11020 hx11020 hy11020 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx110203 | hx110203
          · rcases le_total tau.im (-53/160 : ℝ) with hy110203 | hy110203
            · have hs1102030 : InSquare (69/320) (-107/320) (1/320) tau := by
                convert childLL hs110203 hx110203 hy110203 using 1 <;> norm_num
              exact Batch0217.cell1741.sound htau (by
                simp only [Batch0217.cell1741, Batch0217.tau1741, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102030 (by positivity) using 1 <;> norm_num)
            · have hs1102032 : InSquare (69/320) (-21/64) (1/320) tau := by
                convert childUL hs110203 hx110203 hy110203 using 1 <;> norm_num
              exact Batch0217.cell1742.sound htau (by
                simp only [Batch0217.cell1742, Batch0217.tau1742, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy110203 | hy110203
            · have hs1102031 : InSquare (71/320) (-107/320) (1/320) tau := by
                convert childLR hs110203 hx110203 hy110203 using 1 <;> norm_num
              rcases le_total tau.re (71/320 : ℝ) with hx1102031 | hx1102031
              · rcases le_total tau.im (-107/320 : ℝ) with hy1102031 | hy1102031
                · have hs11020310 : InSquare (141/640) (-43/128) (1/640) tau := by
                    convert childLL hs1102031 hx1102031 hy1102031 using 1 <;> norm_num
                  exact Batch0400.cell3200.sound htau (by
                    simp only [Batch0400.cell3200, Batch0400.tau3200, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020310 (by positivity) using 1 <;> norm_num)
                · have hs11020312 : InSquare (141/640) (-213/640) (1/640) tau := by
                    convert childUL hs1102031 hx1102031 hy1102031 using 1 <;> norm_num
                  exact Batch0400.cell3201.sound htau (by
                    simp only [Batch0400.cell3201, Batch0400.tau3201, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-107/320 : ℝ) with hy1102031 | hy1102031
                · have hs11020311 : InSquare (143/640) (-43/128) (1/640) tau := by
                    convert childLR hs1102031 hx1102031 hy1102031 using 1 <;> norm_num
                  exact (outside_11020311 htau hs11020311).elim
                · have hs11020313 : InSquare (143/640) (-213/640) (1/640) tau := by
                    convert childUR hs1102031 hx1102031 hy1102031 using 1 <;> norm_num
                  exact Batch0400.cell3202.sound htau (by
                    simp only [Batch0400.cell3202, Batch0400.tau3202, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020313 (by positivity) using 1 <;> norm_num)
            · have hs1102033 : InSquare (71/320) (-21/64) (1/320) tau := by
                convert childUR hs110203 hx110203 hy110203 using 1 <;> norm_num
              exact Batch0217.cell1743.sound htau (by
                simp only [Batch0217.cell1743, Batch0217.tau1743, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102033 (by positivity) using 1 <;> norm_num)
    · have hs11022 : InSquare (17/80) (-5/16) (1/80) tau := by
        convert childUL hs hx1102 hy1102 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx11022 | hx11022
      · rcases le_total tau.im (-5/16 : ℝ) with hy11022 | hy11022
        · have hs110220 : InSquare (33/160) (-51/160) (1/160) tau := by
            convert childLL hs11022 hx11022 hy11022 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx110220 | hx110220
          · rcases le_total tau.im (-51/160 : ℝ) with hy110220 | hy110220
            · have hs1102200 : InSquare (13/64) (-103/320) (1/320) tau := by
                convert childLL hs110220 hx110220 hy110220 using 1 <;> norm_num
              exact Batch0218.cell1745.sound htau (by
                simp only [Batch0218.cell1745, Batch0218.tau1745, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102200 (by positivity) using 1 <;> norm_num)
            · have hs1102202 : InSquare (13/64) (-101/320) (1/320) tau := by
                convert childUL hs110220 hx110220 hy110220 using 1 <;> norm_num
              exact Batch0218.cell1747.sound htau (by
                simp only [Batch0218.cell1747, Batch0218.tau1747, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy110220 | hy110220
            · have hs1102201 : InSquare (67/320) (-103/320) (1/320) tau := by
                convert childLR hs110220 hx110220 hy110220 using 1 <;> norm_num
              exact Batch0218.cell1746.sound htau (by
                simp only [Batch0218.cell1746, Batch0218.tau1746, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102201 (by positivity) using 1 <;> norm_num)
            · have hs1102203 : InSquare (67/320) (-101/320) (1/320) tau := by
                convert childUR hs110220 hx110220 hy110220 using 1 <;> norm_num
              exact Batch0218.cell1748.sound htau (by
                simp only [Batch0218.cell1748, Batch0218.tau1748, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102203 (by positivity) using 1 <;> norm_num)
        · have hs110222 : InSquare (33/160) (-49/160) (1/160) tau := by
            convert childUL hs11022 hx11022 hy11022 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx110222 | hx110222
          · rcases le_total tau.im (-49/160 : ℝ) with hy110222 | hy110222
            · have hs1102220 : InSquare (13/64) (-99/320) (1/320) tau := by
                convert childLL hs110222 hx110222 hy110222 using 1 <;> norm_num
              exact Batch0219.cell1753.sound htau (by
                simp only [Batch0219.cell1753, Batch0219.tau1753, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102220 (by positivity) using 1 <;> norm_num)
            · have hs1102222 : InSquare (13/64) (-97/320) (1/320) tau := by
                convert childUL hs110222 hx110222 hy110222 using 1 <;> norm_num
              exact Batch0219.cell1755.sound htau (by
                simp only [Batch0219.cell1755, Batch0219.tau1755, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy110222 | hy110222
            · have hs1102221 : InSquare (67/320) (-99/320) (1/320) tau := by
                convert childLR hs110222 hx110222 hy110222 using 1 <;> norm_num
              exact Batch0219.cell1754.sound htau (by
                simp only [Batch0219.cell1754, Batch0219.tau1754, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102221 (by positivity) using 1 <;> norm_num)
            · have hs1102223 : InSquare (67/320) (-97/320) (1/320) tau := by
                convert childUR hs110222 hx110222 hy110222 using 1 <;> norm_num
              exact Batch0219.cell1756.sound htau (by
                simp only [Batch0219.cell1756, Batch0219.tau1756, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy11022 | hy11022
        · have hs110221 : InSquare (7/32) (-51/160) (1/160) tau := by
            convert childLR hs11022 hx11022 hy11022 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx110221 | hx110221
          · rcases le_total tau.im (-51/160 : ℝ) with hy110221 | hy110221
            · have hs1102210 : InSquare (69/320) (-103/320) (1/320) tau := by
                convert childLL hs110221 hx110221 hy110221 using 1 <;> norm_num
              exact Batch0218.cell1749.sound htau (by
                simp only [Batch0218.cell1749, Batch0218.tau1749, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102210 (by positivity) using 1 <;> norm_num)
            · have hs1102212 : InSquare (69/320) (-101/320) (1/320) tau := by
                convert childUL hs110221 hx110221 hy110221 using 1 <;> norm_num
              exact Batch0218.cell1751.sound htau (by
                simp only [Batch0218.cell1751, Batch0218.tau1751, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy110221 | hy110221
            · have hs1102211 : InSquare (71/320) (-103/320) (1/320) tau := by
                convert childLR hs110221 hx110221 hy110221 using 1 <;> norm_num
              exact Batch0218.cell1750.sound htau (by
                simp only [Batch0218.cell1750, Batch0218.tau1750, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102211 (by positivity) using 1 <;> norm_num)
            · have hs1102213 : InSquare (71/320) (-101/320) (1/320) tau := by
                convert childUR hs110221 hx110221 hy110221 using 1 <;> norm_num
              exact Batch0219.cell1752.sound htau (by
                simp only [Batch0219.cell1752, Batch0219.tau1752, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102213 (by positivity) using 1 <;> norm_num)
        · have hs110223 : InSquare (7/32) (-49/160) (1/160) tau := by
            convert childUR hs11022 hx11022 hy11022 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx110223 | hx110223
          · rcases le_total tau.im (-49/160 : ℝ) with hy110223 | hy110223
            · have hs1102230 : InSquare (69/320) (-99/320) (1/320) tau := by
                convert childLL hs110223 hx110223 hy110223 using 1 <;> norm_num
              exact Batch0219.cell1757.sound htau (by
                simp only [Batch0219.cell1757, Batch0219.tau1757, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102230 (by positivity) using 1 <;> norm_num)
            · have hs1102232 : InSquare (69/320) (-97/320) (1/320) tau := by
                convert childUL hs110223 hx110223 hy110223 using 1 <;> norm_num
              exact Batch0219.cell1759.sound htau (by
                simp only [Batch0219.cell1759, Batch0219.tau1759, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy110223 | hy110223
            · have hs1102231 : InSquare (71/320) (-99/320) (1/320) tau := by
                convert childLR hs110223 hx110223 hy110223 using 1 <;> norm_num
              exact Batch0219.cell1758.sound htau (by
                simp only [Batch0219.cell1758, Batch0219.tau1758, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102231 (by positivity) using 1 <;> norm_num)
            · have hs1102233 : InSquare (71/320) (-97/320) (1/320) tau := by
                convert childUR hs110223 hx110223 hy110223 using 1 <;> norm_num
              exact Batch0220.cell1760.sound htau (by
                simp only [Batch0220.cell1760, Batch0220.tau1760, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy1102 | hy1102
    · have hs11021 : InSquare (19/80) (-27/80) (1/80) tau := by
        convert childLR hs hx1102 hy1102 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx11021 | hx11021
      · rcases le_total tau.im (-27/80 : ℝ) with hy11021 | hy11021
        · have hs110210 : InSquare (37/160) (-11/32) (1/160) tau := by
            convert childLL hs11021 hx11021 hy11021 using 1 <;> norm_num
          exact (outside_110210 htau hs110210).elim
        · have hs110212 : InSquare (37/160) (-53/160) (1/160) tau := by
            convert childUL hs11021 hx11021 hy11021 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx110212 | hx110212
          · rcases le_total tau.im (-53/160 : ℝ) with hy110212 | hy110212
            · have hs1102120 : InSquare (73/320) (-107/320) (1/320) tau := by
                convert childLL hs110212 hx110212 hy110212 using 1 <;> norm_num
              exact (outside_1102120 htau hs1102120).elim
            · have hs1102122 : InSquare (73/320) (-21/64) (1/320) tau := by
                convert childUL hs110212 hx110212 hy110212 using 1 <;> norm_num
              exact Batch0218.cell1744.sound htau (by
                simp only [Batch0218.cell1744, Batch0218.tau1744, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy110212 | hy110212
            · have hs1102121 : InSquare (15/64) (-107/320) (1/320) tau := by
                convert childLR hs110212 hx110212 hy110212 using 1 <;> norm_num
              exact (outside_1102121 htau hs1102121).elim
            · have hs1102123 : InSquare (15/64) (-21/64) (1/320) tau := by
                convert childUR hs110212 hx110212 hy110212 using 1 <;> norm_num
              rcases le_total tau.re (15/64 : ℝ) with hx1102123 | hx1102123
              · rcases le_total tau.im (-21/64 : ℝ) with hy1102123 | hy1102123
                · have hs11021230 : InSquare (149/640) (-211/640) (1/640) tau := by
                    convert childLL hs1102123 hx1102123 hy1102123 using 1 <;> norm_num
                  exact (outside_11021230 htau hs11021230).elim
                · have hs11021232 : InSquare (149/640) (-209/640) (1/640) tau := by
                    convert childUL hs1102123 hx1102123 hy1102123 using 1 <;> norm_num
                  exact Batch0400.cell3203.sound htau (by
                    simp only [Batch0400.cell3203, Batch0400.tau3203, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11021232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-21/64 : ℝ) with hy1102123 | hy1102123
                · have hs11021231 : InSquare (151/640) (-211/640) (1/640) tau := by
                    convert childLR hs1102123 hx1102123 hy1102123 using 1 <;> norm_num
                  exact (outside_11021231 htau hs11021231).elim
                · have hs11021233 : InSquare (151/640) (-209/640) (1/640) tau := by
                    convert childUR hs1102123 hx1102123 hy1102123 using 1 <;> norm_num
                  exact (outside_11021233 htau hs11021233).elim
      · rcases le_total tau.im (-27/80 : ℝ) with hy11021 | hy11021
        · have hs110211 : InSquare (39/160) (-11/32) (1/160) tau := by
            convert childLR hs11021 hx11021 hy11021 using 1 <;> norm_num
          exact (outside_110211 htau hs110211).elim
        · have hs110213 : InSquare (39/160) (-53/160) (1/160) tau := by
            convert childUR hs11021 hx11021 hy11021 using 1 <;> norm_num
          exact (outside_110213 htau hs110213).elim
    · have hs11023 : InSquare (19/80) (-5/16) (1/80) tau := by
        convert childUR hs hx1102 hy1102 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx11023 | hx11023
      · rcases le_total tau.im (-5/16 : ℝ) with hy11023 | hy11023
        · have hs110230 : InSquare (37/160) (-51/160) (1/160) tau := by
            convert childLL hs11023 hx11023 hy11023 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx110230 | hx110230
          · rcases le_total tau.im (-51/160 : ℝ) with hy110230 | hy110230
            · have hs1102300 : InSquare (73/320) (-103/320) (1/320) tau := by
                convert childLL hs110230 hx110230 hy110230 using 1 <;> norm_num
              exact Batch0220.cell1761.sound htau (by
                simp only [Batch0220.cell1761, Batch0220.tau1761, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102300 (by positivity) using 1 <;> norm_num)
            · have hs1102302 : InSquare (73/320) (-101/320) (1/320) tau := by
                convert childUL hs110230 hx110230 hy110230 using 1 <;> norm_num
              exact Batch0220.cell1763.sound htau (by
                simp only [Batch0220.cell1763, Batch0220.tau1763, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy110230 | hy110230
            · have hs1102301 : InSquare (15/64) (-103/320) (1/320) tau := by
                convert childLR hs110230 hx110230 hy110230 using 1 <;> norm_num
              exact Batch0220.cell1762.sound htau (by
                simp only [Batch0220.cell1762, Batch0220.tau1762, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102301 (by positivity) using 1 <;> norm_num)
            · have hs1102303 : InSquare (15/64) (-101/320) (1/320) tau := by
                convert childUR hs110230 hx110230 hy110230 using 1 <;> norm_num
              exact Batch0220.cell1764.sound htau (by
                simp only [Batch0220.cell1764, Batch0220.tau1764, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102303 (by positivity) using 1 <;> norm_num)
        · have hs110232 : InSquare (37/160) (-49/160) (1/160) tau := by
            convert childUL hs11023 hx11023 hy11023 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx110232 | hx110232
          · rcases le_total tau.im (-49/160 : ℝ) with hy110232 | hy110232
            · have hs1102320 : InSquare (73/320) (-99/320) (1/320) tau := by
                convert childLL hs110232 hx110232 hy110232 using 1 <;> norm_num
              exact Batch0221.cell1768.sound htau (by
                simp only [Batch0221.cell1768, Batch0221.tau1768, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102320 (by positivity) using 1 <;> norm_num)
            · have hs1102322 : InSquare (73/320) (-97/320) (1/320) tau := by
                convert childUL hs110232 hx110232 hy110232 using 1 <;> norm_num
              exact Batch0221.cell1770.sound htau (by
                simp only [Batch0221.cell1770, Batch0221.tau1770, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy110232 | hy110232
            · have hs1102321 : InSquare (15/64) (-99/320) (1/320) tau := by
                convert childLR hs110232 hx110232 hy110232 using 1 <;> norm_num
              exact Batch0221.cell1769.sound htau (by
                simp only [Batch0221.cell1769, Batch0221.tau1769, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102321 (by positivity) using 1 <;> norm_num)
            · have hs1102323 : InSquare (15/64) (-97/320) (1/320) tau := by
                convert childUR hs110232 hx110232 hy110232 using 1 <;> norm_num
              exact Batch0221.cell1771.sound htau (by
                simp only [Batch0221.cell1771, Batch0221.tau1771, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy11023 | hy11023
        · have hs110231 : InSquare (39/160) (-51/160) (1/160) tau := by
            convert childLR hs11023 hx11023 hy11023 using 1 <;> norm_num
          rcases le_total tau.re (39/160 : ℝ) with hx110231 | hx110231
          · rcases le_total tau.im (-51/160 : ℝ) with hy110231 | hy110231
            · have hs1102310 : InSquare (77/320) (-103/320) (1/320) tau := by
                convert childLL hs110231 hx110231 hy110231 using 1 <;> norm_num
              exact Batch0220.cell1765.sound htau (by
                simp only [Batch0220.cell1765, Batch0220.tau1765, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102310 (by positivity) using 1 <;> norm_num)
            · have hs1102312 : InSquare (77/320) (-101/320) (1/320) tau := by
                convert childUL hs110231 hx110231 hy110231 using 1 <;> norm_num
              exact Batch0220.cell1766.sound htau (by
                simp only [Batch0220.cell1766, Batch0220.tau1766, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy110231 | hy110231
            · have hs1102311 : InSquare (79/320) (-103/320) (1/320) tau := by
                convert childLR hs110231 hx110231 hy110231 using 1 <;> norm_num
              exact (outside_1102311 htau hs1102311).elim
            · have hs1102313 : InSquare (79/320) (-101/320) (1/320) tau := by
                convert childUR hs110231 hx110231 hy110231 using 1 <;> norm_num
              exact Batch0220.cell1767.sound htau (by
                simp only [Batch0220.cell1767, Batch0220.tau1767, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102313 (by positivity) using 1 <;> norm_num)
        · have hs110233 : InSquare (39/160) (-49/160) (1/160) tau := by
            convert childUR hs11023 hx11023 hy11023 using 1 <;> norm_num
          rcases le_total tau.re (39/160 : ℝ) with hx110233 | hx110233
          · rcases le_total tau.im (-49/160 : ℝ) with hy110233 | hy110233
            · have hs1102330 : InSquare (77/320) (-99/320) (1/320) tau := by
                convert childLL hs110233 hx110233 hy110233 using 1 <;> norm_num
              exact Batch0221.cell1772.sound htau (by
                simp only [Batch0221.cell1772, Batch0221.tau1772, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102330 (by positivity) using 1 <;> norm_num)
            · have hs1102332 : InSquare (77/320) (-97/320) (1/320) tau := by
                convert childUL hs110233 hx110233 hy110233 using 1 <;> norm_num
              exact Batch0221.cell1774.sound htau (by
                simp only [Batch0221.cell1774, Batch0221.tau1774, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy110233 | hy110233
            · have hs1102331 : InSquare (79/320) (-99/320) (1/320) tau := by
                convert childLR hs110233 hx110233 hy110233 using 1 <;> norm_num
              exact Batch0221.cell1773.sound htau (by
                simp only [Batch0221.cell1773, Batch0221.tau1773, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102331 (by positivity) using 1 <;> norm_num)
            · have hs1102333 : InSquare (79/320) (-97/320) (1/320) tau := by
                convert childUR hs110233 hx110233 hy110233 using 1 <;> norm_num
              exact Batch0221.cell1775.sound htau (by
                simp only [Batch0221.cell1775, Batch0221.tau1775, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1102

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1103 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1103

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_11030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (21/80) (-27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/4)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/80) (-27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/40)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11033 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/80) (-5/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/40)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_110320 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (41/160) (-51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/4)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_110321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (43/160) (-51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/80)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1103230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (17/64) (-99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/80)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1103231 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (87/320) (-99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-43/160)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1103233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (87/320) (-97/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-43/160)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx1103 | hx1103
  · rcases le_total tau.im (-13/40 : ℝ) with hy1103 | hy1103
    · have hs11030 : InSquare (21/80) (-27/80) (1/80) tau := by
        convert childLL hs hx1103 hy1103 using 1 <;> norm_num
      exact (outside_11030 htau hs11030).elim
    · have hs11032 : InSquare (21/80) (-5/16) (1/80) tau := by
        convert childUL hs hx1103 hy1103 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx11032 | hx11032
      · rcases le_total tau.im (-5/16 : ℝ) with hy11032 | hy11032
        · have hs110320 : InSquare (41/160) (-51/160) (1/160) tau := by
            convert childLL hs11032 hx11032 hy11032 using 1 <;> norm_num
          exact (outside_110320 htau hs110320).elim
        · have hs110322 : InSquare (41/160) (-49/160) (1/160) tau := by
            convert childUL hs11032 hx11032 hy11032 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx110322 | hx110322
          · rcases le_total tau.im (-49/160 : ℝ) with hy110322 | hy110322
            · have hs1103220 : InSquare (81/320) (-99/320) (1/320) tau := by
                convert childLL hs110322 hx110322 hy110322 using 1 <;> norm_num
              exact Batch0222.cell1776.sound htau (by
                simp only [Batch0222.cell1776, Batch0222.tau1776, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1103220 (by positivity) using 1 <;> norm_num)
            · have hs1103222 : InSquare (81/320) (-97/320) (1/320) tau := by
                convert childUL hs110322 hx110322 hy110322 using 1 <;> norm_num
              exact Batch0222.cell1778.sound htau (by
                simp only [Batch0222.cell1778, Batch0222.tau1778, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1103222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy110322 | hy110322
            · have hs1103221 : InSquare (83/320) (-99/320) (1/320) tau := by
                convert childLR hs110322 hx110322 hy110322 using 1 <;> norm_num
              exact Batch0222.cell1777.sound htau (by
                simp only [Batch0222.cell1777, Batch0222.tau1777, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1103221 (by positivity) using 1 <;> norm_num)
            · have hs1103223 : InSquare (83/320) (-97/320) (1/320) tau := by
                convert childUR hs110322 hx110322 hy110322 using 1 <;> norm_num
              exact Batch0222.cell1779.sound htau (by
                simp only [Batch0222.cell1779, Batch0222.tau1779, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1103223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy11032 | hy11032
        · have hs110321 : InSquare (43/160) (-51/160) (1/160) tau := by
            convert childLR hs11032 hx11032 hy11032 using 1 <;> norm_num
          exact (outside_110321 htau hs110321).elim
        · have hs110323 : InSquare (43/160) (-49/160) (1/160) tau := by
            convert childUR hs11032 hx11032 hy11032 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx110323 | hx110323
          · rcases le_total tau.im (-49/160 : ℝ) with hy110323 | hy110323
            · have hs1103230 : InSquare (17/64) (-99/320) (1/320) tau := by
                convert childLL hs110323 hx110323 hy110323 using 1 <;> norm_num
              exact (outside_1103230 htau hs1103230).elim
            · have hs1103232 : InSquare (17/64) (-97/320) (1/320) tau := by
                convert childUL hs110323 hx110323 hy110323 using 1 <;> norm_num
              exact Batch0222.cell1780.sound htau (by
                simp only [Batch0222.cell1780, Batch0222.tau1780, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1103232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy110323 | hy110323
            · have hs1103231 : InSquare (87/320) (-99/320) (1/320) tau := by
                convert childLR hs110323 hx110323 hy110323 using 1 <;> norm_num
              exact (outside_1103231 htau hs1103231).elim
            · have hs1103233 : InSquare (87/320) (-97/320) (1/320) tau := by
                convert childUR hs110323 hx110323 hy110323 using 1 <;> norm_num
              exact (outside_1103233 htau hs1103233).elim
  · rcases le_total tau.im (-13/40 : ℝ) with hy1103 | hy1103
    · have hs11031 : InSquare (23/80) (-27/80) (1/80) tau := by
        convert childLR hs hx1103 hy1103 using 1 <;> norm_num
      exact (outside_11031 htau hs11031).elim
    · have hs11033 : InSquare (23/80) (-5/16) (1/80) tau := by
        convert childUR hs hx1103 hy1103 using 1 <;> norm_num
      exact (outside_11033 htau hs11033).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1103

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1120 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1120

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx1120 | hx1120
  · rcases le_total tau.im (-11/40 : ℝ) with hy1120 | hy1120
    · have hs11200 : InSquare (17/80) (-23/80) (1/80) tau := by
        convert childLL hs hx1120 hy1120 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx11200 | hx11200
      · rcases le_total tau.im (-23/80 : ℝ) with hy11200 | hy11200
        · have hs112000 : InSquare (33/160) (-47/160) (1/160) tau := by
            convert childLL hs11200 hx11200 hy11200 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx112000 | hx112000
          · rcases le_total tau.im (-47/160 : ℝ) with hy112000 | hy112000
            · have hs1120000 : InSquare (13/64) (-19/64) (1/320) tau := by
                convert childLL hs112000 hx112000 hy112000 using 1 <;> norm_num
              exact Batch0222.cell1781.sound htau (by
                simp only [Batch0222.cell1781, Batch0222.tau1781, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120000 (by positivity) using 1 <;> norm_num)
            · have hs1120002 : InSquare (13/64) (-93/320) (1/320) tau := by
                convert childUL hs112000 hx112000 hy112000 using 1 <;> norm_num
              exact Batch0222.cell1783.sound htau (by
                simp only [Batch0222.cell1783, Batch0222.tau1783, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy112000 | hy112000
            · have hs1120001 : InSquare (67/320) (-19/64) (1/320) tau := by
                convert childLR hs112000 hx112000 hy112000 using 1 <;> norm_num
              exact Batch0222.cell1782.sound htau (by
                simp only [Batch0222.cell1782, Batch0222.tau1782, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120001 (by positivity) using 1 <;> norm_num)
            · have hs1120003 : InSquare (67/320) (-93/320) (1/320) tau := by
                convert childUR hs112000 hx112000 hy112000 using 1 <;> norm_num
              exact Batch0223.cell1784.sound htau (by
                simp only [Batch0223.cell1784, Batch0223.tau1784, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120003 (by positivity) using 1 <;> norm_num)
        · have hs112002 : InSquare (33/160) (-9/32) (1/160) tau := by
            convert childUL hs11200 hx11200 hy11200 using 1 <;> norm_num
          exact Batch0080.cell0646.sound htau (by
            simp only [Batch0080.cell0646, Batch0080.tau0646, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy11200 | hy11200
        · have hs112001 : InSquare (7/32) (-47/160) (1/160) tau := by
            convert childLR hs11200 hx11200 hy11200 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx112001 | hx112001
          · rcases le_total tau.im (-47/160 : ℝ) with hy112001 | hy112001
            · have hs1120010 : InSquare (69/320) (-19/64) (1/320) tau := by
                convert childLL hs112001 hx112001 hy112001 using 1 <;> norm_num
              exact Batch0223.cell1785.sound htau (by
                simp only [Batch0223.cell1785, Batch0223.tau1785, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120010 (by positivity) using 1 <;> norm_num)
            · have hs1120012 : InSquare (69/320) (-93/320) (1/320) tau := by
                convert childUL hs112001 hx112001 hy112001 using 1 <;> norm_num
              exact Batch0223.cell1787.sound htau (by
                simp only [Batch0223.cell1787, Batch0223.tau1787, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy112001 | hy112001
            · have hs1120011 : InSquare (71/320) (-19/64) (1/320) tau := by
                convert childLR hs112001 hx112001 hy112001 using 1 <;> norm_num
              exact Batch0223.cell1786.sound htau (by
                simp only [Batch0223.cell1786, Batch0223.tau1786, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120011 (by positivity) using 1 <;> norm_num)
            · have hs1120013 : InSquare (71/320) (-93/320) (1/320) tau := by
                convert childUR hs112001 hx112001 hy112001 using 1 <;> norm_num
              exact Batch0223.cell1788.sound htau (by
                simp only [Batch0223.cell1788, Batch0223.tau1788, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120013 (by positivity) using 1 <;> norm_num)
        · have hs112003 : InSquare (7/32) (-9/32) (1/160) tau := by
            convert childUR hs11200 hx11200 hy11200 using 1 <;> norm_num
          exact Batch0080.cell0647.sound htau (by
            simp only [Batch0080.cell0647, Batch0080.tau0647, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112003 (by positivity) using 1 <;> norm_num)
    · have hs11202 : InSquare (17/80) (-21/80) (1/80) tau := by
        convert childUL hs hx1120 hy1120 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx11202 | hx11202
      · rcases le_total tau.im (-21/80 : ℝ) with hy11202 | hy11202
        · have hs112020 : InSquare (33/160) (-43/160) (1/160) tau := by
            convert childLL hs11202 hx11202 hy11202 using 1 <;> norm_num
          exact Batch0081.cell0648.sound htau (by
            simp only [Batch0081.cell0648, Batch0081.tau0648, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112020 (by positivity) using 1 <;> norm_num)
        · have hs112022 : InSquare (33/160) (-41/160) (1/160) tau := by
            convert childUL hs11202 hx11202 hy11202 using 1 <;> norm_num
          exact Batch0081.cell0650.sound htau (by
            simp only [Batch0081.cell0650, Batch0081.tau0650, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy11202 | hy11202
        · have hs112021 : InSquare (7/32) (-43/160) (1/160) tau := by
            convert childLR hs11202 hx11202 hy11202 using 1 <;> norm_num
          exact Batch0081.cell0649.sound htau (by
            simp only [Batch0081.cell0649, Batch0081.tau0649, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112021 (by positivity) using 1 <;> norm_num)
        · have hs112023 : InSquare (7/32) (-41/160) (1/160) tau := by
            convert childUR hs11202 hx11202 hy11202 using 1 <;> norm_num
          exact Batch0081.cell0651.sound htau (by
            simp only [Batch0081.cell0651, Batch0081.tau0651, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy1120 | hy1120
    · have hs11201 : InSquare (19/80) (-23/80) (1/80) tau := by
        convert childLR hs hx1120 hy1120 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx11201 | hx11201
      · rcases le_total tau.im (-23/80 : ℝ) with hy11201 | hy11201
        · have hs112010 : InSquare (37/160) (-47/160) (1/160) tau := by
            convert childLL hs11201 hx11201 hy11201 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx112010 | hx112010
          · rcases le_total tau.im (-47/160 : ℝ) with hy112010 | hy112010
            · have hs1120100 : InSquare (73/320) (-19/64) (1/320) tau := by
                convert childLL hs112010 hx112010 hy112010 using 1 <;> norm_num
              exact Batch0223.cell1789.sound htau (by
                simp only [Batch0223.cell1789, Batch0223.tau1789, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120100 (by positivity) using 1 <;> norm_num)
            · have hs1120102 : InSquare (73/320) (-93/320) (1/320) tau := by
                convert childUL hs112010 hx112010 hy112010 using 1 <;> norm_num
              exact Batch0223.cell1791.sound htau (by
                simp only [Batch0223.cell1791, Batch0223.tau1791, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy112010 | hy112010
            · have hs1120101 : InSquare (15/64) (-19/64) (1/320) tau := by
                convert childLR hs112010 hx112010 hy112010 using 1 <;> norm_num
              exact Batch0223.cell1790.sound htau (by
                simp only [Batch0223.cell1790, Batch0223.tau1790, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120101 (by positivity) using 1 <;> norm_num)
            · have hs1120103 : InSquare (15/64) (-93/320) (1/320) tau := by
                convert childUR hs112010 hx112010 hy112010 using 1 <;> norm_num
              exact Batch0224.cell1792.sound htau (by
                simp only [Batch0224.cell1792, Batch0224.tau1792, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120103 (by positivity) using 1 <;> norm_num)
        · have hs112012 : InSquare (37/160) (-9/32) (1/160) tau := by
            convert childUL hs11201 hx11201 hy11201 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx112012 | hx112012
          · rcases le_total tau.im (-9/32 : ℝ) with hy112012 | hy112012
            · have hs1120120 : InSquare (73/320) (-91/320) (1/320) tau := by
                convert childLL hs112012 hx112012 hy112012 using 1 <;> norm_num
              exact Batch0224.cell1797.sound htau (by
                simp only [Batch0224.cell1797, Batch0224.tau1797, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120120 (by positivity) using 1 <;> norm_num)
            · have hs1120122 : InSquare (73/320) (-89/320) (1/320) tau := by
                convert childUL hs112012 hx112012 hy112012 using 1 <;> norm_num
              exact Batch0224.cell1799.sound htau (by
                simp only [Batch0224.cell1799, Batch0224.tau1799, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy112012 | hy112012
            · have hs1120121 : InSquare (15/64) (-91/320) (1/320) tau := by
                convert childLR hs112012 hx112012 hy112012 using 1 <;> norm_num
              exact Batch0224.cell1798.sound htau (by
                simp only [Batch0224.cell1798, Batch0224.tau1798, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120121 (by positivity) using 1 <;> norm_num)
            · have hs1120123 : InSquare (15/64) (-89/320) (1/320) tau := by
                convert childUR hs112012 hx112012 hy112012 using 1 <;> norm_num
              exact Batch0225.cell1800.sound htau (by
                simp only [Batch0225.cell1800, Batch0225.tau1800, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy11201 | hy11201
        · have hs112011 : InSquare (39/160) (-47/160) (1/160) tau := by
            convert childLR hs11201 hx11201 hy11201 using 1 <;> norm_num
          rcases le_total tau.re (39/160 : ℝ) with hx112011 | hx112011
          · rcases le_total tau.im (-47/160 : ℝ) with hy112011 | hy112011
            · have hs1120110 : InSquare (77/320) (-19/64) (1/320) tau := by
                convert childLL hs112011 hx112011 hy112011 using 1 <;> norm_num
              exact Batch0224.cell1793.sound htau (by
                simp only [Batch0224.cell1793, Batch0224.tau1793, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120110 (by positivity) using 1 <;> norm_num)
            · have hs1120112 : InSquare (77/320) (-93/320) (1/320) tau := by
                convert childUL hs112011 hx112011 hy112011 using 1 <;> norm_num
              exact Batch0224.cell1795.sound htau (by
                simp only [Batch0224.cell1795, Batch0224.tau1795, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy112011 | hy112011
            · have hs1120111 : InSquare (79/320) (-19/64) (1/320) tau := by
                convert childLR hs112011 hx112011 hy112011 using 1 <;> norm_num
              exact Batch0224.cell1794.sound htau (by
                simp only [Batch0224.cell1794, Batch0224.tau1794, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120111 (by positivity) using 1 <;> norm_num)
            · have hs1120113 : InSquare (79/320) (-93/320) (1/320) tau := by
                convert childUR hs112011 hx112011 hy112011 using 1 <;> norm_num
              exact Batch0224.cell1796.sound htau (by
                simp only [Batch0224.cell1796, Batch0224.tau1796, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120113 (by positivity) using 1 <;> norm_num)
        · have hs112013 : InSquare (39/160) (-9/32) (1/160) tau := by
            convert childUR hs11201 hx11201 hy11201 using 1 <;> norm_num
          rcases le_total tau.re (39/160 : ℝ) with hx112013 | hx112013
          · rcases le_total tau.im (-9/32 : ℝ) with hy112013 | hy112013
            · have hs1120130 : InSquare (77/320) (-91/320) (1/320) tau := by
                convert childLL hs112013 hx112013 hy112013 using 1 <;> norm_num
              exact Batch0225.cell1801.sound htau (by
                simp only [Batch0225.cell1801, Batch0225.tau1801, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120130 (by positivity) using 1 <;> norm_num)
            · have hs1120132 : InSquare (77/320) (-89/320) (1/320) tau := by
                convert childUL hs112013 hx112013 hy112013 using 1 <;> norm_num
              exact Batch0225.cell1803.sound htau (by
                simp only [Batch0225.cell1803, Batch0225.tau1803, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy112013 | hy112013
            · have hs1120131 : InSquare (79/320) (-91/320) (1/320) tau := by
                convert childLR hs112013 hx112013 hy112013 using 1 <;> norm_num
              exact Batch0225.cell1802.sound htau (by
                simp only [Batch0225.cell1802, Batch0225.tau1802, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120131 (by positivity) using 1 <;> norm_num)
            · have hs1120133 : InSquare (79/320) (-89/320) (1/320) tau := by
                convert childUR hs112013 hx112013 hy112013 using 1 <;> norm_num
              exact Batch0225.cell1804.sound htau (by
                simp only [Batch0225.cell1804, Batch0225.tau1804, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120133 (by positivity) using 1 <;> norm_num)
    · have hs11203 : InSquare (19/80) (-21/80) (1/80) tau := by
        convert childUR hs hx1120 hy1120 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx11203 | hx11203
      · rcases le_total tau.im (-21/80 : ℝ) with hy11203 | hy11203
        · have hs112030 : InSquare (37/160) (-43/160) (1/160) tau := by
            convert childLL hs11203 hx11203 hy11203 using 1 <;> norm_num
          exact Batch0081.cell0652.sound htau (by
            simp only [Batch0081.cell0652, Batch0081.tau0652, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112030 (by positivity) using 1 <;> norm_num)
        · have hs112032 : InSquare (37/160) (-41/160) (1/160) tau := by
            convert childUL hs11203 hx11203 hy11203 using 1 <;> norm_num
          exact Batch0081.cell0654.sound htau (by
            simp only [Batch0081.cell0654, Batch0081.tau0654, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy11203 | hy11203
        · have hs112031 : InSquare (39/160) (-43/160) (1/160) tau := by
            convert childLR hs11203 hx11203 hy11203 using 1 <;> norm_num
          exact Batch0081.cell0653.sound htau (by
            simp only [Batch0081.cell0653, Batch0081.tau0653, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112031 (by positivity) using 1 <;> norm_num)
        · have hs112033 : InSquare (39/160) (-41/160) (1/160) tau := by
            convert childUR hs11203 hx11203 hy11203 using 1 <;> norm_num
          exact Batch0081.cell0655.sound htau (by
            simp only [Batch0081.cell0655, Batch0081.tau0655, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1120

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1121 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1121

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_112111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/160) (-47/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/80)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1121100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (89/320) (-19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/40)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1121101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/320) (-19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/32)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1121103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/320) (-93/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/32)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1121130 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (93/320) (-91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/80)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1121131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (19/64) (-91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-47/160)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1121133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (19/64) (-89/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-47/160)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx1121 | hx1121
  · rcases le_total tau.im (-11/40 : ℝ) with hy1121 | hy1121
    · have hs11210 : InSquare (21/80) (-23/80) (1/80) tau := by
        convert childLL hs hx1121 hy1121 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx11210 | hx11210
      · rcases le_total tau.im (-23/80 : ℝ) with hy11210 | hy11210
        · have hs112100 : InSquare (41/160) (-47/160) (1/160) tau := by
            convert childLL hs11210 hx11210 hy11210 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx112100 | hx112100
          · rcases le_total tau.im (-47/160 : ℝ) with hy112100 | hy112100
            · have hs1121000 : InSquare (81/320) (-19/64) (1/320) tau := by
                convert childLL hs112100 hx112100 hy112100 using 1 <;> norm_num
              exact Batch0225.cell1805.sound htau (by
                simp only [Batch0225.cell1805, Batch0225.tau1805, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121000 (by positivity) using 1 <;> norm_num)
            · have hs1121002 : InSquare (81/320) (-93/320) (1/320) tau := by
                convert childUL hs112100 hx112100 hy112100 using 1 <;> norm_num
              exact Batch0225.cell1807.sound htau (by
                simp only [Batch0225.cell1807, Batch0225.tau1807, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy112100 | hy112100
            · have hs1121001 : InSquare (83/320) (-19/64) (1/320) tau := by
                convert childLR hs112100 hx112100 hy112100 using 1 <;> norm_num
              exact Batch0225.cell1806.sound htau (by
                simp only [Batch0225.cell1806, Batch0225.tau1806, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121001 (by positivity) using 1 <;> norm_num)
            · have hs1121003 : InSquare (83/320) (-93/320) (1/320) tau := by
                convert childUR hs112100 hx112100 hy112100 using 1 <;> norm_num
              exact Batch0226.cell1808.sound htau (by
                simp only [Batch0226.cell1808, Batch0226.tau1808, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121003 (by positivity) using 1 <;> norm_num)
        · have hs112102 : InSquare (41/160) (-9/32) (1/160) tau := by
            convert childUL hs11210 hx11210 hy11210 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx112102 | hx112102
          · rcases le_total tau.im (-9/32 : ℝ) with hy112102 | hy112102
            · have hs1121020 : InSquare (81/320) (-91/320) (1/320) tau := by
                convert childLL hs112102 hx112102 hy112102 using 1 <;> norm_num
              exact Batch0226.cell1813.sound htau (by
                simp only [Batch0226.cell1813, Batch0226.tau1813, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121020 (by positivity) using 1 <;> norm_num)
            · have hs1121022 : InSquare (81/320) (-89/320) (1/320) tau := by
                convert childUL hs112102 hx112102 hy112102 using 1 <;> norm_num
              exact Batch0226.cell1815.sound htau (by
                simp only [Batch0226.cell1815, Batch0226.tau1815, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy112102 | hy112102
            · have hs1121021 : InSquare (83/320) (-91/320) (1/320) tau := by
                convert childLR hs112102 hx112102 hy112102 using 1 <;> norm_num
              exact Batch0226.cell1814.sound htau (by
                simp only [Batch0226.cell1814, Batch0226.tau1814, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121021 (by positivity) using 1 <;> norm_num)
            · have hs1121023 : InSquare (83/320) (-89/320) (1/320) tau := by
                convert childUR hs112102 hx112102 hy112102 using 1 <;> norm_num
              exact Batch0227.cell1816.sound htau (by
                simp only [Batch0227.cell1816, Batch0227.tau1816, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy11210 | hy11210
        · have hs112101 : InSquare (43/160) (-47/160) (1/160) tau := by
            convert childLR hs11210 hx11210 hy11210 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx112101 | hx112101
          · rcases le_total tau.im (-47/160 : ℝ) with hy112101 | hy112101
            · have hs1121010 : InSquare (17/64) (-19/64) (1/320) tau := by
                convert childLL hs112101 hx112101 hy112101 using 1 <;> norm_num
              exact Batch0226.cell1809.sound htau (by
                simp only [Batch0226.cell1809, Batch0226.tau1809, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121010 (by positivity) using 1 <;> norm_num)
            · have hs1121012 : InSquare (17/64) (-93/320) (1/320) tau := by
                convert childUL hs112101 hx112101 hy112101 using 1 <;> norm_num
              exact Batch0226.cell1811.sound htau (by
                simp only [Batch0226.cell1811, Batch0226.tau1811, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy112101 | hy112101
            · have hs1121011 : InSquare (87/320) (-19/64) (1/320) tau := by
                convert childLR hs112101 hx112101 hy112101 using 1 <;> norm_num
              exact Batch0226.cell1810.sound htau (by
                simp only [Batch0226.cell1810, Batch0226.tau1810, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121011 (by positivity) using 1 <;> norm_num)
            · have hs1121013 : InSquare (87/320) (-93/320) (1/320) tau := by
                convert childUR hs112101 hx112101 hy112101 using 1 <;> norm_num
              exact Batch0226.cell1812.sound htau (by
                simp only [Batch0226.cell1812, Batch0226.tau1812, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121013 (by positivity) using 1 <;> norm_num)
        · have hs112103 : InSquare (43/160) (-9/32) (1/160) tau := by
            convert childUR hs11210 hx11210 hy11210 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx112103 | hx112103
          · rcases le_total tau.im (-9/32 : ℝ) with hy112103 | hy112103
            · have hs1121030 : InSquare (17/64) (-91/320) (1/320) tau := by
                convert childLL hs112103 hx112103 hy112103 using 1 <;> norm_num
              exact Batch0227.cell1817.sound htau (by
                simp only [Batch0227.cell1817, Batch0227.tau1817, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121030 (by positivity) using 1 <;> norm_num)
            · have hs1121032 : InSquare (17/64) (-89/320) (1/320) tau := by
                convert childUL hs112103 hx112103 hy112103 using 1 <;> norm_num
              exact Batch0227.cell1819.sound htau (by
                simp only [Batch0227.cell1819, Batch0227.tau1819, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy112103 | hy112103
            · have hs1121031 : InSquare (87/320) (-91/320) (1/320) tau := by
                convert childLR hs112103 hx112103 hy112103 using 1 <;> norm_num
              exact Batch0227.cell1818.sound htau (by
                simp only [Batch0227.cell1818, Batch0227.tau1818, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121031 (by positivity) using 1 <;> norm_num)
            · have hs1121033 : InSquare (87/320) (-89/320) (1/320) tau := by
                convert childUR hs112103 hx112103 hy112103 using 1 <;> norm_num
              exact Batch0227.cell1820.sound htau (by
                simp only [Batch0227.cell1820, Batch0227.tau1820, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121033 (by positivity) using 1 <;> norm_num)
    · have hs11212 : InSquare (21/80) (-21/80) (1/80) tau := by
        convert childUL hs hx1121 hy1121 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx11212 | hx11212
      · rcases le_total tau.im (-21/80 : ℝ) with hy11212 | hy11212
        · have hs112120 : InSquare (41/160) (-43/160) (1/160) tau := by
            convert childLL hs11212 hx11212 hy11212 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx112120 | hx112120
          · rcases le_total tau.im (-43/160 : ℝ) with hy112120 | hy112120
            · have hs1121200 : InSquare (81/320) (-87/320) (1/320) tau := by
                convert childLL hs112120 hx112120 hy112120 using 1 <;> norm_num
              exact Batch0228.cell1827.sound htau (by
                simp only [Batch0228.cell1827, Batch0228.tau1827, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121200 (by positivity) using 1 <;> norm_num)
            · have hs1121202 : InSquare (81/320) (-17/64) (1/320) tau := by
                convert childUL hs112120 hx112120 hy112120 using 1 <;> norm_num
              exact Batch0228.cell1829.sound htau (by
                simp only [Batch0228.cell1829, Batch0228.tau1829, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy112120 | hy112120
            · have hs1121201 : InSquare (83/320) (-87/320) (1/320) tau := by
                convert childLR hs112120 hx112120 hy112120 using 1 <;> norm_num
              exact Batch0228.cell1828.sound htau (by
                simp only [Batch0228.cell1828, Batch0228.tau1828, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121201 (by positivity) using 1 <;> norm_num)
            · have hs1121203 : InSquare (83/320) (-17/64) (1/320) tau := by
                convert childUR hs112120 hx112120 hy112120 using 1 <;> norm_num
              exact Batch0228.cell1830.sound htau (by
                simp only [Batch0228.cell1830, Batch0228.tau1830, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121203 (by positivity) using 1 <;> norm_num)
        · have hs112122 : InSquare (41/160) (-41/160) (1/160) tau := by
            convert childUL hs11212 hx11212 hy11212 using 1 <;> norm_num
          exact Batch0082.cell0656.sound htau (by
            simp only [Batch0082.cell0656, Batch0082.tau0656, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy11212 | hy11212
        · have hs112121 : InSquare (43/160) (-43/160) (1/160) tau := by
            convert childLR hs11212 hx11212 hy11212 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx112121 | hx112121
          · rcases le_total tau.im (-43/160 : ℝ) with hy112121 | hy112121
            · have hs1121210 : InSquare (17/64) (-87/320) (1/320) tau := by
                convert childLL hs112121 hx112121 hy112121 using 1 <;> norm_num
              exact Batch0228.cell1831.sound htau (by
                simp only [Batch0228.cell1831, Batch0228.tau1831, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121210 (by positivity) using 1 <;> norm_num)
            · have hs1121212 : InSquare (17/64) (-17/64) (1/320) tau := by
                convert childUL hs112121 hx112121 hy112121 using 1 <;> norm_num
              exact Batch0229.cell1833.sound htau (by
                simp only [Batch0229.cell1833, Batch0229.tau1833, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy112121 | hy112121
            · have hs1121211 : InSquare (87/320) (-87/320) (1/320) tau := by
                convert childLR hs112121 hx112121 hy112121 using 1 <;> norm_num
              exact Batch0229.cell1832.sound htau (by
                simp only [Batch0229.cell1832, Batch0229.tau1832, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121211 (by positivity) using 1 <;> norm_num)
            · have hs1121213 : InSquare (87/320) (-17/64) (1/320) tau := by
                convert childUR hs112121 hx112121 hy112121 using 1 <;> norm_num
              exact Batch0229.cell1834.sound htau (by
                simp only [Batch0229.cell1834, Batch0229.tau1834, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121213 (by positivity) using 1 <;> norm_num)
        · have hs112123 : InSquare (43/160) (-41/160) (1/160) tau := by
            convert childUR hs11212 hx11212 hy11212 using 1 <;> norm_num
          exact Batch0082.cell0657.sound htau (by
            simp only [Batch0082.cell0657, Batch0082.tau0657, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy1121 | hy1121
    · have hs11211 : InSquare (23/80) (-23/80) (1/80) tau := by
        convert childLR hs hx1121 hy1121 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx11211 | hx11211
      · rcases le_total tau.im (-23/80 : ℝ) with hy11211 | hy11211
        · have hs112110 : InSquare (9/32) (-47/160) (1/160) tau := by
            convert childLL hs11211 hx11211 hy11211 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx112110 | hx112110
          · rcases le_total tau.im (-47/160 : ℝ) with hy112110 | hy112110
            · have hs1121100 : InSquare (89/320) (-19/64) (1/320) tau := by
                convert childLL hs112110 hx112110 hy112110 using 1 <;> norm_num
              exact (outside_1121100 htau hs1121100).elim
            · have hs1121102 : InSquare (89/320) (-93/320) (1/320) tau := by
                convert childUL hs112110 hx112110 hy112110 using 1 <;> norm_num
              exact Batch0227.cell1821.sound htau (by
                simp only [Batch0227.cell1821, Batch0227.tau1821, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy112110 | hy112110
            · have hs1121101 : InSquare (91/320) (-19/64) (1/320) tau := by
                convert childLR hs112110 hx112110 hy112110 using 1 <;> norm_num
              exact (outside_1121101 htau hs1121101).elim
            · have hs1121103 : InSquare (91/320) (-93/320) (1/320) tau := by
                convert childUR hs112110 hx112110 hy112110 using 1 <;> norm_num
              exact (outside_1121103 htau hs1121103).elim
        · have hs112112 : InSquare (9/32) (-9/32) (1/160) tau := by
            convert childUL hs11211 hx11211 hy11211 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx112112 | hx112112
          · rcases le_total tau.im (-9/32 : ℝ) with hy112112 | hy112112
            · have hs1121120 : InSquare (89/320) (-91/320) (1/320) tau := by
                convert childLL hs112112 hx112112 hy112112 using 1 <;> norm_num
              exact Batch0227.cell1822.sound htau (by
                simp only [Batch0227.cell1822, Batch0227.tau1822, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121120 (by positivity) using 1 <;> norm_num)
            · have hs1121122 : InSquare (89/320) (-89/320) (1/320) tau := by
                convert childUL hs112112 hx112112 hy112112 using 1 <;> norm_num
              exact Batch0228.cell1824.sound htau (by
                simp only [Batch0228.cell1824, Batch0228.tau1824, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy112112 | hy112112
            · have hs1121121 : InSquare (91/320) (-91/320) (1/320) tau := by
                convert childLR hs112112 hx112112 hy112112 using 1 <;> norm_num
              exact Batch0227.cell1823.sound htau (by
                simp only [Batch0227.cell1823, Batch0227.tau1823, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121121 (by positivity) using 1 <;> norm_num)
            · have hs1121123 : InSquare (91/320) (-89/320) (1/320) tau := by
                convert childUR hs112112 hx112112 hy112112 using 1 <;> norm_num
              exact Batch0228.cell1825.sound htau (by
                simp only [Batch0228.cell1825, Batch0228.tau1825, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy11211 | hy11211
        · have hs112111 : InSquare (47/160) (-47/160) (1/160) tau := by
            convert childLR hs11211 hx11211 hy11211 using 1 <;> norm_num
          exact (outside_112111 htau hs112111).elim
        · have hs112113 : InSquare (47/160) (-9/32) (1/160) tau := by
            convert childUR hs11211 hx11211 hy11211 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx112113 | hx112113
          · rcases le_total tau.im (-9/32 : ℝ) with hy112113 | hy112113
            · have hs1121130 : InSquare (93/320) (-91/320) (1/320) tau := by
                convert childLL hs112113 hx112113 hy112113 using 1 <;> norm_num
              exact (outside_1121130 htau hs1121130).elim
            · have hs1121132 : InSquare (93/320) (-89/320) (1/320) tau := by
                convert childUL hs112113 hx112113 hy112113 using 1 <;> norm_num
              exact Batch0228.cell1826.sound htau (by
                simp only [Batch0228.cell1826, Batch0228.tau1826, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy112113 | hy112113
            · have hs1121131 : InSquare (19/64) (-91/320) (1/320) tau := by
                convert childLR hs112113 hx112113 hy112113 using 1 <;> norm_num
              exact (outside_1121131 htau hs1121131).elim
            · have hs1121133 : InSquare (19/64) (-89/320) (1/320) tau := by
                convert childUR hs112113 hx112113 hy112113 using 1 <;> norm_num
              exact (outside_1121133 htau hs1121133).elim
    · have hs11213 : InSquare (23/80) (-21/80) (1/80) tau := by
        convert childUR hs hx1121 hy1121 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx11213 | hx11213
      · rcases le_total tau.im (-21/80 : ℝ) with hy11213 | hy11213
        · have hs112130 : InSquare (9/32) (-43/160) (1/160) tau := by
            convert childLL hs11213 hx11213 hy11213 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx112130 | hx112130
          · rcases le_total tau.im (-43/160 : ℝ) with hy112130 | hy112130
            · have hs1121300 : InSquare (89/320) (-87/320) (1/320) tau := by
                convert childLL hs112130 hx112130 hy112130 using 1 <;> norm_num
              exact Batch0229.cell1835.sound htau (by
                simp only [Batch0229.cell1835, Batch0229.tau1835, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121300 (by positivity) using 1 <;> norm_num)
            · have hs1121302 : InSquare (89/320) (-17/64) (1/320) tau := by
                convert childUL hs112130 hx112130 hy112130 using 1 <;> norm_num
              exact Batch0229.cell1837.sound htau (by
                simp only [Batch0229.cell1837, Batch0229.tau1837, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy112130 | hy112130
            · have hs1121301 : InSquare (91/320) (-87/320) (1/320) tau := by
                convert childLR hs112130 hx112130 hy112130 using 1 <;> norm_num
              exact Batch0229.cell1836.sound htau (by
                simp only [Batch0229.cell1836, Batch0229.tau1836, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121301 (by positivity) using 1 <;> norm_num)
            · have hs1121303 : InSquare (91/320) (-17/64) (1/320) tau := by
                convert childUR hs112130 hx112130 hy112130 using 1 <;> norm_num
              exact Batch0229.cell1838.sound htau (by
                simp only [Batch0229.cell1838, Batch0229.tau1838, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121303 (by positivity) using 1 <;> norm_num)
        · have hs112132 : InSquare (9/32) (-41/160) (1/160) tau := by
            convert childUL hs11213 hx11213 hy11213 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx112132 | hx112132
          · rcases le_total tau.im (-41/160 : ℝ) with hy112132 | hy112132
            · have hs1121320 : InSquare (89/320) (-83/320) (1/320) tau := by
                convert childLL hs112132 hx112132 hy112132 using 1 <;> norm_num
              exact Batch0230.cell1843.sound htau (by
                simp only [Batch0230.cell1843, Batch0230.tau1843, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121320 (by positivity) using 1 <;> norm_num)
            · have hs1121322 : InSquare (89/320) (-81/320) (1/320) tau := by
                convert childUL hs112132 hx112132 hy112132 using 1 <;> norm_num
              exact Batch0230.cell1845.sound htau (by
                simp only [Batch0230.cell1845, Batch0230.tau1845, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-41/160 : ℝ) with hy112132 | hy112132
            · have hs1121321 : InSquare (91/320) (-83/320) (1/320) tau := by
                convert childLR hs112132 hx112132 hy112132 using 1 <;> norm_num
              exact Batch0230.cell1844.sound htau (by
                simp only [Batch0230.cell1844, Batch0230.tau1844, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121321 (by positivity) using 1 <;> norm_num)
            · have hs1121323 : InSquare (91/320) (-81/320) (1/320) tau := by
                convert childUR hs112132 hx112132 hy112132 using 1 <;> norm_num
              exact Batch0230.cell1846.sound htau (by
                simp only [Batch0230.cell1846, Batch0230.tau1846, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy11213 | hy11213
        · have hs112131 : InSquare (47/160) (-43/160) (1/160) tau := by
            convert childLR hs11213 hx11213 hy11213 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx112131 | hx112131
          · rcases le_total tau.im (-43/160 : ℝ) with hy112131 | hy112131
            · have hs1121310 : InSquare (93/320) (-87/320) (1/320) tau := by
                convert childLL hs112131 hx112131 hy112131 using 1 <;> norm_num
              exact Batch0229.cell1839.sound htau (by
                simp only [Batch0229.cell1839, Batch0229.tau1839, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121310 (by positivity) using 1 <;> norm_num)
            · have hs1121312 : InSquare (93/320) (-17/64) (1/320) tau := by
                convert childUL hs112131 hx112131 hy112131 using 1 <;> norm_num
              exact Batch0230.cell1841.sound htau (by
                simp only [Batch0230.cell1841, Batch0230.tau1841, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy112131 | hy112131
            · have hs1121311 : InSquare (19/64) (-87/320) (1/320) tau := by
                convert childLR hs112131 hx112131 hy112131 using 1 <;> norm_num
              exact Batch0230.cell1840.sound htau (by
                simp only [Batch0230.cell1840, Batch0230.tau1840, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121311 (by positivity) using 1 <;> norm_num)
            · have hs1121313 : InSquare (19/64) (-17/64) (1/320) tau := by
                convert childUR hs112131 hx112131 hy112131 using 1 <;> norm_num
              exact Batch0230.cell1842.sound htau (by
                simp only [Batch0230.cell1842, Batch0230.tau1842, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121313 (by positivity) using 1 <;> norm_num)
        · have hs112133 : InSquare (47/160) (-41/160) (1/160) tau := by
            convert childUR hs11213 hx11213 hy11213 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx112133 | hx112133
          · rcases le_total tau.im (-41/160 : ℝ) with hy112133 | hy112133
            · have hs1121330 : InSquare (93/320) (-83/320) (1/320) tau := by
                convert childLL hs112133 hx112133 hy112133 using 1 <;> norm_num
              exact Batch0230.cell1847.sound htau (by
                simp only [Batch0230.cell1847, Batch0230.tau1847, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121330 (by positivity) using 1 <;> norm_num)
            · have hs1121332 : InSquare (93/320) (-81/320) (1/320) tau := by
                convert childUL hs112133 hx112133 hy112133 using 1 <;> norm_num
              exact Batch0231.cell1849.sound htau (by
                simp only [Batch0231.cell1849, Batch0231.tau1849, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-41/160 : ℝ) with hy112133 | hy112133
            · have hs1121331 : InSquare (19/64) (-83/320) (1/320) tau := by
                convert childLR hs112133 hx112133 hy112133 using 1 <;> norm_num
              exact Batch0231.cell1848.sound htau (by
                simp only [Batch0231.cell1848, Batch0231.tau1848, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121331 (by positivity) using 1 <;> norm_num)
            · have hs1121333 : InSquare (19/64) (-81/320) (1/320) tau := by
                convert childUR hs112133 hx112133 hy112133 using 1 <;> norm_num
              exact Batch0231.cell1850.sound htau (by
                simp only [Batch0231.cell1850, Batch0231.tau1850, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1121

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1122 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1122

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx1122 | hx1122
  · rcases le_total tau.im (-9/40 : ℝ) with hy1122 | hy1122
    · have hs11220 : InSquare (17/80) (-19/80) (1/80) tau := by
        convert childLL hs hx1122 hy1122 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx11220 | hx11220
      · rcases le_total tau.im (-19/80 : ℝ) with hy11220 | hy11220
        · have hs112200 : InSquare (33/160) (-39/160) (1/160) tau := by
            convert childLL hs11220 hx11220 hy11220 using 1 <;> norm_num
          exact Batch0082.cell0658.sound htau (by
            simp only [Batch0082.cell0658, Batch0082.tau0658, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112200 (by positivity) using 1 <;> norm_num)
        · have hs112202 : InSquare (33/160) (-37/160) (1/160) tau := by
            convert childUL hs11220 hx11220 hy11220 using 1 <;> norm_num
          exact Batch0082.cell0660.sound htau (by
            simp only [Batch0082.cell0660, Batch0082.tau0660, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy11220 | hy11220
        · have hs112201 : InSquare (7/32) (-39/160) (1/160) tau := by
            convert childLR hs11220 hx11220 hy11220 using 1 <;> norm_num
          exact Batch0082.cell0659.sound htau (by
            simp only [Batch0082.cell0659, Batch0082.tau0659, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112201 (by positivity) using 1 <;> norm_num)
        · have hs112203 : InSquare (7/32) (-37/160) (1/160) tau := by
            convert childUR hs11220 hx11220 hy11220 using 1 <;> norm_num
          exact Batch0082.cell0661.sound htau (by
            simp only [Batch0082.cell0661, Batch0082.tau0661, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112203 (by positivity) using 1 <;> norm_num)
    · have hs11222 : InSquare (17/80) (-17/80) (1/80) tau := by
        convert childUL hs hx1122 hy1122 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx11222 | hx11222
      · rcases le_total tau.im (-17/80 : ℝ) with hy11222 | hy11222
        · have hs112220 : InSquare (33/160) (-7/32) (1/160) tau := by
            convert childLL hs11222 hx11222 hy11222 using 1 <;> norm_num
          exact Batch0083.cell0666.sound htau (by
            simp only [Batch0083.cell0666, Batch0083.tau0666, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112220 (by positivity) using 1 <;> norm_num)
        · have hs112222 : InSquare (33/160) (-33/160) (1/160) tau := by
            convert childUL hs11222 hx11222 hy11222 using 1 <;> norm_num
          exact Batch0083.cell0668.sound htau (by
            simp only [Batch0083.cell0668, Batch0083.tau0668, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy11222 | hy11222
        · have hs112221 : InSquare (7/32) (-7/32) (1/160) tau := by
            convert childLR hs11222 hx11222 hy11222 using 1 <;> norm_num
          exact Batch0083.cell0667.sound htau (by
            simp only [Batch0083.cell0667, Batch0083.tau0667, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112221 (by positivity) using 1 <;> norm_num)
        · have hs112223 : InSquare (7/32) (-33/160) (1/160) tau := by
            convert childUR hs11222 hx11222 hy11222 using 1 <;> norm_num
          exact Batch0083.cell0669.sound htau (by
            simp only [Batch0083.cell0669, Batch0083.tau0669, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy1122 | hy1122
    · have hs11221 : InSquare (19/80) (-19/80) (1/80) tau := by
        convert childLR hs hx1122 hy1122 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx11221 | hx11221
      · rcases le_total tau.im (-19/80 : ℝ) with hy11221 | hy11221
        · have hs112210 : InSquare (37/160) (-39/160) (1/160) tau := by
            convert childLL hs11221 hx11221 hy11221 using 1 <;> norm_num
          exact Batch0082.cell0662.sound htau (by
            simp only [Batch0082.cell0662, Batch0082.tau0662, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112210 (by positivity) using 1 <;> norm_num)
        · have hs112212 : InSquare (37/160) (-37/160) (1/160) tau := by
            convert childUL hs11221 hx11221 hy11221 using 1 <;> norm_num
          exact Batch0083.cell0664.sound htau (by
            simp only [Batch0083.cell0664, Batch0083.tau0664, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy11221 | hy11221
        · have hs112211 : InSquare (39/160) (-39/160) (1/160) tau := by
            convert childLR hs11221 hx11221 hy11221 using 1 <;> norm_num
          exact Batch0082.cell0663.sound htau (by
            simp only [Batch0082.cell0663, Batch0082.tau0663, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112211 (by positivity) using 1 <;> norm_num)
        · have hs112213 : InSquare (39/160) (-37/160) (1/160) tau := by
            convert childUR hs11221 hx11221 hy11221 using 1 <;> norm_num
          exact Batch0083.cell0665.sound htau (by
            simp only [Batch0083.cell0665, Batch0083.tau0665, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112213 (by positivity) using 1 <;> norm_num)
    · have hs11223 : InSquare (19/80) (-17/80) (1/80) tau := by
        convert childUR hs hx1122 hy1122 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx11223 | hx11223
      · rcases le_total tau.im (-17/80 : ℝ) with hy11223 | hy11223
        · have hs112230 : InSquare (37/160) (-7/32) (1/160) tau := by
            convert childLL hs11223 hx11223 hy11223 using 1 <;> norm_num
          exact Batch0083.cell0670.sound htau (by
            simp only [Batch0083.cell0670, Batch0083.tau0670, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112230 (by positivity) using 1 <;> norm_num)
        · have hs112232 : InSquare (37/160) (-33/160) (1/160) tau := by
            convert childUL hs11223 hx11223 hy11223 using 1 <;> norm_num
          exact Batch0084.cell0672.sound htau (by
            simp only [Batch0084.cell0672, Batch0084.tau0672, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy11223 | hy11223
        · have hs112231 : InSquare (39/160) (-7/32) (1/160) tau := by
            convert childLR hs11223 hx11223 hy11223 using 1 <;> norm_num
          exact Batch0083.cell0671.sound htau (by
            simp only [Batch0083.cell0671, Batch0083.tau0671, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112231 (by positivity) using 1 <;> norm_num)
        · have hs112233 : InSquare (39/160) (-33/160) (1/160) tau := by
            convert childUR hs11223 hx11223 hy11223 using 1 <;> norm_num
          exact Batch0084.cell0673.sound htau (by
            simp only [Batch0084.cell0673, Batch0084.tau0673, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1122

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1123 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1123

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx1123 | hx1123
  · rcases le_total tau.im (-9/40 : ℝ) with hy1123 | hy1123
    · have hs11230 : InSquare (21/80) (-19/80) (1/80) tau := by
        convert childLL hs hx1123 hy1123 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx11230 | hx11230
      · rcases le_total tau.im (-19/80 : ℝ) with hy11230 | hy11230
        · have hs112300 : InSquare (41/160) (-39/160) (1/160) tau := by
            convert childLL hs11230 hx11230 hy11230 using 1 <;> norm_num
          exact Batch0084.cell0674.sound htau (by
            simp only [Batch0084.cell0674, Batch0084.tau0674, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112300 (by positivity) using 1 <;> norm_num)
        · have hs112302 : InSquare (41/160) (-37/160) (1/160) tau := by
            convert childUL hs11230 hx11230 hy11230 using 1 <;> norm_num
          exact Batch0084.cell0676.sound htau (by
            simp only [Batch0084.cell0676, Batch0084.tau0676, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy11230 | hy11230
        · have hs112301 : InSquare (43/160) (-39/160) (1/160) tau := by
            convert childLR hs11230 hx11230 hy11230 using 1 <;> norm_num
          exact Batch0084.cell0675.sound htau (by
            simp only [Batch0084.cell0675, Batch0084.tau0675, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112301 (by positivity) using 1 <;> norm_num)
        · have hs112303 : InSquare (43/160) (-37/160) (1/160) tau := by
            convert childUR hs11230 hx11230 hy11230 using 1 <;> norm_num
          exact Batch0084.cell0677.sound htau (by
            simp only [Batch0084.cell0677, Batch0084.tau0677, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112303 (by positivity) using 1 <;> norm_num)
    · have hs11232 : InSquare (21/80) (-17/80) (1/80) tau := by
        convert childUL hs hx1123 hy1123 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx11232 | hx11232
      · rcases le_total tau.im (-17/80 : ℝ) with hy11232 | hy11232
        · have hs112320 : InSquare (41/160) (-7/32) (1/160) tau := by
            convert childLL hs11232 hx11232 hy11232 using 1 <;> norm_num
          exact Batch0085.cell0681.sound htau (by
            simp only [Batch0085.cell0681, Batch0085.tau0681, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112320 (by positivity) using 1 <;> norm_num)
        · have hs112322 : InSquare (41/160) (-33/160) (1/160) tau := by
            convert childUL hs11232 hx11232 hy11232 using 1 <;> norm_num
          exact Batch0085.cell0683.sound htau (by
            simp only [Batch0085.cell0683, Batch0085.tau0683, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy11232 | hy11232
        · have hs112321 : InSquare (43/160) (-7/32) (1/160) tau := by
            convert childLR hs11232 hx11232 hy11232 using 1 <;> norm_num
          exact Batch0085.cell0682.sound htau (by
            simp only [Batch0085.cell0682, Batch0085.tau0682, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112321 (by positivity) using 1 <;> norm_num)
        · have hs112323 : InSquare (43/160) (-33/160) (1/160) tau := by
            convert childUR hs11232 hx11232 hy11232 using 1 <;> norm_num
          exact Batch0085.cell0684.sound htau (by
            simp only [Batch0085.cell0684, Batch0085.tau0684, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy1123 | hy1123
    · have hs11231 : InSquare (23/80) (-19/80) (1/80) tau := by
        convert childLR hs hx1123 hy1123 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx11231 | hx11231
      · rcases le_total tau.im (-19/80 : ℝ) with hy11231 | hy11231
        · have hs112310 : InSquare (9/32) (-39/160) (1/160) tau := by
            convert childLL hs11231 hx11231 hy11231 using 1 <;> norm_num
          exact Batch0084.cell0678.sound htau (by
            simp only [Batch0084.cell0678, Batch0084.tau0678, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112310 (by positivity) using 1 <;> norm_num)
        · have hs112312 : InSquare (9/32) (-37/160) (1/160) tau := by
            convert childUL hs11231 hx11231 hy11231 using 1 <;> norm_num
          exact Batch0084.cell0679.sound htau (by
            simp only [Batch0084.cell0679, Batch0084.tau0679, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy11231 | hy11231
        · have hs112311 : InSquare (47/160) (-39/160) (1/160) tau := by
            convert childLR hs11231 hx11231 hy11231 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx112311 | hx112311
          · rcases le_total tau.im (-39/160 : ℝ) with hy112311 | hy112311
            · have hs1123110 : InSquare (93/320) (-79/320) (1/320) tau := by
                convert childLL hs112311 hx112311 hy112311 using 1 <;> norm_num
              exact Batch0231.cell1851.sound htau (by
                simp only [Batch0231.cell1851, Batch0231.tau1851, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1123110 (by positivity) using 1 <;> norm_num)
            · have hs1123112 : InSquare (93/320) (-77/320) (1/320) tau := by
                convert childUL hs112311 hx112311 hy112311 using 1 <;> norm_num
              exact Batch0231.cell1853.sound htau (by
                simp only [Batch0231.cell1853, Batch0231.tau1853, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1123112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-39/160 : ℝ) with hy112311 | hy112311
            · have hs1123111 : InSquare (19/64) (-79/320) (1/320) tau := by
                convert childLR hs112311 hx112311 hy112311 using 1 <;> norm_num
              exact Batch0231.cell1852.sound htau (by
                simp only [Batch0231.cell1852, Batch0231.tau1852, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1123111 (by positivity) using 1 <;> norm_num)
            · have hs1123113 : InSquare (19/64) (-77/320) (1/320) tau := by
                convert childUR hs112311 hx112311 hy112311 using 1 <;> norm_num
              exact Batch0231.cell1854.sound htau (by
                simp only [Batch0231.cell1854, Batch0231.tau1854, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1123113 (by positivity) using 1 <;> norm_num)
        · have hs112313 : InSquare (47/160) (-37/160) (1/160) tau := by
            convert childUR hs11231 hx11231 hy11231 using 1 <;> norm_num
          exact Batch0085.cell0680.sound htau (by
            simp only [Batch0085.cell0680, Batch0085.tau0680, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112313 (by positivity) using 1 <;> norm_num)
    · have hs11233 : InSquare (23/80) (-17/80) (1/80) tau := by
        convert childUR hs hx1123 hy1123 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx11233 | hx11233
      · rcases le_total tau.im (-17/80 : ℝ) with hy11233 | hy11233
        · have hs112330 : InSquare (9/32) (-7/32) (1/160) tau := by
            convert childLL hs11233 hx11233 hy11233 using 1 <;> norm_num
          exact Batch0085.cell0685.sound htau (by
            simp only [Batch0085.cell0685, Batch0085.tau0685, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112330 (by positivity) using 1 <;> norm_num)
        · have hs112332 : InSquare (9/32) (-33/160) (1/160) tau := by
            convert childUL hs11233 hx11233 hy11233 using 1 <;> norm_num
          exact Batch0085.cell0687.sound htau (by
            simp only [Batch0085.cell0687, Batch0085.tau0687, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy11233 | hy11233
        · have hs112331 : InSquare (47/160) (-7/32) (1/160) tau := by
            convert childLR hs11233 hx11233 hy11233 using 1 <;> norm_num
          exact Batch0085.cell0686.sound htau (by
            simp only [Batch0085.cell0686, Batch0085.tau0686, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112331 (by positivity) using 1 <;> norm_num)
        · have hs112333 : InSquare (47/160) (-33/160) (1/160) tau := by
            convert childUR hs11233 hx11233 hy11233 using 1 <;> norm_num
          exact Batch0086.cell0688.sound htau (by
            simp only [Batch0086.cell0688, Batch0086.tau0688, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1123

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1130 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1130

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_11300 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (5/16) (-23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/10)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11301 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (27/80) (-23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/40)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11303 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (27/80) (-21/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/40)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_113021 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (51/160) (-43/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-5/16)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_113023 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (51/160) (-41/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-5/16)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1130200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (97/320) (-87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/10)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1130201 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (99/320) (-87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-49/160)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1130203 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (99/320) (-17/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-49/160)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx1130 | hx1130
  · rcases le_total tau.im (-11/40 : ℝ) with hy1130 | hy1130
    · have hs11300 : InSquare (5/16) (-23/80) (1/80) tau := by
        convert childLL hs hx1130 hy1130 using 1 <;> norm_num
      exact (outside_11300 htau hs11300).elim
    · have hs11302 : InSquare (5/16) (-21/80) (1/80) tau := by
        convert childUL hs hx1130 hy1130 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx11302 | hx11302
      · rcases le_total tau.im (-21/80 : ℝ) with hy11302 | hy11302
        · have hs113020 : InSquare (49/160) (-43/160) (1/160) tau := by
            convert childLL hs11302 hx11302 hy11302 using 1 <;> norm_num
          rcases le_total tau.re (49/160 : ℝ) with hx113020 | hx113020
          · rcases le_total tau.im (-43/160 : ℝ) with hy113020 | hy113020
            · have hs1130200 : InSquare (97/320) (-87/320) (1/320) tau := by
                convert childLL hs113020 hx113020 hy113020 using 1 <;> norm_num
              exact (outside_1130200 htau hs1130200).elim
            · have hs1130202 : InSquare (97/320) (-17/64) (1/320) tau := by
                convert childUL hs113020 hx113020 hy113020 using 1 <;> norm_num
              exact Batch0231.cell1855.sound htau (by
                simp only [Batch0231.cell1855, Batch0231.tau1855, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1130202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy113020 | hy113020
            · have hs1130201 : InSquare (99/320) (-87/320) (1/320) tau := by
                convert childLR hs113020 hx113020 hy113020 using 1 <;> norm_num
              exact (outside_1130201 htau hs1130201).elim
            · have hs1130203 : InSquare (99/320) (-17/64) (1/320) tau := by
                convert childUR hs113020 hx113020 hy113020 using 1 <;> norm_num
              exact (outside_1130203 htau hs1130203).elim
        · have hs113022 : InSquare (49/160) (-41/160) (1/160) tau := by
            convert childUL hs11302 hx11302 hy11302 using 1 <;> norm_num
          rcases le_total tau.re (49/160 : ℝ) with hx113022 | hx113022
          · rcases le_total tau.im (-41/160 : ℝ) with hy113022 | hy113022
            · have hs1130220 : InSquare (97/320) (-83/320) (1/320) tau := by
                convert childLL hs113022 hx113022 hy113022 using 1 <;> norm_num
              exact Batch0232.cell1856.sound htau (by
                simp only [Batch0232.cell1856, Batch0232.tau1856, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1130220 (by positivity) using 1 <;> norm_num)
            · have hs1130222 : InSquare (97/320) (-81/320) (1/320) tau := by
                convert childUL hs113022 hx113022 hy113022 using 1 <;> norm_num
              exact Batch0232.cell1858.sound htau (by
                simp only [Batch0232.cell1858, Batch0232.tau1858, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1130222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-41/160 : ℝ) with hy113022 | hy113022
            · have hs1130221 : InSquare (99/320) (-83/320) (1/320) tau := by
                convert childLR hs113022 hx113022 hy113022 using 1 <;> norm_num
              exact Batch0232.cell1857.sound htau (by
                simp only [Batch0232.cell1857, Batch0232.tau1857, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1130221 (by positivity) using 1 <;> norm_num)
            · have hs1130223 : InSquare (99/320) (-81/320) (1/320) tau := by
                convert childUR hs113022 hx113022 hy113022 using 1 <;> norm_num
              exact Batch0232.cell1859.sound htau (by
                simp only [Batch0232.cell1859, Batch0232.tau1859, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1130223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy11302 | hy11302
        · have hs113021 : InSquare (51/160) (-43/160) (1/160) tau := by
            convert childLR hs11302 hx11302 hy11302 using 1 <;> norm_num
          exact (outside_113021 htau hs113021).elim
        · have hs113023 : InSquare (51/160) (-41/160) (1/160) tau := by
            convert childUR hs11302 hx11302 hy11302 using 1 <;> norm_num
          exact (outside_113023 htau hs113023).elim
  · rcases le_total tau.im (-11/40 : ℝ) with hy1130 | hy1130
    · have hs11301 : InSquare (27/80) (-23/80) (1/80) tau := by
        convert childLR hs hx1130 hy1130 using 1 <;> norm_num
      exact (outside_11301 htau hs11301).elim
    · have hs11303 : InSquare (27/80) (-21/80) (1/80) tau := by
        convert childUR hs hx1130 hy1130 using 1 <;> norm_num
      exact (outside_11303 htau hs11303).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1130

end


