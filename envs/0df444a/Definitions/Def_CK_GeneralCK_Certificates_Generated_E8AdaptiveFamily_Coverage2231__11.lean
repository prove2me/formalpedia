-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2231__11
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2231__11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:19:00.48799+00:00
-- url     : https://prove2.me/theorems/610ab39c-78b0-49e3-a734-dd8901fcf5e0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2231 (+10 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2300, GeneralCK.Certifi…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2231 (+10 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2300, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2301, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2302, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2303, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2310, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2311, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2312, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2313, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2320, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2321)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2231 (+10 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2300, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2301, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2302, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2303, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2310, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2311, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2312, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2313, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2320, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2321)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2231 (+10 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2300, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2301, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2302, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2303, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2310, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2311, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2312, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2313, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2320, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2321) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2231 (+10 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2300, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2301, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2302, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2303, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2310, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2311, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2312, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2313, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2320, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2321).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0248
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0249
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0250
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0251
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0252
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0253
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0400
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0401
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0402
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0031
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0112
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0113
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0032
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0114
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0115
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0116
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0117
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0033
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0118
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0254
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0255
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0256
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0257
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0258
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0259
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0260
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0403
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0119
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0261
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0262
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0263
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0264

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2231 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2231

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_223120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-39/160) (53/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/80)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_223122 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-39/160) (11/32) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/80)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_223123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-37/160) (11/32) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/40)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2231022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-79/320) (103/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+39/160)]
  have himSq : (51/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-51/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2231212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-15/64) (107/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+37/160)]
  have himSq : (53/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-53/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2231213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-73/320) (107/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/40)]
  have himSq : (53/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-53/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2231320 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-71/320) (109/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/32)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2231322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-71/320) (111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/32)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2231323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-69/320) (111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+17/80)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2231332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-67/320) (111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (33/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+33/160)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22312100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-151/640) (209/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (15/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+15/64)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22312102 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-151/640) (211/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (15/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+15/64)]
  have himSq : (21/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-21/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22312103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-149/640) (211/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+37/160)]
  have himSq : (21/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-21/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22313022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-143/640) (43/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (71/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+71/320)]
  have himSq : (107/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-107/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22313210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-139/640) (217/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (69/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+69/320)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22313212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-139/640) (219/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (69/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+69/320)]
  have himSq : (109/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-109/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22313213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-137/640) (219/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+17/80)]
  have himSq : (109/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-109/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22313332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-131/640) (223/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/64)]
  have himSq : (111/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-111/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22313333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-129/640) (223/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/5 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/5)]
  have himSq : (111/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-111/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx2231 | hx2231
  · rcases le_total tau.im (13/40 : ℝ) with hy2231 | hy2231
    · have hs22310 : InSquare (-19/80) (5/16) (1/80) tau := by
        convert childLL hs hx2231 hy2231 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx22310 | hx22310
      · rcases le_total tau.im (5/16 : ℝ) with hy22310 | hy22310
        · have hs223100 : InSquare (-39/160) (49/160) (1/160) tau := by
            convert childLL hs22310 hx22310 hy22310 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx223100 | hx223100
          · rcases le_total tau.im (49/160 : ℝ) with hy223100 | hy223100
            · have hs2231000 : InSquare (-79/320) (97/320) (1/320) tau := by
                convert childLL hs223100 hx223100 hy223100 using 1 <;> norm_num
              exact Batch0248.cell1988.sound htau (by
                simp only [Batch0248.cell1988, Batch0248.tau1988, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231000 (by positivity) using 1 <;> norm_num)
            · have hs2231002 : InSquare (-79/320) (99/320) (1/320) tau := by
                convert childUL hs223100 hx223100 hy223100 using 1 <;> norm_num
              exact Batch0248.cell1990.sound htau (by
                simp only [Batch0248.cell1990, Batch0248.tau1990, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy223100 | hy223100
            · have hs2231001 : InSquare (-77/320) (97/320) (1/320) tau := by
                convert childLR hs223100 hx223100 hy223100 using 1 <;> norm_num
              exact Batch0248.cell1989.sound htau (by
                simp only [Batch0248.cell1989, Batch0248.tau1989, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231001 (by positivity) using 1 <;> norm_num)
            · have hs2231003 : InSquare (-77/320) (99/320) (1/320) tau := by
                convert childUR hs223100 hx223100 hy223100 using 1 <;> norm_num
              exact Batch0248.cell1991.sound htau (by
                simp only [Batch0248.cell1991, Batch0248.tau1991, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231003 (by positivity) using 1 <;> norm_num)
        · have hs223102 : InSquare (-39/160) (51/160) (1/160) tau := by
            convert childUL hs22310 hx22310 hy22310 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx223102 | hx223102
          · rcases le_total tau.im (51/160 : ℝ) with hy223102 | hy223102
            · have hs2231020 : InSquare (-79/320) (101/320) (1/320) tau := by
                convert childLL hs223102 hx223102 hy223102 using 1 <;> norm_num
              exact Batch0249.cell1996.sound htau (by
                simp only [Batch0249.cell1996, Batch0249.tau1996, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231020 (by positivity) using 1 <;> norm_num)
            · have hs2231022 : InSquare (-79/320) (103/320) (1/320) tau := by
                convert childUL hs223102 hx223102 hy223102 using 1 <;> norm_num
              exact (outside_2231022 htau hs2231022).elim
          · rcases le_total tau.im (51/160 : ℝ) with hy223102 | hy223102
            · have hs2231021 : InSquare (-77/320) (101/320) (1/320) tau := by
                convert childLR hs223102 hx223102 hy223102 using 1 <;> norm_num
              exact Batch0249.cell1997.sound htau (by
                simp only [Batch0249.cell1997, Batch0249.tau1997, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231021 (by positivity) using 1 <;> norm_num)
            · have hs2231023 : InSquare (-77/320) (103/320) (1/320) tau := by
                convert childUR hs223102 hx223102 hy223102 using 1 <;> norm_num
              exact Batch0249.cell1998.sound htau (by
                simp only [Batch0249.cell1998, Batch0249.tau1998, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy22310 | hy22310
        · have hs223101 : InSquare (-37/160) (49/160) (1/160) tau := by
            convert childLR hs22310 hx22310 hy22310 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx223101 | hx223101
          · rcases le_total tau.im (49/160 : ℝ) with hy223101 | hy223101
            · have hs2231010 : InSquare (-15/64) (97/320) (1/320) tau := by
                convert childLL hs223101 hx223101 hy223101 using 1 <;> norm_num
              exact Batch0249.cell1992.sound htau (by
                simp only [Batch0249.cell1992, Batch0249.tau1992, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231010 (by positivity) using 1 <;> norm_num)
            · have hs2231012 : InSquare (-15/64) (99/320) (1/320) tau := by
                convert childUL hs223101 hx223101 hy223101 using 1 <;> norm_num
              exact Batch0249.cell1994.sound htau (by
                simp only [Batch0249.cell1994, Batch0249.tau1994, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy223101 | hy223101
            · have hs2231011 : InSquare (-73/320) (97/320) (1/320) tau := by
                convert childLR hs223101 hx223101 hy223101 using 1 <;> norm_num
              exact Batch0249.cell1993.sound htau (by
                simp only [Batch0249.cell1993, Batch0249.tau1993, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231011 (by positivity) using 1 <;> norm_num)
            · have hs2231013 : InSquare (-73/320) (99/320) (1/320) tau := by
                convert childUR hs223101 hx223101 hy223101 using 1 <;> norm_num
              exact Batch0249.cell1995.sound htau (by
                simp only [Batch0249.cell1995, Batch0249.tau1995, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231013 (by positivity) using 1 <;> norm_num)
        · have hs223103 : InSquare (-37/160) (51/160) (1/160) tau := by
            convert childUR hs22310 hx22310 hy22310 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx223103 | hx223103
          · rcases le_total tau.im (51/160 : ℝ) with hy223103 | hy223103
            · have hs2231030 : InSquare (-15/64) (101/320) (1/320) tau := by
                convert childLL hs223103 hx223103 hy223103 using 1 <;> norm_num
              exact Batch0249.cell1999.sound htau (by
                simp only [Batch0249.cell1999, Batch0249.tau1999, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231030 (by positivity) using 1 <;> norm_num)
            · have hs2231032 : InSquare (-15/64) (103/320) (1/320) tau := by
                convert childUL hs223103 hx223103 hy223103 using 1 <;> norm_num
              exact Batch0250.cell2001.sound htau (by
                simp only [Batch0250.cell2001, Batch0250.tau2001, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy223103 | hy223103
            · have hs2231031 : InSquare (-73/320) (101/320) (1/320) tau := by
                convert childLR hs223103 hx223103 hy223103 using 1 <;> norm_num
              exact Batch0250.cell2000.sound htau (by
                simp only [Batch0250.cell2000, Batch0250.tau2000, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231031 (by positivity) using 1 <;> norm_num)
            · have hs2231033 : InSquare (-73/320) (103/320) (1/320) tau := by
                convert childUR hs223103 hx223103 hy223103 using 1 <;> norm_num
              exact Batch0250.cell2002.sound htau (by
                simp only [Batch0250.cell2002, Batch0250.tau2002, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231033 (by positivity) using 1 <;> norm_num)
    · have hs22312 : InSquare (-19/80) (27/80) (1/80) tau := by
        convert childUL hs hx2231 hy2231 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx22312 | hx22312
      · rcases le_total tau.im (27/80 : ℝ) with hy22312 | hy22312
        · have hs223120 : InSquare (-39/160) (53/160) (1/160) tau := by
            convert childLL hs22312 hx22312 hy22312 using 1 <;> norm_num
          exact (outside_223120 htau hs223120).elim
        · have hs223122 : InSquare (-39/160) (11/32) (1/160) tau := by
            convert childUL hs22312 hx22312 hy22312 using 1 <;> norm_num
          exact (outside_223122 htau hs223122).elim
      · rcases le_total tau.im (27/80 : ℝ) with hy22312 | hy22312
        · have hs223121 : InSquare (-37/160) (53/160) (1/160) tau := by
            convert childLR hs22312 hx22312 hy22312 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx223121 | hx223121
          · rcases le_total tau.im (53/160 : ℝ) with hy223121 | hy223121
            · have hs2231210 : InSquare (-15/64) (21/64) (1/320) tau := by
                convert childLL hs223121 hx223121 hy223121 using 1 <;> norm_num
              rcases le_total tau.re (-15/64 : ℝ) with hx2231210 | hx2231210
              · rcases le_total tau.im (21/64 : ℝ) with hy2231210 | hy2231210
                · have hs22312100 : InSquare (-151/640) (209/640) (1/640) tau := by
                    convert childLL hs2231210 hx2231210 hy2231210 using 1 <;> norm_num
                  exact (outside_22312100 htau hs22312100).elim
                · have hs22312102 : InSquare (-151/640) (211/640) (1/640) tau := by
                    convert childUL hs2231210 hx2231210 hy2231210 using 1 <;> norm_num
                  exact (outside_22312102 htau hs22312102).elim
              · rcases le_total tau.im (21/64 : ℝ) with hy2231210 | hy2231210
                · have hs22312101 : InSquare (-149/640) (209/640) (1/640) tau := by
                    convert childLR hs2231210 hx2231210 hy2231210 using 1 <;> norm_num
                  exact Batch0400.cell3204.sound htau (by
                    simp only [Batch0400.cell3204, Batch0400.tau3204, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22312101 (by positivity) using 1 <;> norm_num)
                · have hs22312103 : InSquare (-149/640) (211/640) (1/640) tau := by
                    convert childUR hs2231210 hx2231210 hy2231210 using 1 <;> norm_num
                  exact (outside_22312103 htau hs22312103).elim
            · have hs2231212 : InSquare (-15/64) (107/320) (1/320) tau := by
                convert childUL hs223121 hx223121 hy223121 using 1 <;> norm_num
              exact (outside_2231212 htau hs2231212).elim
          · rcases le_total tau.im (53/160 : ℝ) with hy223121 | hy223121
            · have hs2231211 : InSquare (-73/320) (21/64) (1/320) tau := by
                convert childLR hs223121 hx223121 hy223121 using 1 <;> norm_num
              exact Batch0252.cell2019.sound htau (by
                simp only [Batch0252.cell2019, Batch0252.tau2019, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231211 (by positivity) using 1 <;> norm_num)
            · have hs2231213 : InSquare (-73/320) (107/320) (1/320) tau := by
                convert childUR hs223121 hx223121 hy223121 using 1 <;> norm_num
              exact (outside_2231213 htau hs2231213).elim
        · have hs223123 : InSquare (-37/160) (11/32) (1/160) tau := by
            convert childUR hs22312 hx22312 hy22312 using 1 <;> norm_num
          exact (outside_223123 htau hs223123).elim
  · rcases le_total tau.im (13/40 : ℝ) with hy2231 | hy2231
    · have hs22311 : InSquare (-17/80) (5/16) (1/80) tau := by
        convert childLR hs hx2231 hy2231 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx22311 | hx22311
      · rcases le_total tau.im (5/16 : ℝ) with hy22311 | hy22311
        · have hs223110 : InSquare (-7/32) (49/160) (1/160) tau := by
            convert childLL hs22311 hx22311 hy22311 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx223110 | hx223110
          · rcases le_total tau.im (49/160 : ℝ) with hy223110 | hy223110
            · have hs2231100 : InSquare (-71/320) (97/320) (1/320) tau := by
                convert childLL hs223110 hx223110 hy223110 using 1 <;> norm_num
              exact Batch0250.cell2003.sound htau (by
                simp only [Batch0250.cell2003, Batch0250.tau2003, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231100 (by positivity) using 1 <;> norm_num)
            · have hs2231102 : InSquare (-71/320) (99/320) (1/320) tau := by
                convert childUL hs223110 hx223110 hy223110 using 1 <;> norm_num
              exact Batch0250.cell2005.sound htau (by
                simp only [Batch0250.cell2005, Batch0250.tau2005, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy223110 | hy223110
            · have hs2231101 : InSquare (-69/320) (97/320) (1/320) tau := by
                convert childLR hs223110 hx223110 hy223110 using 1 <;> norm_num
              exact Batch0250.cell2004.sound htau (by
                simp only [Batch0250.cell2004, Batch0250.tau2004, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231101 (by positivity) using 1 <;> norm_num)
            · have hs2231103 : InSquare (-69/320) (99/320) (1/320) tau := by
                convert childUR hs223110 hx223110 hy223110 using 1 <;> norm_num
              exact Batch0250.cell2006.sound htau (by
                simp only [Batch0250.cell2006, Batch0250.tau2006, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231103 (by positivity) using 1 <;> norm_num)
        · have hs223112 : InSquare (-7/32) (51/160) (1/160) tau := by
            convert childUL hs22311 hx22311 hy22311 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx223112 | hx223112
          · rcases le_total tau.im (51/160 : ℝ) with hy223112 | hy223112
            · have hs2231120 : InSquare (-71/320) (101/320) (1/320) tau := by
                convert childLL hs223112 hx223112 hy223112 using 1 <;> norm_num
              exact Batch0251.cell2011.sound htau (by
                simp only [Batch0251.cell2011, Batch0251.tau2011, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231120 (by positivity) using 1 <;> norm_num)
            · have hs2231122 : InSquare (-71/320) (103/320) (1/320) tau := by
                convert childUL hs223112 hx223112 hy223112 using 1 <;> norm_num
              exact Batch0251.cell2013.sound htau (by
                simp only [Batch0251.cell2013, Batch0251.tau2013, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy223112 | hy223112
            · have hs2231121 : InSquare (-69/320) (101/320) (1/320) tau := by
                convert childLR hs223112 hx223112 hy223112 using 1 <;> norm_num
              exact Batch0251.cell2012.sound htau (by
                simp only [Batch0251.cell2012, Batch0251.tau2012, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231121 (by positivity) using 1 <;> norm_num)
            · have hs2231123 : InSquare (-69/320) (103/320) (1/320) tau := by
                convert childUR hs223112 hx223112 hy223112 using 1 <;> norm_num
              exact Batch0251.cell2014.sound htau (by
                simp only [Batch0251.cell2014, Batch0251.tau2014, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy22311 | hy22311
        · have hs223111 : InSquare (-33/160) (49/160) (1/160) tau := by
            convert childLR hs22311 hx22311 hy22311 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx223111 | hx223111
          · rcases le_total tau.im (49/160 : ℝ) with hy223111 | hy223111
            · have hs2231110 : InSquare (-67/320) (97/320) (1/320) tau := by
                convert childLL hs223111 hx223111 hy223111 using 1 <;> norm_num
              exact Batch0250.cell2007.sound htau (by
                simp only [Batch0250.cell2007, Batch0250.tau2007, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231110 (by positivity) using 1 <;> norm_num)
            · have hs2231112 : InSquare (-67/320) (99/320) (1/320) tau := by
                convert childUL hs223111 hx223111 hy223111 using 1 <;> norm_num
              exact Batch0251.cell2009.sound htau (by
                simp only [Batch0251.cell2009, Batch0251.tau2009, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy223111 | hy223111
            · have hs2231111 : InSquare (-13/64) (97/320) (1/320) tau := by
                convert childLR hs223111 hx223111 hy223111 using 1 <;> norm_num
              exact Batch0251.cell2008.sound htau (by
                simp only [Batch0251.cell2008, Batch0251.tau2008, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231111 (by positivity) using 1 <;> norm_num)
            · have hs2231113 : InSquare (-13/64) (99/320) (1/320) tau := by
                convert childUR hs223111 hx223111 hy223111 using 1 <;> norm_num
              exact Batch0251.cell2010.sound htau (by
                simp only [Batch0251.cell2010, Batch0251.tau2010, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231113 (by positivity) using 1 <;> norm_num)
        · have hs223113 : InSquare (-33/160) (51/160) (1/160) tau := by
            convert childUR hs22311 hx22311 hy22311 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx223113 | hx223113
          · rcases le_total tau.im (51/160 : ℝ) with hy223113 | hy223113
            · have hs2231130 : InSquare (-67/320) (101/320) (1/320) tau := by
                convert childLL hs223113 hx223113 hy223113 using 1 <;> norm_num
              exact Batch0251.cell2015.sound htau (by
                simp only [Batch0251.cell2015, Batch0251.tau2015, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231130 (by positivity) using 1 <;> norm_num)
            · have hs2231132 : InSquare (-67/320) (103/320) (1/320) tau := by
                convert childUL hs223113 hx223113 hy223113 using 1 <;> norm_num
              exact Batch0252.cell2017.sound htau (by
                simp only [Batch0252.cell2017, Batch0252.tau2017, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy223113 | hy223113
            · have hs2231131 : InSquare (-13/64) (101/320) (1/320) tau := by
                convert childLR hs223113 hx223113 hy223113 using 1 <;> norm_num
              exact Batch0252.cell2016.sound htau (by
                simp only [Batch0252.cell2016, Batch0252.tau2016, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231131 (by positivity) using 1 <;> norm_num)
            · have hs2231133 : InSquare (-13/64) (103/320) (1/320) tau := by
                convert childUR hs223113 hx223113 hy223113 using 1 <;> norm_num
              exact Batch0252.cell2018.sound htau (by
                simp only [Batch0252.cell2018, Batch0252.tau2018, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231133 (by positivity) using 1 <;> norm_num)
    · have hs22313 : InSquare (-17/80) (27/80) (1/80) tau := by
        convert childUR hs hx2231 hy2231 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx22313 | hx22313
      · rcases le_total tau.im (27/80 : ℝ) with hy22313 | hy22313
        · have hs223130 : InSquare (-7/32) (53/160) (1/160) tau := by
            convert childLL hs22313 hx22313 hy22313 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx223130 | hx223130
          · rcases le_total tau.im (53/160 : ℝ) with hy223130 | hy223130
            · have hs2231300 : InSquare (-71/320) (21/64) (1/320) tau := by
                convert childLL hs223130 hx223130 hy223130 using 1 <;> norm_num
              exact Batch0252.cell2020.sound htau (by
                simp only [Batch0252.cell2020, Batch0252.tau2020, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231300 (by positivity) using 1 <;> norm_num)
            · have hs2231302 : InSquare (-71/320) (107/320) (1/320) tau := by
                convert childUL hs223130 hx223130 hy223130 using 1 <;> norm_num
              rcases le_total tau.re (-71/320 : ℝ) with hx2231302 | hx2231302
              · rcases le_total tau.im (107/320 : ℝ) with hy2231302 | hy2231302
                · have hs22313020 : InSquare (-143/640) (213/640) (1/640) tau := by
                    convert childLL hs2231302 hx2231302 hy2231302 using 1 <;> norm_num
                  exact Batch0400.cell3205.sound htau (by
                    simp only [Batch0400.cell3205, Batch0400.tau3205, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313020 (by positivity) using 1 <;> norm_num)
                · have hs22313022 : InSquare (-143/640) (43/128) (1/640) tau := by
                    convert childUL hs2231302 hx2231302 hy2231302 using 1 <;> norm_num
                  exact (outside_22313022 htau hs22313022).elim
              · rcases le_total tau.im (107/320 : ℝ) with hy2231302 | hy2231302
                · have hs22313021 : InSquare (-141/640) (213/640) (1/640) tau := by
                    convert childLR hs2231302 hx2231302 hy2231302 using 1 <;> norm_num
                  exact Batch0400.cell3206.sound htau (by
                    simp only [Batch0400.cell3206, Batch0400.tau3206, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313021 (by positivity) using 1 <;> norm_num)
                · have hs22313023 : InSquare (-141/640) (43/128) (1/640) tau := by
                    convert childUR hs2231302 hx2231302 hy2231302 using 1 <;> norm_num
                  exact Batch0400.cell3207.sound htau (by
                    simp only [Batch0400.cell3207, Batch0400.tau3207, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy223130 | hy223130
            · have hs2231301 : InSquare (-69/320) (21/64) (1/320) tau := by
                convert childLR hs223130 hx223130 hy223130 using 1 <;> norm_num
              exact Batch0252.cell2021.sound htau (by
                simp only [Batch0252.cell2021, Batch0252.tau2021, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231301 (by positivity) using 1 <;> norm_num)
            · have hs2231303 : InSquare (-69/320) (107/320) (1/320) tau := by
                convert childUR hs223130 hx223130 hy223130 using 1 <;> norm_num
              exact Batch0252.cell2022.sound htau (by
                simp only [Batch0252.cell2022, Batch0252.tau2022, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231303 (by positivity) using 1 <;> norm_num)
        · have hs223132 : InSquare (-7/32) (11/32) (1/160) tau := by
            convert childUL hs22313 hx22313 hy22313 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx223132 | hx223132
          · rcases le_total tau.im (11/32 : ℝ) with hy223132 | hy223132
            · have hs2231320 : InSquare (-71/320) (109/320) (1/320) tau := by
                convert childLL hs223132 hx223132 hy223132 using 1 <;> norm_num
              exact (outside_2231320 htau hs2231320).elim
            · have hs2231322 : InSquare (-71/320) (111/320) (1/320) tau := by
                convert childUL hs223132 hx223132 hy223132 using 1 <;> norm_num
              exact (outside_2231322 htau hs2231322).elim
          · rcases le_total tau.im (11/32 : ℝ) with hy223132 | hy223132
            · have hs2231321 : InSquare (-69/320) (109/320) (1/320) tau := by
                convert childLR hs223132 hx223132 hy223132 using 1 <;> norm_num
              rcases le_total tau.re (-69/320 : ℝ) with hx2231321 | hx2231321
              · rcases le_total tau.im (109/320 : ℝ) with hy2231321 | hy2231321
                · have hs22313210 : InSquare (-139/640) (217/640) (1/640) tau := by
                    convert childLL hs2231321 hx2231321 hy2231321 using 1 <;> norm_num
                  exact (outside_22313210 htau hs22313210).elim
                · have hs22313212 : InSquare (-139/640) (219/640) (1/640) tau := by
                    convert childUL hs2231321 hx2231321 hy2231321 using 1 <;> norm_num
                  exact (outside_22313212 htau hs22313212).elim
              · rcases le_total tau.im (109/320 : ℝ) with hy2231321 | hy2231321
                · have hs22313211 : InSquare (-137/640) (217/640) (1/640) tau := by
                    convert childLR hs2231321 hx2231321 hy2231321 using 1 <;> norm_num
                  exact Batch0401.cell3208.sound htau (by
                    simp only [Batch0401.cell3208, Batch0401.tau3208, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313211 (by positivity) using 1 <;> norm_num)
                · have hs22313213 : InSquare (-137/640) (219/640) (1/640) tau := by
                    convert childUR hs2231321 hx2231321 hy2231321 using 1 <;> norm_num
                  exact (outside_22313213 htau hs22313213).elim
            · have hs2231323 : InSquare (-69/320) (111/320) (1/320) tau := by
                convert childUR hs223132 hx223132 hy223132 using 1 <;> norm_num
              exact (outside_2231323 htau hs2231323).elim
      · rcases le_total tau.im (27/80 : ℝ) with hy22313 | hy22313
        · have hs223131 : InSquare (-33/160) (53/160) (1/160) tau := by
            convert childLR hs22313 hx22313 hy22313 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx223131 | hx223131
          · rcases le_total tau.im (53/160 : ℝ) with hy223131 | hy223131
            · have hs2231310 : InSquare (-67/320) (21/64) (1/320) tau := by
                convert childLL hs223131 hx223131 hy223131 using 1 <;> norm_num
              exact Batch0252.cell2023.sound htau (by
                simp only [Batch0252.cell2023, Batch0252.tau2023, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231310 (by positivity) using 1 <;> norm_num)
            · have hs2231312 : InSquare (-67/320) (107/320) (1/320) tau := by
                convert childUL hs223131 hx223131 hy223131 using 1 <;> norm_num
              exact Batch0253.cell2025.sound htau (by
                simp only [Batch0253.cell2025, Batch0253.tau2025, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy223131 | hy223131
            · have hs2231311 : InSquare (-13/64) (21/64) (1/320) tau := by
                convert childLR hs223131 hx223131 hy223131 using 1 <;> norm_num
              exact Batch0253.cell2024.sound htau (by
                simp only [Batch0253.cell2024, Batch0253.tau2024, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231311 (by positivity) using 1 <;> norm_num)
            · have hs2231313 : InSquare (-13/64) (107/320) (1/320) tau := by
                convert childUR hs223131 hx223131 hy223131 using 1 <;> norm_num
              exact Batch0253.cell2026.sound htau (by
                simp only [Batch0253.cell2026, Batch0253.tau2026, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231313 (by positivity) using 1 <;> norm_num)
        · have hs223133 : InSquare (-33/160) (11/32) (1/160) tau := by
            convert childUR hs22313 hx22313 hy22313 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx223133 | hx223133
          · rcases le_total tau.im (11/32 : ℝ) with hy223133 | hy223133
            · have hs2231330 : InSquare (-67/320) (109/320) (1/320) tau := by
                convert childLL hs223133 hx223133 hy223133 using 1 <;> norm_num
              rcases le_total tau.re (-67/320 : ℝ) with hx2231330 | hx2231330
              · rcases le_total tau.im (109/320 : ℝ) with hy2231330 | hy2231330
                · have hs22313300 : InSquare (-27/128) (217/640) (1/640) tau := by
                    convert childLL hs2231330 hx2231330 hy2231330 using 1 <;> norm_num
                  exact Batch0401.cell3209.sound htau (by
                    simp only [Batch0401.cell3209, Batch0401.tau3209, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313300 (by positivity) using 1 <;> norm_num)
                · have hs22313302 : InSquare (-27/128) (219/640) (1/640) tau := by
                    convert childUL hs2231330 hx2231330 hy2231330 using 1 <;> norm_num
                  exact Batch0401.cell3211.sound htau (by
                    simp only [Batch0401.cell3211, Batch0401.tau3211, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (109/320 : ℝ) with hy2231330 | hy2231330
                · have hs22313301 : InSquare (-133/640) (217/640) (1/640) tau := by
                    convert childLR hs2231330 hx2231330 hy2231330 using 1 <;> norm_num
                  exact Batch0401.cell3210.sound htau (by
                    simp only [Batch0401.cell3210, Batch0401.tau3210, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313301 (by positivity) using 1 <;> norm_num)
                · have hs22313303 : InSquare (-133/640) (219/640) (1/640) tau := by
                    convert childUR hs2231330 hx2231330 hy2231330 using 1 <;> norm_num
                  exact Batch0401.cell3212.sound htau (by
                    simp only [Batch0401.cell3212, Batch0401.tau3212, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313303 (by positivity) using 1 <;> norm_num)
            · have hs2231332 : InSquare (-67/320) (111/320) (1/320) tau := by
                convert childUL hs223133 hx223133 hy223133 using 1 <;> norm_num
              exact (outside_2231332 htau hs2231332).elim
          · rcases le_total tau.im (11/32 : ℝ) with hy223133 | hy223133
            · have hs2231331 : InSquare (-13/64) (109/320) (1/320) tau := by
                convert childLR hs223133 hx223133 hy223133 using 1 <;> norm_num
              rcases le_total tau.re (-13/64 : ℝ) with hx2231331 | hx2231331
              · rcases le_total tau.im (109/320 : ℝ) with hy2231331 | hy2231331
                · have hs22313310 : InSquare (-131/640) (217/640) (1/640) tau := by
                    convert childLL hs2231331 hx2231331 hy2231331 using 1 <;> norm_num
                  exact Batch0401.cell3213.sound htau (by
                    simp only [Batch0401.cell3213, Batch0401.tau3213, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313310 (by positivity) using 1 <;> norm_num)
                · have hs22313312 : InSquare (-131/640) (219/640) (1/640) tau := by
                    convert childUL hs2231331 hx2231331 hy2231331 using 1 <;> norm_num
                  exact Batch0401.cell3215.sound htau (by
                    simp only [Batch0401.cell3215, Batch0401.tau3215, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (109/320 : ℝ) with hy2231331 | hy2231331
                · have hs22313311 : InSquare (-129/640) (217/640) (1/640) tau := by
                    convert childLR hs2231331 hx2231331 hy2231331 using 1 <;> norm_num
                  exact Batch0401.cell3214.sound htau (by
                    simp only [Batch0401.cell3214, Batch0401.tau3214, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313311 (by positivity) using 1 <;> norm_num)
                · have hs22313313 : InSquare (-129/640) (219/640) (1/640) tau := by
                    convert childUR hs2231331 hx2231331 hy2231331 using 1 <;> norm_num
                  exact Batch0402.cell3216.sound htau (by
                    simp only [Batch0402.cell3216, Batch0402.tau3216, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313313 (by positivity) using 1 <;> norm_num)
            · have hs2231333 : InSquare (-13/64) (111/320) (1/320) tau := by
                convert childUR hs223133 hx223133 hy223133 using 1 <;> norm_num
              rcases le_total tau.re (-13/64 : ℝ) with hx2231333 | hx2231333
              · rcases le_total tau.im (111/320 : ℝ) with hy2231333 | hy2231333
                · have hs22313330 : InSquare (-131/640) (221/640) (1/640) tau := by
                    convert childLL hs2231333 hx2231333 hy2231333 using 1 <;> norm_num
                  exact Batch0402.cell3217.sound htau (by
                    simp only [Batch0402.cell3217, Batch0402.tau3217, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313330 (by positivity) using 1 <;> norm_num)
                · have hs22313332 : InSquare (-131/640) (223/640) (1/640) tau := by
                    convert childUL hs2231333 hx2231333 hy2231333 using 1 <;> norm_num
                  exact (outside_22313332 htau hs22313332).elim
              · rcases le_total tau.im (111/320 : ℝ) with hy2231333 | hy2231333
                · have hs22313331 : InSquare (-129/640) (221/640) (1/640) tau := by
                    convert childLR hs2231333 hx2231333 hy2231333 using 1 <;> norm_num
                  exact Batch0402.cell3218.sound htau (by
                    simp only [Batch0402.cell3218, Batch0402.tau3218, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313331 (by positivity) using 1 <;> norm_num)
                · have hs22313333 : InSquare (-129/640) (223/640) (1/640) tau := by
                    convert childUR hs2231333 hx2231333 hy2231333 using 1 <;> norm_num
                  exact (outside_22313333 htau hs22313333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2231

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2300 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2300

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx2300 | hx2300
  · rcases le_total tau.im (9/40 : ℝ) with hy2300 | hy2300
    · have hs23000 : InSquare (-3/16) (17/80) (1/80) tau := by
        convert childLL hs hx2300 hy2300 using 1 <;> norm_num
      exact Batch0031.cell0251.sound htau (by
        simp only [Batch0031.cell0251, Batch0031.tau0251, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23000 (by positivity) using 1 <;> norm_num)
    · have hs23002 : InSquare (-3/16) (19/80) (1/80) tau := by
        convert childUL hs hx2300 hy2300 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx23002 | hx23002
      · rcases le_total tau.im (19/80 : ℝ) with hy23002 | hy23002
        · have hs230020 : InSquare (-31/160) (37/160) (1/160) tau := by
            convert childLL hs23002 hx23002 hy23002 using 1 <;> norm_num
          exact Batch0112.cell0898.sound htau (by
            simp only [Batch0112.cell0898, Batch0112.tau0898, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230020 (by positivity) using 1 <;> norm_num)
        · have hs230022 : InSquare (-31/160) (39/160) (1/160) tau := by
            convert childUL hs23002 hx23002 hy23002 using 1 <;> norm_num
          exact Batch0112.cell0900.sound htau (by
            simp only [Batch0112.cell0900, Batch0112.tau0900, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy23002 | hy23002
        · have hs230021 : InSquare (-29/160) (37/160) (1/160) tau := by
            convert childLR hs23002 hx23002 hy23002 using 1 <;> norm_num
          exact Batch0112.cell0899.sound htau (by
            simp only [Batch0112.cell0899, Batch0112.tau0899, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230021 (by positivity) using 1 <;> norm_num)
        · have hs230023 : InSquare (-29/160) (39/160) (1/160) tau := by
            convert childUR hs23002 hx23002 hy23002 using 1 <;> norm_num
          exact Batch0112.cell0901.sound htau (by
            simp only [Batch0112.cell0901, Batch0112.tau0901, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy2300 | hy2300
    · have hs23001 : InSquare (-13/80) (17/80) (1/80) tau := by
        convert childLR hs hx2300 hy2300 using 1 <;> norm_num
      exact Batch0031.cell0252.sound htau (by
        simp only [Batch0031.cell0252, Batch0031.tau0252, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23001 (by positivity) using 1 <;> norm_num)
    · have hs23003 : InSquare (-13/80) (19/80) (1/80) tau := by
        convert childUR hs hx2300 hy2300 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx23003 | hx23003
      · rcases le_total tau.im (19/80 : ℝ) with hy23003 | hy23003
        · have hs230030 : InSquare (-27/160) (37/160) (1/160) tau := by
            convert childLL hs23003 hx23003 hy23003 using 1 <;> norm_num
          exact Batch0112.cell0902.sound htau (by
            simp only [Batch0112.cell0902, Batch0112.tau0902, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230030 (by positivity) using 1 <;> norm_num)
        · have hs230032 : InSquare (-27/160) (39/160) (1/160) tau := by
            convert childUL hs23003 hx23003 hy23003 using 1 <;> norm_num
          exact Batch0113.cell0904.sound htau (by
            simp only [Batch0113.cell0904, Batch0113.tau0904, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy23003 | hy23003
        · have hs230031 : InSquare (-5/32) (37/160) (1/160) tau := by
            convert childLR hs23003 hx23003 hy23003 using 1 <;> norm_num
          exact Batch0112.cell0903.sound htau (by
            simp only [Batch0112.cell0903, Batch0112.tau0903, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230031 (by positivity) using 1 <;> norm_num)
        · have hs230033 : InSquare (-5/32) (39/160) (1/160) tau := by
            convert childUR hs23003 hx23003 hy23003 using 1 <;> norm_num
          exact Batch0113.cell0905.sound htau (by
            simp only [Batch0113.cell0905, Batch0113.tau0905, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2300

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2301 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2301

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx2301 | hx2301
  · rcases le_total tau.im (9/40 : ℝ) with hy2301 | hy2301
    · have hs23010 : InSquare (-11/80) (17/80) (1/80) tau := by
        convert childLL hs hx2301 hy2301 using 1 <;> norm_num
      exact Batch0031.cell0253.sound htau (by
        simp only [Batch0031.cell0253, Batch0031.tau0253, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23010 (by positivity) using 1 <;> norm_num)
    · have hs23012 : InSquare (-11/80) (19/80) (1/80) tau := by
        convert childUL hs hx2301 hy2301 using 1 <;> norm_num
      exact Batch0031.cell0255.sound htau (by
        simp only [Batch0031.cell0255, Batch0031.tau0255, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23012 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy2301 | hy2301
    · have hs23011 : InSquare (-9/80) (17/80) (1/80) tau := by
        convert childLR hs hx2301 hy2301 using 1 <;> norm_num
      exact Batch0031.cell0254.sound htau (by
        simp only [Batch0031.cell0254, Batch0031.tau0254, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23011 (by positivity) using 1 <;> norm_num)
    · have hs23013 : InSquare (-9/80) (19/80) (1/80) tau := by
        convert childUR hs hx2301 hy2301 using 1 <;> norm_num
      exact Batch0032.cell0256.sound htau (by
        simp only [Batch0032.cell0256, Batch0032.tau0256, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23013 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2301

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2302 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2302

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx2302 | hx2302
  · rcases le_total tau.im (11/40 : ℝ) with hy2302 | hy2302
    · have hs23020 : InSquare (-3/16) (21/80) (1/80) tau := by
        convert childLL hs hx2302 hy2302 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx23020 | hx23020
      · rcases le_total tau.im (21/80 : ℝ) with hy23020 | hy23020
        · have hs230200 : InSquare (-31/160) (41/160) (1/160) tau := by
            convert childLL hs23020 hx23020 hy23020 using 1 <;> norm_num
          exact Batch0113.cell0906.sound htau (by
            simp only [Batch0113.cell0906, Batch0113.tau0906, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230200 (by positivity) using 1 <;> norm_num)
        · have hs230202 : InSquare (-31/160) (43/160) (1/160) tau := by
            convert childUL hs23020 hx23020 hy23020 using 1 <;> norm_num
          exact Batch0113.cell0908.sound htau (by
            simp only [Batch0113.cell0908, Batch0113.tau0908, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy23020 | hy23020
        · have hs230201 : InSquare (-29/160) (41/160) (1/160) tau := by
            convert childLR hs23020 hx23020 hy23020 using 1 <;> norm_num
          exact Batch0113.cell0907.sound htau (by
            simp only [Batch0113.cell0907, Batch0113.tau0907, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230201 (by positivity) using 1 <;> norm_num)
        · have hs230203 : InSquare (-29/160) (43/160) (1/160) tau := by
            convert childUR hs23020 hx23020 hy23020 using 1 <;> norm_num
          exact Batch0113.cell0909.sound htau (by
            simp only [Batch0113.cell0909, Batch0113.tau0909, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230203 (by positivity) using 1 <;> norm_num)
    · have hs23022 : InSquare (-3/16) (23/80) (1/80) tau := by
        convert childUL hs hx2302 hy2302 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx23022 | hx23022
      · rcases le_total tau.im (23/80 : ℝ) with hy23022 | hy23022
        · have hs230220 : InSquare (-31/160) (9/32) (1/160) tau := by
            convert childLL hs23022 hx23022 hy23022 using 1 <;> norm_num
          exact Batch0114.cell0914.sound htau (by
            simp only [Batch0114.cell0914, Batch0114.tau0914, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230220 (by positivity) using 1 <;> norm_num)
        · have hs230222 : InSquare (-31/160) (47/160) (1/160) tau := by
            convert childUL hs23022 hx23022 hy23022 using 1 <;> norm_num
          exact Batch0114.cell0916.sound htau (by
            simp only [Batch0114.cell0916, Batch0114.tau0916, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy23022 | hy23022
        · have hs230221 : InSquare (-29/160) (9/32) (1/160) tau := by
            convert childLR hs23022 hx23022 hy23022 using 1 <;> norm_num
          exact Batch0114.cell0915.sound htau (by
            simp only [Batch0114.cell0915, Batch0114.tau0915, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230221 (by positivity) using 1 <;> norm_num)
        · have hs230223 : InSquare (-29/160) (47/160) (1/160) tau := by
            convert childUR hs23022 hx23022 hy23022 using 1 <;> norm_num
          exact Batch0114.cell0917.sound htau (by
            simp only [Batch0114.cell0917, Batch0114.tau0917, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy2302 | hy2302
    · have hs23021 : InSquare (-13/80) (21/80) (1/80) tau := by
        convert childLR hs hx2302 hy2302 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx23021 | hx23021
      · rcases le_total tau.im (21/80 : ℝ) with hy23021 | hy23021
        · have hs230210 : InSquare (-27/160) (41/160) (1/160) tau := by
            convert childLL hs23021 hx23021 hy23021 using 1 <;> norm_num
          exact Batch0113.cell0910.sound htau (by
            simp only [Batch0113.cell0910, Batch0113.tau0910, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230210 (by positivity) using 1 <;> norm_num)
        · have hs230212 : InSquare (-27/160) (43/160) (1/160) tau := by
            convert childUL hs23021 hx23021 hy23021 using 1 <;> norm_num
          exact Batch0114.cell0912.sound htau (by
            simp only [Batch0114.cell0912, Batch0114.tau0912, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy23021 | hy23021
        · have hs230211 : InSquare (-5/32) (41/160) (1/160) tau := by
            convert childLR hs23021 hx23021 hy23021 using 1 <;> norm_num
          exact Batch0113.cell0911.sound htau (by
            simp only [Batch0113.cell0911, Batch0113.tau0911, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230211 (by positivity) using 1 <;> norm_num)
        · have hs230213 : InSquare (-5/32) (43/160) (1/160) tau := by
            convert childUR hs23021 hx23021 hy23021 using 1 <;> norm_num
          exact Batch0114.cell0913.sound htau (by
            simp only [Batch0114.cell0913, Batch0114.tau0913, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230213 (by positivity) using 1 <;> norm_num)
    · have hs23023 : InSquare (-13/80) (23/80) (1/80) tau := by
        convert childUR hs hx2302 hy2302 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx23023 | hx23023
      · rcases le_total tau.im (23/80 : ℝ) with hy23023 | hy23023
        · have hs230230 : InSquare (-27/160) (9/32) (1/160) tau := by
            convert childLL hs23023 hx23023 hy23023 using 1 <;> norm_num
          exact Batch0114.cell0918.sound htau (by
            simp only [Batch0114.cell0918, Batch0114.tau0918, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230230 (by positivity) using 1 <;> norm_num)
        · have hs230232 : InSquare (-27/160) (47/160) (1/160) tau := by
            convert childUL hs23023 hx23023 hy23023 using 1 <;> norm_num
          exact Batch0115.cell0920.sound htau (by
            simp only [Batch0115.cell0920, Batch0115.tau0920, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy23023 | hy23023
        · have hs230231 : InSquare (-5/32) (9/32) (1/160) tau := by
            convert childLR hs23023 hx23023 hy23023 using 1 <;> norm_num
          exact Batch0114.cell0919.sound htau (by
            simp only [Batch0114.cell0919, Batch0114.tau0919, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230231 (by positivity) using 1 <;> norm_num)
        · have hs230233 : InSquare (-5/32) (47/160) (1/160) tau := by
            convert childUR hs23023 hx23023 hy23023 using 1 <;> norm_num
          exact Batch0115.cell0921.sound htau (by
            simp only [Batch0115.cell0921, Batch0115.tau0921, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2302

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2303 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2303

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx2303 | hx2303
  · rcases le_total tau.im (11/40 : ℝ) with hy2303 | hy2303
    · have hs23030 : InSquare (-11/80) (21/80) (1/80) tau := by
        convert childLL hs hx2303 hy2303 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx23030 | hx23030
      · rcases le_total tau.im (21/80 : ℝ) with hy23030 | hy23030
        · have hs230300 : InSquare (-23/160) (41/160) (1/160) tau := by
            convert childLL hs23030 hx23030 hy23030 using 1 <;> norm_num
          exact Batch0115.cell0922.sound htau (by
            simp only [Batch0115.cell0922, Batch0115.tau0922, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230300 (by positivity) using 1 <;> norm_num)
        · have hs230302 : InSquare (-23/160) (43/160) (1/160) tau := by
            convert childUL hs23030 hx23030 hy23030 using 1 <;> norm_num
          exact Batch0115.cell0924.sound htau (by
            simp only [Batch0115.cell0924, Batch0115.tau0924, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy23030 | hy23030
        · have hs230301 : InSquare (-21/160) (41/160) (1/160) tau := by
            convert childLR hs23030 hx23030 hy23030 using 1 <;> norm_num
          exact Batch0115.cell0923.sound htau (by
            simp only [Batch0115.cell0923, Batch0115.tau0923, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230301 (by positivity) using 1 <;> norm_num)
        · have hs230303 : InSquare (-21/160) (43/160) (1/160) tau := by
            convert childUR hs23030 hx23030 hy23030 using 1 <;> norm_num
          exact Batch0115.cell0925.sound htau (by
            simp only [Batch0115.cell0925, Batch0115.tau0925, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230303 (by positivity) using 1 <;> norm_num)
    · have hs23032 : InSquare (-11/80) (23/80) (1/80) tau := by
        convert childUL hs hx2303 hy2303 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx23032 | hx23032
      · rcases le_total tau.im (23/80 : ℝ) with hy23032 | hy23032
        · have hs230320 : InSquare (-23/160) (9/32) (1/160) tau := by
            convert childLL hs23032 hx23032 hy23032 using 1 <;> norm_num
          exact Batch0116.cell0930.sound htau (by
            simp only [Batch0116.cell0930, Batch0116.tau0930, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230320 (by positivity) using 1 <;> norm_num)
        · have hs230322 : InSquare (-23/160) (47/160) (1/160) tau := by
            convert childUL hs23032 hx23032 hy23032 using 1 <;> norm_num
          exact Batch0116.cell0932.sound htau (by
            simp only [Batch0116.cell0932, Batch0116.tau0932, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy23032 | hy23032
        · have hs230321 : InSquare (-21/160) (9/32) (1/160) tau := by
            convert childLR hs23032 hx23032 hy23032 using 1 <;> norm_num
          exact Batch0116.cell0931.sound htau (by
            simp only [Batch0116.cell0931, Batch0116.tau0931, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230321 (by positivity) using 1 <;> norm_num)
        · have hs230323 : InSquare (-21/160) (47/160) (1/160) tau := by
            convert childUR hs23032 hx23032 hy23032 using 1 <;> norm_num
          exact Batch0116.cell0933.sound htau (by
            simp only [Batch0116.cell0933, Batch0116.tau0933, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy2303 | hy2303
    · have hs23031 : InSquare (-9/80) (21/80) (1/80) tau := by
        convert childLR hs hx2303 hy2303 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx23031 | hx23031
      · rcases le_total tau.im (21/80 : ℝ) with hy23031 | hy23031
        · have hs230310 : InSquare (-19/160) (41/160) (1/160) tau := by
            convert childLL hs23031 hx23031 hy23031 using 1 <;> norm_num
          exact Batch0115.cell0926.sound htau (by
            simp only [Batch0115.cell0926, Batch0115.tau0926, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230310 (by positivity) using 1 <;> norm_num)
        · have hs230312 : InSquare (-19/160) (43/160) (1/160) tau := by
            convert childUL hs23031 hx23031 hy23031 using 1 <;> norm_num
          exact Batch0116.cell0928.sound htau (by
            simp only [Batch0116.cell0928, Batch0116.tau0928, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy23031 | hy23031
        · have hs230311 : InSquare (-17/160) (41/160) (1/160) tau := by
            convert childLR hs23031 hx23031 hy23031 using 1 <;> norm_num
          exact Batch0115.cell0927.sound htau (by
            simp only [Batch0115.cell0927, Batch0115.tau0927, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230311 (by positivity) using 1 <;> norm_num)
        · have hs230313 : InSquare (-17/160) (43/160) (1/160) tau := by
            convert childUR hs23031 hx23031 hy23031 using 1 <;> norm_num
          exact Batch0116.cell0929.sound htau (by
            simp only [Batch0116.cell0929, Batch0116.tau0929, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230313 (by positivity) using 1 <;> norm_num)
    · have hs23033 : InSquare (-9/80) (23/80) (1/80) tau := by
        convert childUR hs hx2303 hy2303 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx23033 | hx23033
      · rcases le_total tau.im (23/80 : ℝ) with hy23033 | hy23033
        · have hs230330 : InSquare (-19/160) (9/32) (1/160) tau := by
            convert childLL hs23033 hx23033 hy23033 using 1 <;> norm_num
          exact Batch0116.cell0934.sound htau (by
            simp only [Batch0116.cell0934, Batch0116.tau0934, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230330 (by positivity) using 1 <;> norm_num)
        · have hs230332 : InSquare (-19/160) (47/160) (1/160) tau := by
            convert childUL hs23033 hx23033 hy23033 using 1 <;> norm_num
          exact Batch0117.cell0936.sound htau (by
            simp only [Batch0117.cell0936, Batch0117.tau0936, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy23033 | hy23033
        · have hs230331 : InSquare (-17/160) (9/32) (1/160) tau := by
            convert childLR hs23033 hx23033 hy23033 using 1 <;> norm_num
          exact Batch0116.cell0935.sound htau (by
            simp only [Batch0116.cell0935, Batch0116.tau0935, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230331 (by positivity) using 1 <;> norm_num)
        · have hs230333 : InSquare (-17/160) (47/160) (1/160) tau := by
            convert childUR hs23033 hx23033 hy23033 using 1 <;> norm_num
          exact Batch0117.cell0937.sound htau (by
            simp only [Batch0117.cell0937, Batch0117.tau0937, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2303

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2310 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2310

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx2310 | hx2310
  · rcases le_total tau.im (9/40 : ℝ) with hy2310 | hy2310
    · have hs23100 : InSquare (-7/80) (17/80) (1/80) tau := by
        convert childLL hs hx2310 hy2310 using 1 <;> norm_num
      exact Batch0032.cell0257.sound htau (by
        simp only [Batch0032.cell0257, Batch0032.tau0257, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23100 (by positivity) using 1 <;> norm_num)
    · have hs23102 : InSquare (-7/80) (19/80) (1/80) tau := by
        convert childUL hs hx2310 hy2310 using 1 <;> norm_num
      exact Batch0032.cell0259.sound htau (by
        simp only [Batch0032.cell0259, Batch0032.tau0259, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23102 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy2310 | hy2310
    · have hs23101 : InSquare (-1/16) (17/80) (1/80) tau := by
        convert childLR hs hx2310 hy2310 using 1 <;> norm_num
      exact Batch0032.cell0258.sound htau (by
        simp only [Batch0032.cell0258, Batch0032.tau0258, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23101 (by positivity) using 1 <;> norm_num)
    · have hs23103 : InSquare (-1/16) (19/80) (1/80) tau := by
        convert childUR hs hx2310 hy2310 using 1 <;> norm_num
      exact Batch0032.cell0260.sound htau (by
        simp only [Batch0032.cell0260, Batch0032.tau0260, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23103 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2310

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2311 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2311

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx2311 | hx2311
  · rcases le_total tau.im (9/40 : ℝ) with hy2311 | hy2311
    · have hs23110 : InSquare (-3/80) (17/80) (1/80) tau := by
        convert childLL hs hx2311 hy2311 using 1 <;> norm_num
      exact Batch0032.cell0261.sound htau (by
        simp only [Batch0032.cell0261, Batch0032.tau0261, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23110 (by positivity) using 1 <;> norm_num)
    · have hs23112 : InSquare (-3/80) (19/80) (1/80) tau := by
        convert childUL hs hx2311 hy2311 using 1 <;> norm_num
      exact Batch0032.cell0263.sound htau (by
        simp only [Batch0032.cell0263, Batch0032.tau0263, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23112 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy2311 | hy2311
    · have hs23111 : InSquare (-1/80) (17/80) (1/80) tau := by
        convert childLR hs hx2311 hy2311 using 1 <;> norm_num
      exact Batch0032.cell0262.sound htau (by
        simp only [Batch0032.cell0262, Batch0032.tau0262, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23111 (by positivity) using 1 <;> norm_num)
    · have hs23113 : InSquare (-1/80) (19/80) (1/80) tau := by
        convert childUR hs hx2311 hy2311 using 1 <;> norm_num
      exact Batch0033.cell0264.sound htau (by
        simp only [Batch0033.cell0264, Batch0033.tau0264, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23113 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2311

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2312 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2312

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx2312 | hx2312
  · rcases le_total tau.im (11/40 : ℝ) with hy2312 | hy2312
    · have hs23120 : InSquare (-7/80) (21/80) (1/80) tau := by
        convert childLL hs hx2312 hy2312 using 1 <;> norm_num
      exact Batch0033.cell0265.sound htau (by
        simp only [Batch0033.cell0265, Batch0033.tau0265, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23120 (by positivity) using 1 <;> norm_num)
    · have hs23122 : InSquare (-7/80) (23/80) (1/80) tau := by
        convert childUL hs hx2312 hy2312 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx23122 | hx23122
      · rcases le_total tau.im (23/80 : ℝ) with hy23122 | hy23122
        · have hs231220 : InSquare (-3/32) (9/32) (1/160) tau := by
            convert childLL hs23122 hx23122 hy23122 using 1 <;> norm_num
          exact Batch0117.cell0938.sound htau (by
            simp only [Batch0117.cell0938, Batch0117.tau0938, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231220 (by positivity) using 1 <;> norm_num)
        · have hs231222 : InSquare (-3/32) (47/160) (1/160) tau := by
            convert childUL hs23122 hx23122 hy23122 using 1 <;> norm_num
          exact Batch0117.cell0940.sound htau (by
            simp only [Batch0117.cell0940, Batch0117.tau0940, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy23122 | hy23122
        · have hs231221 : InSquare (-13/160) (9/32) (1/160) tau := by
            convert childLR hs23122 hx23122 hy23122 using 1 <;> norm_num
          exact Batch0117.cell0939.sound htau (by
            simp only [Batch0117.cell0939, Batch0117.tau0939, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231221 (by positivity) using 1 <;> norm_num)
        · have hs231223 : InSquare (-13/160) (47/160) (1/160) tau := by
            convert childUR hs23122 hx23122 hy23122 using 1 <;> norm_num
          exact Batch0117.cell0941.sound htau (by
            simp only [Batch0117.cell0941, Batch0117.tau0941, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy2312 | hy2312
    · have hs23121 : InSquare (-1/16) (21/80) (1/80) tau := by
        convert childLR hs hx2312 hy2312 using 1 <;> norm_num
      exact Batch0033.cell0266.sound htau (by
        simp only [Batch0033.cell0266, Batch0033.tau0266, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23121 (by positivity) using 1 <;> norm_num)
    · have hs23123 : InSquare (-1/16) (23/80) (1/80) tau := by
        convert childUR hs hx2312 hy2312 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx23123 | hx23123
      · rcases le_total tau.im (23/80 : ℝ) with hy23123 | hy23123
        · have hs231230 : InSquare (-11/160) (9/32) (1/160) tau := by
            convert childLL hs23123 hx23123 hy23123 using 1 <;> norm_num
          exact Batch0117.cell0942.sound htau (by
            simp only [Batch0117.cell0942, Batch0117.tau0942, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231230 (by positivity) using 1 <;> norm_num)
        · have hs231232 : InSquare (-11/160) (47/160) (1/160) tau := by
            convert childUL hs23123 hx23123 hy23123 using 1 <;> norm_num
          exact Batch0118.cell0944.sound htau (by
            simp only [Batch0118.cell0944, Batch0118.tau0944, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy23123 | hy23123
        · have hs231231 : InSquare (-9/160) (9/32) (1/160) tau := by
            convert childLR hs23123 hx23123 hy23123 using 1 <;> norm_num
          exact Batch0117.cell0943.sound htau (by
            simp only [Batch0117.cell0943, Batch0117.tau0943, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231231 (by positivity) using 1 <;> norm_num)
        · have hs231233 : InSquare (-9/160) (47/160) (1/160) tau := by
            convert childUR hs23123 hx23123 hy23123 using 1 <;> norm_num
          exact Batch0118.cell0945.sound htau (by
            simp only [Batch0118.cell0945, Batch0118.tau0945, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2312

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2313 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2313

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx2313 | hx2313
  · rcases le_total tau.im (11/40 : ℝ) with hy2313 | hy2313
    · have hs23130 : InSquare (-3/80) (21/80) (1/80) tau := by
        convert childLL hs hx2313 hy2313 using 1 <;> norm_num
      exact Batch0033.cell0267.sound htau (by
        simp only [Batch0033.cell0267, Batch0033.tau0267, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23130 (by positivity) using 1 <;> norm_num)
    · have hs23132 : InSquare (-3/80) (23/80) (1/80) tau := by
        convert childUL hs hx2313 hy2313 using 1 <;> norm_num
      exact Batch0033.cell0269.sound htau (by
        simp only [Batch0033.cell0269, Batch0033.tau0269, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23132 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy2313 | hy2313
    · have hs23131 : InSquare (-1/80) (21/80) (1/80) tau := by
        convert childLR hs hx2313 hy2313 using 1 <;> norm_num
      exact Batch0033.cell0268.sound htau (by
        simp only [Batch0033.cell0268, Batch0033.tau0268, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23131 (by positivity) using 1 <;> norm_num)
    · have hs23133 : InSquare (-1/80) (23/80) (1/80) tau := by
        convert childUR hs hx2313 hy2313 using 1 <;> norm_num
      exact Batch0033.cell0270.sound htau (by
        simp only [Batch0033.cell0270, Batch0033.tau0270, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2313

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2320 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2320

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx2320 | hx2320
  · rcases le_total tau.im (13/40 : ℝ) with hy2320 | hy2320
    · have hs23200 : InSquare (-3/16) (5/16) (1/80) tau := by
        convert childLL hs hx2320 hy2320 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx23200 | hx23200
      · rcases le_total tau.im (5/16 : ℝ) with hy23200 | hy23200
        · have hs232000 : InSquare (-31/160) (49/160) (1/160) tau := by
            convert childLL hs23200 hx23200 hy23200 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx232000 | hx232000
          · rcases le_total tau.im (49/160 : ℝ) with hy232000 | hy232000
            · have hs2320000 : InSquare (-63/320) (97/320) (1/320) tau := by
                convert childLL hs232000 hx232000 hy232000 using 1 <;> norm_num
              exact Batch0253.cell2027.sound htau (by
                simp only [Batch0253.cell2027, Batch0253.tau2027, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320000 (by positivity) using 1 <;> norm_num)
            · have hs2320002 : InSquare (-63/320) (99/320) (1/320) tau := by
                convert childUL hs232000 hx232000 hy232000 using 1 <;> norm_num
              exact Batch0253.cell2029.sound htau (by
                simp only [Batch0253.cell2029, Batch0253.tau2029, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy232000 | hy232000
            · have hs2320001 : InSquare (-61/320) (97/320) (1/320) tau := by
                convert childLR hs232000 hx232000 hy232000 using 1 <;> norm_num
              exact Batch0253.cell2028.sound htau (by
                simp only [Batch0253.cell2028, Batch0253.tau2028, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320001 (by positivity) using 1 <;> norm_num)
            · have hs2320003 : InSquare (-61/320) (99/320) (1/320) tau := by
                convert childUR hs232000 hx232000 hy232000 using 1 <;> norm_num
              exact Batch0253.cell2030.sound htau (by
                simp only [Batch0253.cell2030, Batch0253.tau2030, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320003 (by positivity) using 1 <;> norm_num)
        · have hs232002 : InSquare (-31/160) (51/160) (1/160) tau := by
            convert childUL hs23200 hx23200 hy23200 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx232002 | hx232002
          · rcases le_total tau.im (51/160 : ℝ) with hy232002 | hy232002
            · have hs2320020 : InSquare (-63/320) (101/320) (1/320) tau := by
                convert childLL hs232002 hx232002 hy232002 using 1 <;> norm_num
              exact Batch0254.cell2035.sound htau (by
                simp only [Batch0254.cell2035, Batch0254.tau2035, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320020 (by positivity) using 1 <;> norm_num)
            · have hs2320022 : InSquare (-63/320) (103/320) (1/320) tau := by
                convert childUL hs232002 hx232002 hy232002 using 1 <;> norm_num
              exact Batch0254.cell2037.sound htau (by
                simp only [Batch0254.cell2037, Batch0254.tau2037, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy232002 | hy232002
            · have hs2320021 : InSquare (-61/320) (101/320) (1/320) tau := by
                convert childLR hs232002 hx232002 hy232002 using 1 <;> norm_num
              exact Batch0254.cell2036.sound htau (by
                simp only [Batch0254.cell2036, Batch0254.tau2036, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320021 (by positivity) using 1 <;> norm_num)
            · have hs2320023 : InSquare (-61/320) (103/320) (1/320) tau := by
                convert childUR hs232002 hx232002 hy232002 using 1 <;> norm_num
              exact Batch0254.cell2038.sound htau (by
                simp only [Batch0254.cell2038, Batch0254.tau2038, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23200 | hy23200
        · have hs232001 : InSquare (-29/160) (49/160) (1/160) tau := by
            convert childLR hs23200 hx23200 hy23200 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx232001 | hx232001
          · rcases le_total tau.im (49/160 : ℝ) with hy232001 | hy232001
            · have hs2320010 : InSquare (-59/320) (97/320) (1/320) tau := by
                convert childLL hs232001 hx232001 hy232001 using 1 <;> norm_num
              exact Batch0253.cell2031.sound htau (by
                simp only [Batch0253.cell2031, Batch0253.tau2031, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320010 (by positivity) using 1 <;> norm_num)
            · have hs2320012 : InSquare (-59/320) (99/320) (1/320) tau := by
                convert childUL hs232001 hx232001 hy232001 using 1 <;> norm_num
              exact Batch0254.cell2033.sound htau (by
                simp only [Batch0254.cell2033, Batch0254.tau2033, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy232001 | hy232001
            · have hs2320011 : InSquare (-57/320) (97/320) (1/320) tau := by
                convert childLR hs232001 hx232001 hy232001 using 1 <;> norm_num
              exact Batch0254.cell2032.sound htau (by
                simp only [Batch0254.cell2032, Batch0254.tau2032, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320011 (by positivity) using 1 <;> norm_num)
            · have hs2320013 : InSquare (-57/320) (99/320) (1/320) tau := by
                convert childUR hs232001 hx232001 hy232001 using 1 <;> norm_num
              exact Batch0254.cell2034.sound htau (by
                simp only [Batch0254.cell2034, Batch0254.tau2034, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320013 (by positivity) using 1 <;> norm_num)
        · have hs232003 : InSquare (-29/160) (51/160) (1/160) tau := by
            convert childUR hs23200 hx23200 hy23200 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx232003 | hx232003
          · rcases le_total tau.im (51/160 : ℝ) with hy232003 | hy232003
            · have hs2320030 : InSquare (-59/320) (101/320) (1/320) tau := by
                convert childLL hs232003 hx232003 hy232003 using 1 <;> norm_num
              exact Batch0254.cell2039.sound htau (by
                simp only [Batch0254.cell2039, Batch0254.tau2039, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320030 (by positivity) using 1 <;> norm_num)
            · have hs2320032 : InSquare (-59/320) (103/320) (1/320) tau := by
                convert childUL hs232003 hx232003 hy232003 using 1 <;> norm_num
              exact Batch0255.cell2041.sound htau (by
                simp only [Batch0255.cell2041, Batch0255.tau2041, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy232003 | hy232003
            · have hs2320031 : InSquare (-57/320) (101/320) (1/320) tau := by
                convert childLR hs232003 hx232003 hy232003 using 1 <;> norm_num
              exact Batch0255.cell2040.sound htau (by
                simp only [Batch0255.cell2040, Batch0255.tau2040, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320031 (by positivity) using 1 <;> norm_num)
            · have hs2320033 : InSquare (-57/320) (103/320) (1/320) tau := by
                convert childUR hs232003 hx232003 hy232003 using 1 <;> norm_num
              exact Batch0255.cell2042.sound htau (by
                simp only [Batch0255.cell2042, Batch0255.tau2042, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320033 (by positivity) using 1 <;> norm_num)
    · have hs23202 : InSquare (-3/16) (27/80) (1/80) tau := by
        convert childUL hs hx2320 hy2320 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx23202 | hx23202
      · rcases le_total tau.im (27/80 : ℝ) with hy23202 | hy23202
        · have hs232020 : InSquare (-31/160) (53/160) (1/160) tau := by
            convert childLL hs23202 hx23202 hy23202 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx232020 | hx232020
          · rcases le_total tau.im (53/160 : ℝ) with hy232020 | hy232020
            · have hs2320200 : InSquare (-63/320) (21/64) (1/320) tau := by
                convert childLL hs232020 hx232020 hy232020 using 1 <;> norm_num
              exact Batch0256.cell2051.sound htau (by
                simp only [Batch0256.cell2051, Batch0256.tau2051, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320200 (by positivity) using 1 <;> norm_num)
            · have hs2320202 : InSquare (-63/320) (107/320) (1/320) tau := by
                convert childUL hs232020 hx232020 hy232020 using 1 <;> norm_num
              exact Batch0256.cell2053.sound htau (by
                simp only [Batch0256.cell2053, Batch0256.tau2053, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy232020 | hy232020
            · have hs2320201 : InSquare (-61/320) (21/64) (1/320) tau := by
                convert childLR hs232020 hx232020 hy232020 using 1 <;> norm_num
              exact Batch0256.cell2052.sound htau (by
                simp only [Batch0256.cell2052, Batch0256.tau2052, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320201 (by positivity) using 1 <;> norm_num)
            · have hs2320203 : InSquare (-61/320) (107/320) (1/320) tau := by
                convert childUR hs232020 hx232020 hy232020 using 1 <;> norm_num
              exact Batch0256.cell2054.sound htau (by
                simp only [Batch0256.cell2054, Batch0256.tau2054, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320203 (by positivity) using 1 <;> norm_num)
        · have hs232022 : InSquare (-31/160) (11/32) (1/160) tau := by
            convert childUL hs23202 hx23202 hy23202 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx232022 | hx232022
          · rcases le_total tau.im (11/32 : ℝ) with hy232022 | hy232022
            · have hs2320220 : InSquare (-63/320) (109/320) (1/320) tau := by
                convert childLL hs232022 hx232022 hy232022 using 1 <;> norm_num
              exact Batch0257.cell2059.sound htau (by
                simp only [Batch0257.cell2059, Batch0257.tau2059, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320220 (by positivity) using 1 <;> norm_num)
            · have hs2320222 : InSquare (-63/320) (111/320) (1/320) tau := by
                convert childUL hs232022 hx232022 hy232022 using 1 <;> norm_num
              rcases le_total tau.re (-63/320 : ℝ) with hx2320222 | hx2320222
              · rcases le_total tau.im (111/320 : ℝ) with hy2320222 | hy2320222
                · have hs23202220 : InSquare (-127/640) (221/640) (1/640) tau := by
                    convert childLL hs2320222 hx2320222 hy2320222 using 1 <;> norm_num
                  exact Batch0402.cell3219.sound htau (by
                    simp only [Batch0402.cell3219, Batch0402.tau3219, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202220 (by positivity) using 1 <;> norm_num)
                · have hs23202222 : InSquare (-127/640) (223/640) (1/640) tau := by
                    convert childUL hs2320222 hx2320222 hy2320222 using 1 <;> norm_num
                  exact Batch0402.cell3221.sound htau (by
                    simp only [Batch0402.cell3221, Batch0402.tau3221, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (111/320 : ℝ) with hy2320222 | hy2320222
                · have hs23202221 : InSquare (-25/128) (221/640) (1/640) tau := by
                    convert childLR hs2320222 hx2320222 hy2320222 using 1 <;> norm_num
                  exact Batch0402.cell3220.sound htau (by
                    simp only [Batch0402.cell3220, Batch0402.tau3220, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202221 (by positivity) using 1 <;> norm_num)
                · have hs23202223 : InSquare (-25/128) (223/640) (1/640) tau := by
                    convert childUR hs2320222 hx2320222 hy2320222 using 1 <;> norm_num
                  exact Batch0402.cell3222.sound htau (by
                    simp only [Batch0402.cell3222, Batch0402.tau3222, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232022 | hy232022
            · have hs2320221 : InSquare (-61/320) (109/320) (1/320) tau := by
                convert childLR hs232022 hx232022 hy232022 using 1 <;> norm_num
              exact Batch0257.cell2060.sound htau (by
                simp only [Batch0257.cell2060, Batch0257.tau2060, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320221 (by positivity) using 1 <;> norm_num)
            · have hs2320223 : InSquare (-61/320) (111/320) (1/320) tau := by
                convert childUR hs232022 hx232022 hy232022 using 1 <;> norm_num
              rcases le_total tau.re (-61/320 : ℝ) with hx2320223 | hx2320223
              · rcases le_total tau.im (111/320 : ℝ) with hy2320223 | hy2320223
                · have hs23202230 : InSquare (-123/640) (221/640) (1/640) tau := by
                    convert childLL hs2320223 hx2320223 hy2320223 using 1 <;> norm_num
                  exact Batch0402.cell3223.sound htau (by
                    simp only [Batch0402.cell3223, Batch0402.tau3223, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202230 (by positivity) using 1 <;> norm_num)
                · have hs23202232 : InSquare (-123/640) (223/640) (1/640) tau := by
                    convert childUL hs2320223 hx2320223 hy2320223 using 1 <;> norm_num
                  exact Batch0403.cell3225.sound htau (by
                    simp only [Batch0403.cell3225, Batch0403.tau3225, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (111/320 : ℝ) with hy2320223 | hy2320223
                · have hs23202231 : InSquare (-121/640) (221/640) (1/640) tau := by
                    convert childLR hs2320223 hx2320223 hy2320223 using 1 <;> norm_num
                  exact Batch0403.cell3224.sound htau (by
                    simp only [Batch0403.cell3224, Batch0403.tau3224, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202231 (by positivity) using 1 <;> norm_num)
                · have hs23202233 : InSquare (-121/640) (223/640) (1/640) tau := by
                    convert childUR hs2320223 hx2320223 hy2320223 using 1 <;> norm_num
                  exact Batch0403.cell3226.sound htau (by
                    simp only [Batch0403.cell3226, Batch0403.tau3226, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23202 | hy23202
        · have hs232021 : InSquare (-29/160) (53/160) (1/160) tau := by
            convert childLR hs23202 hx23202 hy23202 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx232021 | hx232021
          · rcases le_total tau.im (53/160 : ℝ) with hy232021 | hy232021
            · have hs2320210 : InSquare (-59/320) (21/64) (1/320) tau := by
                convert childLL hs232021 hx232021 hy232021 using 1 <;> norm_num
              exact Batch0256.cell2055.sound htau (by
                simp only [Batch0256.cell2055, Batch0256.tau2055, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320210 (by positivity) using 1 <;> norm_num)
            · have hs2320212 : InSquare (-59/320) (107/320) (1/320) tau := by
                convert childUL hs232021 hx232021 hy232021 using 1 <;> norm_num
              exact Batch0257.cell2057.sound htau (by
                simp only [Batch0257.cell2057, Batch0257.tau2057, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy232021 | hy232021
            · have hs2320211 : InSquare (-57/320) (21/64) (1/320) tau := by
                convert childLR hs232021 hx232021 hy232021 using 1 <;> norm_num
              exact Batch0257.cell2056.sound htau (by
                simp only [Batch0257.cell2056, Batch0257.tau2056, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320211 (by positivity) using 1 <;> norm_num)
            · have hs2320213 : InSquare (-57/320) (107/320) (1/320) tau := by
                convert childUR hs232021 hx232021 hy232021 using 1 <;> norm_num
              exact Batch0257.cell2058.sound htau (by
                simp only [Batch0257.cell2058, Batch0257.tau2058, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320213 (by positivity) using 1 <;> norm_num)
        · have hs232023 : InSquare (-29/160) (11/32) (1/160) tau := by
            convert childUR hs23202 hx23202 hy23202 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx232023 | hx232023
          · rcases le_total tau.im (11/32 : ℝ) with hy232023 | hy232023
            · have hs2320230 : InSquare (-59/320) (109/320) (1/320) tau := by
                convert childLL hs232023 hx232023 hy232023 using 1 <;> norm_num
              exact Batch0257.cell2061.sound htau (by
                simp only [Batch0257.cell2061, Batch0257.tau2061, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320230 (by positivity) using 1 <;> norm_num)
            · have hs2320232 : InSquare (-59/320) (111/320) (1/320) tau := by
                convert childUL hs232023 hx232023 hy232023 using 1 <;> norm_num
              exact Batch0257.cell2063.sound htau (by
                simp only [Batch0257.cell2063, Batch0257.tau2063, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232023 | hy232023
            · have hs2320231 : InSquare (-57/320) (109/320) (1/320) tau := by
                convert childLR hs232023 hx232023 hy232023 using 1 <;> norm_num
              exact Batch0257.cell2062.sound htau (by
                simp only [Batch0257.cell2062, Batch0257.tau2062, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320231 (by positivity) using 1 <;> norm_num)
            · have hs2320233 : InSquare (-57/320) (111/320) (1/320) tau := by
                convert childUR hs232023 hx232023 hy232023 using 1 <;> norm_num
              exact Batch0258.cell2064.sound htau (by
                simp only [Batch0258.cell2064, Batch0258.tau2064, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy2320 | hy2320
    · have hs23201 : InSquare (-13/80) (5/16) (1/80) tau := by
        convert childLR hs hx2320 hy2320 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx23201 | hx23201
      · rcases le_total tau.im (5/16 : ℝ) with hy23201 | hy23201
        · have hs232010 : InSquare (-27/160) (49/160) (1/160) tau := by
            convert childLL hs23201 hx23201 hy23201 using 1 <;> norm_num
          exact Batch0118.cell0946.sound htau (by
            simp only [Batch0118.cell0946, Batch0118.tau0946, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232010 (by positivity) using 1 <;> norm_num)
        · have hs232012 : InSquare (-27/160) (51/160) (1/160) tau := by
            convert childUL hs23201 hx23201 hy23201 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx232012 | hx232012
          · rcases le_total tau.im (51/160 : ℝ) with hy232012 | hy232012
            · have hs2320120 : InSquare (-11/64) (101/320) (1/320) tau := by
                convert childLL hs232012 hx232012 hy232012 using 1 <;> norm_num
              exact Batch0255.cell2043.sound htau (by
                simp only [Batch0255.cell2043, Batch0255.tau2043, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320120 (by positivity) using 1 <;> norm_num)
            · have hs2320122 : InSquare (-11/64) (103/320) (1/320) tau := by
                convert childUL hs232012 hx232012 hy232012 using 1 <;> norm_num
              exact Batch0255.cell2045.sound htau (by
                simp only [Batch0255.cell2045, Batch0255.tau2045, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy232012 | hy232012
            · have hs2320121 : InSquare (-53/320) (101/320) (1/320) tau := by
                convert childLR hs232012 hx232012 hy232012 using 1 <;> norm_num
              exact Batch0255.cell2044.sound htau (by
                simp only [Batch0255.cell2044, Batch0255.tau2044, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320121 (by positivity) using 1 <;> norm_num)
            · have hs2320123 : InSquare (-53/320) (103/320) (1/320) tau := by
                convert childUR hs232012 hx232012 hy232012 using 1 <;> norm_num
              exact Batch0255.cell2046.sound htau (by
                simp only [Batch0255.cell2046, Batch0255.tau2046, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23201 | hy23201
        · have hs232011 : InSquare (-5/32) (49/160) (1/160) tau := by
            convert childLR hs23201 hx23201 hy23201 using 1 <;> norm_num
          exact Batch0118.cell0947.sound htau (by
            simp only [Batch0118.cell0947, Batch0118.tau0947, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232011 (by positivity) using 1 <;> norm_num)
        · have hs232013 : InSquare (-5/32) (51/160) (1/160) tau := by
            convert childUR hs23201 hx23201 hy23201 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx232013 | hx232013
          · rcases le_total tau.im (51/160 : ℝ) with hy232013 | hy232013
            · have hs2320130 : InSquare (-51/320) (101/320) (1/320) tau := by
                convert childLL hs232013 hx232013 hy232013 using 1 <;> norm_num
              exact Batch0255.cell2047.sound htau (by
                simp only [Batch0255.cell2047, Batch0255.tau2047, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320130 (by positivity) using 1 <;> norm_num)
            · have hs2320132 : InSquare (-51/320) (103/320) (1/320) tau := by
                convert childUL hs232013 hx232013 hy232013 using 1 <;> norm_num
              exact Batch0256.cell2049.sound htau (by
                simp only [Batch0256.cell2049, Batch0256.tau2049, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy232013 | hy232013
            · have hs2320131 : InSquare (-49/320) (101/320) (1/320) tau := by
                convert childLR hs232013 hx232013 hy232013 using 1 <;> norm_num
              exact Batch0256.cell2048.sound htau (by
                simp only [Batch0256.cell2048, Batch0256.tau2048, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320131 (by positivity) using 1 <;> norm_num)
            · have hs2320133 : InSquare (-49/320) (103/320) (1/320) tau := by
                convert childUR hs232013 hx232013 hy232013 using 1 <;> norm_num
              exact Batch0256.cell2050.sound htau (by
                simp only [Batch0256.cell2050, Batch0256.tau2050, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320133 (by positivity) using 1 <;> norm_num)
    · have hs23203 : InSquare (-13/80) (27/80) (1/80) tau := by
        convert childUR hs hx2320 hy2320 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx23203 | hx23203
      · rcases le_total tau.im (27/80 : ℝ) with hy23203 | hy23203
        · have hs232030 : InSquare (-27/160) (53/160) (1/160) tau := by
            convert childLL hs23203 hx23203 hy23203 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx232030 | hx232030
          · rcases le_total tau.im (53/160 : ℝ) with hy232030 | hy232030
            · have hs2320300 : InSquare (-11/64) (21/64) (1/320) tau := by
                convert childLL hs232030 hx232030 hy232030 using 1 <;> norm_num
              exact Batch0258.cell2065.sound htau (by
                simp only [Batch0258.cell2065, Batch0258.tau2065, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320300 (by positivity) using 1 <;> norm_num)
            · have hs2320302 : InSquare (-11/64) (107/320) (1/320) tau := by
                convert childUL hs232030 hx232030 hy232030 using 1 <;> norm_num
              exact Batch0258.cell2067.sound htau (by
                simp only [Batch0258.cell2067, Batch0258.tau2067, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy232030 | hy232030
            · have hs2320301 : InSquare (-53/320) (21/64) (1/320) tau := by
                convert childLR hs232030 hx232030 hy232030 using 1 <;> norm_num
              exact Batch0258.cell2066.sound htau (by
                simp only [Batch0258.cell2066, Batch0258.tau2066, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320301 (by positivity) using 1 <;> norm_num)
            · have hs2320303 : InSquare (-53/320) (107/320) (1/320) tau := by
                convert childUR hs232030 hx232030 hy232030 using 1 <;> norm_num
              exact Batch0258.cell2068.sound htau (by
                simp only [Batch0258.cell2068, Batch0258.tau2068, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320303 (by positivity) using 1 <;> norm_num)
        · have hs232032 : InSquare (-27/160) (11/32) (1/160) tau := by
            convert childUL hs23203 hx23203 hy23203 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx232032 | hx232032
          · rcases le_total tau.im (11/32 : ℝ) with hy232032 | hy232032
            · have hs2320320 : InSquare (-11/64) (109/320) (1/320) tau := by
                convert childLL hs232032 hx232032 hy232032 using 1 <;> norm_num
              exact Batch0259.cell2073.sound htau (by
                simp only [Batch0259.cell2073, Batch0259.tau2073, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320320 (by positivity) using 1 <;> norm_num)
            · have hs2320322 : InSquare (-11/64) (111/320) (1/320) tau := by
                convert childUL hs232032 hx232032 hy232032 using 1 <;> norm_num
              exact Batch0259.cell2075.sound htau (by
                simp only [Batch0259.cell2075, Batch0259.tau2075, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232032 | hy232032
            · have hs2320321 : InSquare (-53/320) (109/320) (1/320) tau := by
                convert childLR hs232032 hx232032 hy232032 using 1 <;> norm_num
              exact Batch0259.cell2074.sound htau (by
                simp only [Batch0259.cell2074, Batch0259.tau2074, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320321 (by positivity) using 1 <;> norm_num)
            · have hs2320323 : InSquare (-53/320) (111/320) (1/320) tau := by
                convert childUR hs232032 hx232032 hy232032 using 1 <;> norm_num
              exact Batch0259.cell2076.sound htau (by
                simp only [Batch0259.cell2076, Batch0259.tau2076, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23203 | hy23203
        · have hs232031 : InSquare (-5/32) (53/160) (1/160) tau := by
            convert childLR hs23203 hx23203 hy23203 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx232031 | hx232031
          · rcases le_total tau.im (53/160 : ℝ) with hy232031 | hy232031
            · have hs2320310 : InSquare (-51/320) (21/64) (1/320) tau := by
                convert childLL hs232031 hx232031 hy232031 using 1 <;> norm_num
              exact Batch0258.cell2069.sound htau (by
                simp only [Batch0258.cell2069, Batch0258.tau2069, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320310 (by positivity) using 1 <;> norm_num)
            · have hs2320312 : InSquare (-51/320) (107/320) (1/320) tau := by
                convert childUL hs232031 hx232031 hy232031 using 1 <;> norm_num
              exact Batch0258.cell2071.sound htau (by
                simp only [Batch0258.cell2071, Batch0258.tau2071, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy232031 | hy232031
            · have hs2320311 : InSquare (-49/320) (21/64) (1/320) tau := by
                convert childLR hs232031 hx232031 hy232031 using 1 <;> norm_num
              exact Batch0258.cell2070.sound htau (by
                simp only [Batch0258.cell2070, Batch0258.tau2070, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320311 (by positivity) using 1 <;> norm_num)
            · have hs2320313 : InSquare (-49/320) (107/320) (1/320) tau := by
                convert childUR hs232031 hx232031 hy232031 using 1 <;> norm_num
              exact Batch0259.cell2072.sound htau (by
                simp only [Batch0259.cell2072, Batch0259.tau2072, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320313 (by positivity) using 1 <;> norm_num)
        · have hs232033 : InSquare (-5/32) (11/32) (1/160) tau := by
            convert childUR hs23203 hx23203 hy23203 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx232033 | hx232033
          · rcases le_total tau.im (11/32 : ℝ) with hy232033 | hy232033
            · have hs2320330 : InSquare (-51/320) (109/320) (1/320) tau := by
                convert childLL hs232033 hx232033 hy232033 using 1 <;> norm_num
              exact Batch0259.cell2077.sound htau (by
                simp only [Batch0259.cell2077, Batch0259.tau2077, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320330 (by positivity) using 1 <;> norm_num)
            · have hs2320332 : InSquare (-51/320) (111/320) (1/320) tau := by
                convert childUL hs232033 hx232033 hy232033 using 1 <;> norm_num
              exact Batch0259.cell2079.sound htau (by
                simp only [Batch0259.cell2079, Batch0259.tau2079, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232033 | hy232033
            · have hs2320331 : InSquare (-49/320) (109/320) (1/320) tau := by
                convert childLR hs232033 hx232033 hy232033 using 1 <;> norm_num
              exact Batch0259.cell2078.sound htau (by
                simp only [Batch0259.cell2078, Batch0259.tau2078, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320331 (by positivity) using 1 <;> norm_num)
            · have hs2320333 : InSquare (-49/320) (111/320) (1/320) tau := by
                convert childUR hs232033 hx232033 hy232033 using 1 <;> norm_num
              exact Batch0260.cell2080.sound htau (by
                simp only [Batch0260.cell2080, Batch0260.tau2080, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2320

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2321 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2321

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx2321 | hx2321
  · rcases le_total tau.im (13/40 : ℝ) with hy2321 | hy2321
    · have hs23210 : InSquare (-11/80) (5/16) (1/80) tau := by
        convert childLL hs hx2321 hy2321 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx23210 | hx23210
      · rcases le_total tau.im (5/16 : ℝ) with hy23210 | hy23210
        · have hs232100 : InSquare (-23/160) (49/160) (1/160) tau := by
            convert childLL hs23210 hx23210 hy23210 using 1 <;> norm_num
          exact Batch0118.cell0948.sound htau (by
            simp only [Batch0118.cell0948, Batch0118.tau0948, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232100 (by positivity) using 1 <;> norm_num)
        · have hs232102 : InSquare (-23/160) (51/160) (1/160) tau := by
            convert childUL hs23210 hx23210 hy23210 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx232102 | hx232102
          · rcases le_total tau.im (51/160 : ℝ) with hy232102 | hy232102
            · have hs2321020 : InSquare (-47/320) (101/320) (1/320) tau := by
                convert childLL hs232102 hx232102 hy232102 using 1 <;> norm_num
              exact Batch0260.cell2081.sound htau (by
                simp only [Batch0260.cell2081, Batch0260.tau2081, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321020 (by positivity) using 1 <;> norm_num)
            · have hs2321022 : InSquare (-47/320) (103/320) (1/320) tau := by
                convert childUL hs232102 hx232102 hy232102 using 1 <;> norm_num
              exact Batch0260.cell2083.sound htau (by
                simp only [Batch0260.cell2083, Batch0260.tau2083, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy232102 | hy232102
            · have hs2321021 : InSquare (-9/64) (101/320) (1/320) tau := by
                convert childLR hs232102 hx232102 hy232102 using 1 <;> norm_num
              exact Batch0260.cell2082.sound htau (by
                simp only [Batch0260.cell2082, Batch0260.tau2082, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321021 (by positivity) using 1 <;> norm_num)
            · have hs2321023 : InSquare (-9/64) (103/320) (1/320) tau := by
                convert childUR hs232102 hx232102 hy232102 using 1 <;> norm_num
              exact Batch0260.cell2084.sound htau (by
                simp only [Batch0260.cell2084, Batch0260.tau2084, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23210 | hy23210
        · have hs232101 : InSquare (-21/160) (49/160) (1/160) tau := by
            convert childLR hs23210 hx23210 hy23210 using 1 <;> norm_num
          exact Batch0118.cell0949.sound htau (by
            simp only [Batch0118.cell0949, Batch0118.tau0949, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232101 (by positivity) using 1 <;> norm_num)
        · have hs232103 : InSquare (-21/160) (51/160) (1/160) tau := by
            convert childUR hs23210 hx23210 hy23210 using 1 <;> norm_num
          exact Batch0118.cell0950.sound htau (by
            simp only [Batch0118.cell0950, Batch0118.tau0950, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232103 (by positivity) using 1 <;> norm_num)
    · have hs23212 : InSquare (-11/80) (27/80) (1/80) tau := by
        convert childUL hs hx2321 hy2321 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx23212 | hx23212
      · rcases le_total tau.im (27/80 : ℝ) with hy23212 | hy23212
        · have hs232120 : InSquare (-23/160) (53/160) (1/160) tau := by
            convert childLL hs23212 hx23212 hy23212 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx232120 | hx232120
          · rcases le_total tau.im (53/160 : ℝ) with hy232120 | hy232120
            · have hs2321200 : InSquare (-47/320) (21/64) (1/320) tau := by
                convert childLL hs232120 hx232120 hy232120 using 1 <;> norm_num
              exact Batch0260.cell2085.sound htau (by
                simp only [Batch0260.cell2085, Batch0260.tau2085, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321200 (by positivity) using 1 <;> norm_num)
            · have hs2321202 : InSquare (-47/320) (107/320) (1/320) tau := by
                convert childUL hs232120 hx232120 hy232120 using 1 <;> norm_num
              exact Batch0260.cell2087.sound htau (by
                simp only [Batch0260.cell2087, Batch0260.tau2087, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy232120 | hy232120
            · have hs2321201 : InSquare (-9/64) (21/64) (1/320) tau := by
                convert childLR hs232120 hx232120 hy232120 using 1 <;> norm_num
              exact Batch0260.cell2086.sound htau (by
                simp only [Batch0260.cell2086, Batch0260.tau2086, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321201 (by positivity) using 1 <;> norm_num)
            · have hs2321203 : InSquare (-9/64) (107/320) (1/320) tau := by
                convert childUR hs232120 hx232120 hy232120 using 1 <;> norm_num
              exact Batch0261.cell2088.sound htau (by
                simp only [Batch0261.cell2088, Batch0261.tau2088, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321203 (by positivity) using 1 <;> norm_num)
        · have hs232122 : InSquare (-23/160) (11/32) (1/160) tau := by
            convert childUL hs23212 hx23212 hy23212 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx232122 | hx232122
          · rcases le_total tau.im (11/32 : ℝ) with hy232122 | hy232122
            · have hs2321220 : InSquare (-47/320) (109/320) (1/320) tau := by
                convert childLL hs232122 hx232122 hy232122 using 1 <;> norm_num
              exact Batch0261.cell2093.sound htau (by
                simp only [Batch0261.cell2093, Batch0261.tau2093, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321220 (by positivity) using 1 <;> norm_num)
            · have hs2321222 : InSquare (-47/320) (111/320) (1/320) tau := by
                convert childUL hs232122 hx232122 hy232122 using 1 <;> norm_num
              exact Batch0261.cell2095.sound htau (by
                simp only [Batch0261.cell2095, Batch0261.tau2095, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232122 | hy232122
            · have hs2321221 : InSquare (-9/64) (109/320) (1/320) tau := by
                convert childLR hs232122 hx232122 hy232122 using 1 <;> norm_num
              exact Batch0261.cell2094.sound htau (by
                simp only [Batch0261.cell2094, Batch0261.tau2094, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321221 (by positivity) using 1 <;> norm_num)
            · have hs2321223 : InSquare (-9/64) (111/320) (1/320) tau := by
                convert childUR hs232122 hx232122 hy232122 using 1 <;> norm_num
              exact Batch0262.cell2096.sound htau (by
                simp only [Batch0262.cell2096, Batch0262.tau2096, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23212 | hy23212
        · have hs232121 : InSquare (-21/160) (53/160) (1/160) tau := by
            convert childLR hs23212 hx23212 hy23212 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx232121 | hx232121
          · rcases le_total tau.im (53/160 : ℝ) with hy232121 | hy232121
            · have hs2321210 : InSquare (-43/320) (21/64) (1/320) tau := by
                convert childLL hs232121 hx232121 hy232121 using 1 <;> norm_num
              exact Batch0261.cell2089.sound htau (by
                simp only [Batch0261.cell2089, Batch0261.tau2089, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321210 (by positivity) using 1 <;> norm_num)
            · have hs2321212 : InSquare (-43/320) (107/320) (1/320) tau := by
                convert childUL hs232121 hx232121 hy232121 using 1 <;> norm_num
              exact Batch0261.cell2091.sound htau (by
                simp only [Batch0261.cell2091, Batch0261.tau2091, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy232121 | hy232121
            · have hs2321211 : InSquare (-41/320) (21/64) (1/320) tau := by
                convert childLR hs232121 hx232121 hy232121 using 1 <;> norm_num
              exact Batch0261.cell2090.sound htau (by
                simp only [Batch0261.cell2090, Batch0261.tau2090, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321211 (by positivity) using 1 <;> norm_num)
            · have hs2321213 : InSquare (-41/320) (107/320) (1/320) tau := by
                convert childUR hs232121 hx232121 hy232121 using 1 <;> norm_num
              exact Batch0261.cell2092.sound htau (by
                simp only [Batch0261.cell2092, Batch0261.tau2092, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321213 (by positivity) using 1 <;> norm_num)
        · have hs232123 : InSquare (-21/160) (11/32) (1/160) tau := by
            convert childUR hs23212 hx23212 hy23212 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx232123 | hx232123
          · rcases le_total tau.im (11/32 : ℝ) with hy232123 | hy232123
            · have hs2321230 : InSquare (-43/320) (109/320) (1/320) tau := by
                convert childLL hs232123 hx232123 hy232123 using 1 <;> norm_num
              exact Batch0262.cell2097.sound htau (by
                simp only [Batch0262.cell2097, Batch0262.tau2097, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321230 (by positivity) using 1 <;> norm_num)
            · have hs2321232 : InSquare (-43/320) (111/320) (1/320) tau := by
                convert childUL hs232123 hx232123 hy232123 using 1 <;> norm_num
              exact Batch0262.cell2099.sound htau (by
                simp only [Batch0262.cell2099, Batch0262.tau2099, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232123 | hy232123
            · have hs2321231 : InSquare (-41/320) (109/320) (1/320) tau := by
                convert childLR hs232123 hx232123 hy232123 using 1 <;> norm_num
              exact Batch0262.cell2098.sound htau (by
                simp only [Batch0262.cell2098, Batch0262.tau2098, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321231 (by positivity) using 1 <;> norm_num)
            · have hs2321233 : InSquare (-41/320) (111/320) (1/320) tau := by
                convert childUR hs232123 hx232123 hy232123 using 1 <;> norm_num
              exact Batch0262.cell2100.sound htau (by
                simp only [Batch0262.cell2100, Batch0262.tau2100, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy2321 | hy2321
    · have hs23211 : InSquare (-9/80) (5/16) (1/80) tau := by
        convert childLR hs hx2321 hy2321 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx23211 | hx23211
      · rcases le_total tau.im (5/16 : ℝ) with hy23211 | hy23211
        · have hs232110 : InSquare (-19/160) (49/160) (1/160) tau := by
            convert childLL hs23211 hx23211 hy23211 using 1 <;> norm_num
          exact Batch0118.cell0951.sound htau (by
            simp only [Batch0118.cell0951, Batch0118.tau0951, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232110 (by positivity) using 1 <;> norm_num)
        · have hs232112 : InSquare (-19/160) (51/160) (1/160) tau := by
            convert childUL hs23211 hx23211 hy23211 using 1 <;> norm_num
          exact Batch0119.cell0953.sound htau (by
            simp only [Batch0119.cell0953, Batch0119.tau0953, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23211 | hy23211
        · have hs232111 : InSquare (-17/160) (49/160) (1/160) tau := by
            convert childLR hs23211 hx23211 hy23211 using 1 <;> norm_num
          exact Batch0119.cell0952.sound htau (by
            simp only [Batch0119.cell0952, Batch0119.tau0952, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232111 (by positivity) using 1 <;> norm_num)
        · have hs232113 : InSquare (-17/160) (51/160) (1/160) tau := by
            convert childUR hs23211 hx23211 hy23211 using 1 <;> norm_num
          exact Batch0119.cell0954.sound htau (by
            simp only [Batch0119.cell0954, Batch0119.tau0954, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232113 (by positivity) using 1 <;> norm_num)
    · have hs23213 : InSquare (-9/80) (27/80) (1/80) tau := by
        convert childUR hs hx2321 hy2321 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx23213 | hx23213
      · rcases le_total tau.im (27/80 : ℝ) with hy23213 | hy23213
        · have hs232130 : InSquare (-19/160) (53/160) (1/160) tau := by
            convert childLL hs23213 hx23213 hy23213 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx232130 | hx232130
          · rcases le_total tau.im (53/160 : ℝ) with hy232130 | hy232130
            · have hs2321300 : InSquare (-39/320) (21/64) (1/320) tau := by
                convert childLL hs232130 hx232130 hy232130 using 1 <;> norm_num
              exact Batch0262.cell2101.sound htau (by
                simp only [Batch0262.cell2101, Batch0262.tau2101, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321300 (by positivity) using 1 <;> norm_num)
            · have hs2321302 : InSquare (-39/320) (107/320) (1/320) tau := by
                convert childUL hs232130 hx232130 hy232130 using 1 <;> norm_num
              exact Batch0262.cell2103.sound htau (by
                simp only [Batch0262.cell2103, Batch0262.tau2103, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy232130 | hy232130
            · have hs2321301 : InSquare (-37/320) (21/64) (1/320) tau := by
                convert childLR hs232130 hx232130 hy232130 using 1 <;> norm_num
              exact Batch0262.cell2102.sound htau (by
                simp only [Batch0262.cell2102, Batch0262.tau2102, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321301 (by positivity) using 1 <;> norm_num)
            · have hs2321303 : InSquare (-37/320) (107/320) (1/320) tau := by
                convert childUR hs232130 hx232130 hy232130 using 1 <;> norm_num
              exact Batch0263.cell2104.sound htau (by
                simp only [Batch0263.cell2104, Batch0263.tau2104, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321303 (by positivity) using 1 <;> norm_num)
        · have hs232132 : InSquare (-19/160) (11/32) (1/160) tau := by
            convert childUL hs23213 hx23213 hy23213 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx232132 | hx232132
          · rcases le_total tau.im (11/32 : ℝ) with hy232132 | hy232132
            · have hs2321320 : InSquare (-39/320) (109/320) (1/320) tau := by
                convert childLL hs232132 hx232132 hy232132 using 1 <;> norm_num
              exact Batch0263.cell2105.sound htau (by
                simp only [Batch0263.cell2105, Batch0263.tau2105, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321320 (by positivity) using 1 <;> norm_num)
            · have hs2321322 : InSquare (-39/320) (111/320) (1/320) tau := by
                convert childUL hs232132 hx232132 hy232132 using 1 <;> norm_num
              exact Batch0263.cell2107.sound htau (by
                simp only [Batch0263.cell2107, Batch0263.tau2107, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232132 | hy232132
            · have hs2321321 : InSquare (-37/320) (109/320) (1/320) tau := by
                convert childLR hs232132 hx232132 hy232132 using 1 <;> norm_num
              exact Batch0263.cell2106.sound htau (by
                simp only [Batch0263.cell2106, Batch0263.tau2106, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321321 (by positivity) using 1 <;> norm_num)
            · have hs2321323 : InSquare (-37/320) (111/320) (1/320) tau := by
                convert childUR hs232132 hx232132 hy232132 using 1 <;> norm_num
              exact Batch0263.cell2108.sound htau (by
                simp only [Batch0263.cell2108, Batch0263.tau2108, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23213 | hy23213
        · have hs232131 : InSquare (-17/160) (53/160) (1/160) tau := by
            convert childLR hs23213 hx23213 hy23213 using 1 <;> norm_num
          exact Batch0119.cell0955.sound htau (by
            simp only [Batch0119.cell0955, Batch0119.tau0955, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232131 (by positivity) using 1 <;> norm_num)
        · have hs232133 : InSquare (-17/160) (11/32) (1/160) tau := by
            convert childUR hs23213 hx23213 hy23213 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx232133 | hx232133
          · rcases le_total tau.im (11/32 : ℝ) with hy232133 | hy232133
            · have hs2321330 : InSquare (-7/64) (109/320) (1/320) tau := by
                convert childLL hs232133 hx232133 hy232133 using 1 <;> norm_num
              exact Batch0263.cell2109.sound htau (by
                simp only [Batch0263.cell2109, Batch0263.tau2109, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321330 (by positivity) using 1 <;> norm_num)
            · have hs2321332 : InSquare (-7/64) (111/320) (1/320) tau := by
                convert childUL hs232133 hx232133 hy232133 using 1 <;> norm_num
              exact Batch0263.cell2111.sound htau (by
                simp only [Batch0263.cell2111, Batch0263.tau2111, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232133 | hy232133
            · have hs2321331 : InSquare (-33/320) (109/320) (1/320) tau := by
                convert childLR hs232133 hx232133 hy232133 using 1 <;> norm_num
              exact Batch0263.cell2110.sound htau (by
                simp only [Batch0263.cell2110, Batch0263.tau2110, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321331 (by positivity) using 1 <;> norm_num)
            · have hs2321333 : InSquare (-33/320) (111/320) (1/320) tau := by
                convert childUR hs232133 hx232133 hy232133 using 1 <;> norm_num
              exact Batch0264.cell2112.sound htau (by
                simp only [Batch0264.cell2112, Batch0264.tau2112, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2321

end


