-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage1011__11
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage1011__11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:13:56.014361+00:00
-- url     : https://prove2.me/theorems/87bc5fb0-6752-4205-8eac-5bee34948f4e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1011 (+10 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1012, GeneralCK.Certifi…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1011 (+10 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1012, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1013, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1020, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1021, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1022, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1023, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1030, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1031, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1032, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1033)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1011 (+10 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1012, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1013, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1020, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1021, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1022, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1023, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1030, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1031, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1032, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1033)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1011 (+10 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1012, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1013, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1020, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1021, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1022, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1023, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1030, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1031, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1032, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1033) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1011 (+10 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1012, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1013, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1020, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1021, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1022, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1023, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1030, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1031, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1032, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1033).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0206
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0391
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0392
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0393
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0394
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0395
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0396
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0397
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0073
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0074
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0207
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0208
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0209
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0210
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0211
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0212
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0213
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0214
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0215
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0216
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0217
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0398
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0015
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0016
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0075
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0017
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0076
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0077
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0078
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0079
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0018
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0080

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1011 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1011

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_10110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/80) (-31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/20)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/16) (-31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/40)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_101130 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (29/160) (-59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/40)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_101131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/160) (-59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/16)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1011201 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (51/320) (-119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-5/32)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1011210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (53/320) (-119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/80)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1011211 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/64) (-119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/160)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1011330 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (61/320) (-23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/16)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1011331 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/320) (-23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/160)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1011333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/320) (-113/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/160)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10112000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (97/640) (-239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/20)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10112001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (99/640) (-239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-49/320)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10112120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (21/128) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/80)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10112121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (107/640) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-53/320)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10112130 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (109/640) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/160)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10112131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/640) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/64)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10112133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/640) (-233/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/64)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10113201 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/128) (-231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-57/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10113210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (117/640) (-231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/160)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10113211 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (119/640) (-231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-59/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10113213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (119/640) (-229/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-59/320)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10113321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (123/640) (-227/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (61/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-61/320)]
  have himSq : (113/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+113/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (-3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx1011 | hx1011
  · rcases le_total tau.im (-3/8 : ℝ) with hy1011 | hy1011
    · have hs10110 : InSquare (13/80) (-31/80) (1/80) tau := by
        convert childLL hs hx1011 hy1011 using 1 <;> norm_num
      exact (outside_10110 htau hs10110).elim
    · have hs10112 : InSquare (13/80) (-29/80) (1/80) tau := by
        convert childUL hs hx1011 hy1011 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx10112 | hx10112
      · rcases le_total tau.im (-29/80 : ℝ) with hy10112 | hy10112
        · have hs101120 : InSquare (5/32) (-59/160) (1/160) tau := by
            convert childLL hs10112 hx10112 hy10112 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx101120 | hx101120
          · rcases le_total tau.im (-59/160 : ℝ) with hy101120 | hy101120
            · have hs1011200 : InSquare (49/320) (-119/320) (1/320) tau := by
                convert childLL hs101120 hx101120 hy101120 using 1 <;> norm_num
              rcases le_total tau.re (49/320 : ℝ) with hx1011200 | hx1011200
              · rcases le_total tau.im (-119/320 : ℝ) with hy1011200 | hy1011200
                · have hs10112000 : InSquare (97/640) (-239/640) (1/640) tau := by
                    convert childLL hs1011200 hx1011200 hy1011200 using 1 <;> norm_num
                  exact (outside_10112000 htau hs10112000).elim
                · have hs10112002 : InSquare (97/640) (-237/640) (1/640) tau := by
                    convert childUL hs1011200 hx1011200 hy1011200 using 1 <;> norm_num
                  exact Batch0391.cell3133.sound htau (by
                    simp only [Batch0391.cell3133, Batch0391.tau3133, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1011200 | hy1011200
                · have hs10112001 : InSquare (99/640) (-239/640) (1/640) tau := by
                    convert childLR hs1011200 hx1011200 hy1011200 using 1 <;> norm_num
                  exact (outside_10112001 htau hs10112001).elim
                · have hs10112003 : InSquare (99/640) (-237/640) (1/640) tau := by
                    convert childUR hs1011200 hx1011200 hy1011200 using 1 <;> norm_num
                  exact Batch0391.cell3134.sound htau (by
                    simp only [Batch0391.cell3134, Batch0391.tau3134, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112003 (by positivity) using 1 <;> norm_num)
            · have hs1011202 : InSquare (49/320) (-117/320) (1/320) tau := by
                convert childUL hs101120 hx101120 hy101120 using 1 <;> norm_num
              rcases le_total tau.re (49/320 : ℝ) with hx1011202 | hx1011202
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011202 | hy1011202
                · have hs10112020 : InSquare (97/640) (-47/128) (1/640) tau := by
                    convert childLL hs1011202 hx1011202 hy1011202 using 1 <;> norm_num
                  exact Batch0391.cell3135.sound htau (by
                    simp only [Batch0391.cell3135, Batch0391.tau3135, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112020 (by positivity) using 1 <;> norm_num)
                · have hs10112022 : InSquare (97/640) (-233/640) (1/640) tau := by
                    convert childUL hs1011202 hx1011202 hy1011202 using 1 <;> norm_num
                  exact Batch0392.cell3137.sound htau (by
                    simp only [Batch0392.cell3137, Batch0392.tau3137, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011202 | hy1011202
                · have hs10112021 : InSquare (99/640) (-47/128) (1/640) tau := by
                    convert childLR hs1011202 hx1011202 hy1011202 using 1 <;> norm_num
                  exact Batch0392.cell3136.sound htau (by
                    simp only [Batch0392.cell3136, Batch0392.tau3136, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112021 (by positivity) using 1 <;> norm_num)
                · have hs10112023 : InSquare (99/640) (-233/640) (1/640) tau := by
                    convert childUR hs1011202 hx1011202 hy1011202 using 1 <;> norm_num
                  exact Batch0392.cell3138.sound htau (by
                    simp only [Batch0392.cell3138, Batch0392.tau3138, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy101120 | hy101120
            · have hs1011201 : InSquare (51/320) (-119/320) (1/320) tau := by
                convert childLR hs101120 hx101120 hy101120 using 1 <;> norm_num
              exact (outside_1011201 htau hs1011201).elim
            · have hs1011203 : InSquare (51/320) (-117/320) (1/320) tau := by
                convert childUR hs101120 hx101120 hy101120 using 1 <;> norm_num
              rcases le_total tau.re (51/320 : ℝ) with hx1011203 | hx1011203
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011203 | hy1011203
                · have hs10112030 : InSquare (101/640) (-47/128) (1/640) tau := by
                    convert childLL hs1011203 hx1011203 hy1011203 using 1 <;> norm_num
                  exact Batch0392.cell3139.sound htau (by
                    simp only [Batch0392.cell3139, Batch0392.tau3139, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112030 (by positivity) using 1 <;> norm_num)
                · have hs10112032 : InSquare (101/640) (-233/640) (1/640) tau := by
                    convert childUL hs1011203 hx1011203 hy1011203 using 1 <;> norm_num
                  exact Batch0392.cell3141.sound htau (by
                    simp only [Batch0392.cell3141, Batch0392.tau3141, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011203 | hy1011203
                · have hs10112031 : InSquare (103/640) (-47/128) (1/640) tau := by
                    convert childLR hs1011203 hx1011203 hy1011203 using 1 <;> norm_num
                  exact Batch0392.cell3140.sound htau (by
                    simp only [Batch0392.cell3140, Batch0392.tau3140, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112031 (by positivity) using 1 <;> norm_num)
                · have hs10112033 : InSquare (103/640) (-233/640) (1/640) tau := by
                    convert childUR hs1011203 hx1011203 hy1011203 using 1 <;> norm_num
                  exact Batch0392.cell3142.sound htau (by
                    simp only [Batch0392.cell3142, Batch0392.tau3142, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112033 (by positivity) using 1 <;> norm_num)
        · have hs101122 : InSquare (5/32) (-57/160) (1/160) tau := by
            convert childUL hs10112 hx10112 hy10112 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx101122 | hx101122
          · rcases le_total tau.im (-57/160 : ℝ) with hy101122 | hy101122
            · have hs1011220 : InSquare (49/320) (-23/64) (1/320) tau := by
                convert childLL hs101122 hx101122 hy101122 using 1 <;> norm_num
              rcases le_total tau.re (49/320 : ℝ) with hx1011220 | hx1011220
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011220 | hy1011220
                · have hs10112200 : InSquare (97/640) (-231/640) (1/640) tau := by
                    convert childLL hs1011220 hx1011220 hy1011220 using 1 <;> norm_num
                  exact Batch0393.cell3146.sound htau (by
                    simp only [Batch0393.cell3146, Batch0393.tau3146, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112200 (by positivity) using 1 <;> norm_num)
                · have hs10112202 : InSquare (97/640) (-229/640) (1/640) tau := by
                    convert childUL hs1011220 hx1011220 hy1011220 using 1 <;> norm_num
                  exact Batch0393.cell3148.sound htau (by
                    simp only [Batch0393.cell3148, Batch0393.tau3148, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011220 | hy1011220
                · have hs10112201 : InSquare (99/640) (-231/640) (1/640) tau := by
                    convert childLR hs1011220 hx1011220 hy1011220 using 1 <;> norm_num
                  exact Batch0393.cell3147.sound htau (by
                    simp only [Batch0393.cell3147, Batch0393.tau3147, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112201 (by positivity) using 1 <;> norm_num)
                · have hs10112203 : InSquare (99/640) (-229/640) (1/640) tau := by
                    convert childUR hs1011220 hx1011220 hy1011220 using 1 <;> norm_num
                  exact Batch0393.cell3149.sound htau (by
                    simp only [Batch0393.cell3149, Batch0393.tau3149, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112203 (by positivity) using 1 <;> norm_num)
            · have hs1011222 : InSquare (49/320) (-113/320) (1/320) tau := by
                convert childUL hs101122 hx101122 hy101122 using 1 <;> norm_num
              exact Batch0206.cell1648.sound htau (by
                simp only [Batch0206.cell1648, Batch0206.tau1648, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1011222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101122 | hy101122
            · have hs1011221 : InSquare (51/320) (-23/64) (1/320) tau := by
                convert childLR hs101122 hx101122 hy101122 using 1 <;> norm_num
              rcases le_total tau.re (51/320 : ℝ) with hx1011221 | hx1011221
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011221 | hy1011221
                · have hs10112210 : InSquare (101/640) (-231/640) (1/640) tau := by
                    convert childLL hs1011221 hx1011221 hy1011221 using 1 <;> norm_num
                  exact Batch0393.cell3150.sound htau (by
                    simp only [Batch0393.cell3150, Batch0393.tau3150, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112210 (by positivity) using 1 <;> norm_num)
                · have hs10112212 : InSquare (101/640) (-229/640) (1/640) tau := by
                    convert childUL hs1011221 hx1011221 hy1011221 using 1 <;> norm_num
                  exact Batch0394.cell3152.sound htau (by
                    simp only [Batch0394.cell3152, Batch0394.tau3152, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011221 | hy1011221
                · have hs10112211 : InSquare (103/640) (-231/640) (1/640) tau := by
                    convert childLR hs1011221 hx1011221 hy1011221 using 1 <;> norm_num
                  exact Batch0393.cell3151.sound htau (by
                    simp only [Batch0393.cell3151, Batch0393.tau3151, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112211 (by positivity) using 1 <;> norm_num)
                · have hs10112213 : InSquare (103/640) (-229/640) (1/640) tau := by
                    convert childUR hs1011221 hx1011221 hy1011221 using 1 <;> norm_num
                  exact Batch0394.cell3153.sound htau (by
                    simp only [Batch0394.cell3153, Batch0394.tau3153, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112213 (by positivity) using 1 <;> norm_num)
            · have hs1011223 : InSquare (51/320) (-113/320) (1/320) tau := by
                convert childUR hs101122 hx101122 hy101122 using 1 <;> norm_num
              exact Batch0206.cell1649.sound htau (by
                simp only [Batch0206.cell1649, Batch0206.tau1649, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1011223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy10112 | hy10112
        · have hs101121 : InSquare (27/160) (-59/160) (1/160) tau := by
            convert childLR hs10112 hx10112 hy10112 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx101121 | hx101121
          · rcases le_total tau.im (-59/160 : ℝ) with hy101121 | hy101121
            · have hs1011210 : InSquare (53/320) (-119/320) (1/320) tau := by
                convert childLL hs101121 hx101121 hy101121 using 1 <;> norm_num
              exact (outside_1011210 htau hs1011210).elim
            · have hs1011212 : InSquare (53/320) (-117/320) (1/320) tau := by
                convert childUL hs101121 hx101121 hy101121 using 1 <;> norm_num
              rcases le_total tau.re (53/320 : ℝ) with hx1011212 | hx1011212
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011212 | hy1011212
                · have hs10112120 : InSquare (21/128) (-47/128) (1/640) tau := by
                    convert childLL hs1011212 hx1011212 hy1011212 using 1 <;> norm_num
                  exact (outside_10112120 htau hs10112120).elim
                · have hs10112122 : InSquare (21/128) (-233/640) (1/640) tau := by
                    convert childUL hs1011212 hx1011212 hy1011212 using 1 <;> norm_num
                  exact Batch0392.cell3143.sound htau (by
                    simp only [Batch0392.cell3143, Batch0392.tau3143, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011212 | hy1011212
                · have hs10112121 : InSquare (107/640) (-47/128) (1/640) tau := by
                    convert childLR hs1011212 hx1011212 hy1011212 using 1 <;> norm_num
                  exact (outside_10112121 htau hs10112121).elim
                · have hs10112123 : InSquare (107/640) (-233/640) (1/640) tau := by
                    convert childUR hs1011212 hx1011212 hy1011212 using 1 <;> norm_num
                  exact Batch0393.cell3144.sound htau (by
                    simp only [Batch0393.cell3144, Batch0393.tau3144, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy101121 | hy101121
            · have hs1011211 : InSquare (11/64) (-119/320) (1/320) tau := by
                convert childLR hs101121 hx101121 hy101121 using 1 <;> norm_num
              exact (outside_1011211 htau hs1011211).elim
            · have hs1011213 : InSquare (11/64) (-117/320) (1/320) tau := by
                convert childUR hs101121 hx101121 hy101121 using 1 <;> norm_num
              rcases le_total tau.re (11/64 : ℝ) with hx1011213 | hx1011213
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011213 | hy1011213
                · have hs10112130 : InSquare (109/640) (-47/128) (1/640) tau := by
                    convert childLL hs1011213 hx1011213 hy1011213 using 1 <;> norm_num
                  exact (outside_10112130 htau hs10112130).elim
                · have hs10112132 : InSquare (109/640) (-233/640) (1/640) tau := by
                    convert childUL hs1011213 hx1011213 hy1011213 using 1 <;> norm_num
                  exact Batch0393.cell3145.sound htau (by
                    simp only [Batch0393.cell3145, Batch0393.tau3145, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011213 | hy1011213
                · have hs10112131 : InSquare (111/640) (-47/128) (1/640) tau := by
                    convert childLR hs1011213 hx1011213 hy1011213 using 1 <;> norm_num
                  exact (outside_10112131 htau hs10112131).elim
                · have hs10112133 : InSquare (111/640) (-233/640) (1/640) tau := by
                    convert childUR hs1011213 hx1011213 hy1011213 using 1 <;> norm_num
                  exact (outside_10112133 htau hs10112133).elim
        · have hs101123 : InSquare (27/160) (-57/160) (1/160) tau := by
            convert childUR hs10112 hx10112 hy10112 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx101123 | hx101123
          · rcases le_total tau.im (-57/160 : ℝ) with hy101123 | hy101123
            · have hs1011230 : InSquare (53/320) (-23/64) (1/320) tau := by
                convert childLL hs101123 hx101123 hy101123 using 1 <;> norm_num
              rcases le_total tau.re (53/320 : ℝ) with hx1011230 | hx1011230
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011230 | hy1011230
                · have hs10112300 : InSquare (21/128) (-231/640) (1/640) tau := by
                    convert childLL hs1011230 hx1011230 hy1011230 using 1 <;> norm_num
                  exact Batch0394.cell3154.sound htau (by
                    simp only [Batch0394.cell3154, Batch0394.tau3154, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112300 (by positivity) using 1 <;> norm_num)
                · have hs10112302 : InSquare (21/128) (-229/640) (1/640) tau := by
                    convert childUL hs1011230 hx1011230 hy1011230 using 1 <;> norm_num
                  exact Batch0394.cell3156.sound htau (by
                    simp only [Batch0394.cell3156, Batch0394.tau3156, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011230 | hy1011230
                · have hs10112301 : InSquare (107/640) (-231/640) (1/640) tau := by
                    convert childLR hs1011230 hx1011230 hy1011230 using 1 <;> norm_num
                  exact Batch0394.cell3155.sound htau (by
                    simp only [Batch0394.cell3155, Batch0394.tau3155, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112301 (by positivity) using 1 <;> norm_num)
                · have hs10112303 : InSquare (107/640) (-229/640) (1/640) tau := by
                    convert childUR hs1011230 hx1011230 hy1011230 using 1 <;> norm_num
                  exact Batch0394.cell3157.sound htau (by
                    simp only [Batch0394.cell3157, Batch0394.tau3157, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112303 (by positivity) using 1 <;> norm_num)
            · have hs1011232 : InSquare (53/320) (-113/320) (1/320) tau := by
                convert childUL hs101123 hx101123 hy101123 using 1 <;> norm_num
              exact Batch0206.cell1650.sound htau (by
                simp only [Batch0206.cell1650, Batch0206.tau1650, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1011232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101123 | hy101123
            · have hs1011231 : InSquare (11/64) (-23/64) (1/320) tau := by
                convert childLR hs101123 hx101123 hy101123 using 1 <;> norm_num
              rcases le_total tau.re (11/64 : ℝ) with hx1011231 | hx1011231
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011231 | hy1011231
                · have hs10112310 : InSquare (109/640) (-231/640) (1/640) tau := by
                    convert childLL hs1011231 hx1011231 hy1011231 using 1 <;> norm_num
                  exact Batch0394.cell3158.sound htau (by
                    simp only [Batch0394.cell3158, Batch0394.tau3158, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112310 (by positivity) using 1 <;> norm_num)
                · have hs10112312 : InSquare (109/640) (-229/640) (1/640) tau := by
                    convert childUL hs1011231 hx1011231 hy1011231 using 1 <;> norm_num
                  exact Batch0395.cell3160.sound htau (by
                    simp only [Batch0395.cell3160, Batch0395.tau3160, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011231 | hy1011231
                · have hs10112311 : InSquare (111/640) (-231/640) (1/640) tau := by
                    convert childLR hs1011231 hx1011231 hy1011231 using 1 <;> norm_num
                  exact Batch0394.cell3159.sound htau (by
                    simp only [Batch0394.cell3159, Batch0394.tau3159, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112311 (by positivity) using 1 <;> norm_num)
                · have hs10112313 : InSquare (111/640) (-229/640) (1/640) tau := by
                    convert childUR hs1011231 hx1011231 hy1011231 using 1 <;> norm_num
                  exact Batch0395.cell3161.sound htau (by
                    simp only [Batch0395.cell3161, Batch0395.tau3161, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112313 (by positivity) using 1 <;> norm_num)
            · have hs1011233 : InSquare (11/64) (-113/320) (1/320) tau := by
                convert childUR hs101123 hx101123 hy101123 using 1 <;> norm_num
              rcases le_total tau.re (11/64 : ℝ) with hx1011233 | hx1011233
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011233 | hy1011233
                · have hs10112330 : InSquare (109/640) (-227/640) (1/640) tau := by
                    convert childLL hs1011233 hx1011233 hy1011233 using 1 <;> norm_num
                  exact Batch0395.cell3162.sound htau (by
                    simp only [Batch0395.cell3162, Batch0395.tau3162, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112330 (by positivity) using 1 <;> norm_num)
                · have hs10112332 : InSquare (109/640) (-45/128) (1/640) tau := by
                    convert childUL hs1011233 hx1011233 hy1011233 using 1 <;> norm_num
                  exact Batch0395.cell3164.sound htau (by
                    simp only [Batch0395.cell3164, Batch0395.tau3164, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011233 | hy1011233
                · have hs10112331 : InSquare (111/640) (-227/640) (1/640) tau := by
                    convert childLR hs1011233 hx1011233 hy1011233 using 1 <;> norm_num
                  exact Batch0395.cell3163.sound htau (by
                    simp only [Batch0395.cell3163, Batch0395.tau3163, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112331 (by positivity) using 1 <;> norm_num)
                · have hs10112333 : InSquare (111/640) (-45/128) (1/640) tau := by
                    convert childUR hs1011233 hx1011233 hy1011233 using 1 <;> norm_num
                  exact Batch0395.cell3165.sound htau (by
                    simp only [Batch0395.cell3165, Batch0395.tau3165, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112333 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/8 : ℝ) with hy1011 | hy1011
    · have hs10111 : InSquare (3/16) (-31/80) (1/80) tau := by
        convert childLR hs hx1011 hy1011 using 1 <;> norm_num
      exact (outside_10111 htau hs10111).elim
    · have hs10113 : InSquare (3/16) (-29/80) (1/80) tau := by
        convert childUR hs hx1011 hy1011 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx10113 | hx10113
      · rcases le_total tau.im (-29/80 : ℝ) with hy10113 | hy10113
        · have hs101130 : InSquare (29/160) (-59/160) (1/160) tau := by
            convert childLL hs10113 hx10113 hy10113 using 1 <;> norm_num
          exact (outside_101130 htau hs101130).elim
        · have hs101132 : InSquare (29/160) (-57/160) (1/160) tau := by
            convert childUL hs10113 hx10113 hy10113 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx101132 | hx101132
          · rcases le_total tau.im (-57/160 : ℝ) with hy101132 | hy101132
            · have hs1011320 : InSquare (57/320) (-23/64) (1/320) tau := by
                convert childLL hs101132 hx101132 hy101132 using 1 <;> norm_num
              rcases le_total tau.re (57/320 : ℝ) with hx1011320 | hx1011320
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011320 | hy1011320
                · have hs10113200 : InSquare (113/640) (-231/640) (1/640) tau := by
                    convert childLL hs1011320 hx1011320 hy1011320 using 1 <;> norm_num
                  exact Batch0395.cell3166.sound htau (by
                    simp only [Batch0395.cell3166, Batch0395.tau3166, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113200 (by positivity) using 1 <;> norm_num)
                · have hs10113202 : InSquare (113/640) (-229/640) (1/640) tau := by
                    convert childUL hs1011320 hx1011320 hy1011320 using 1 <;> norm_num
                  exact Batch0395.cell3167.sound htau (by
                    simp only [Batch0395.cell3167, Batch0395.tau3167, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011320 | hy1011320
                · have hs10113201 : InSquare (23/128) (-231/640) (1/640) tau := by
                    convert childLR hs1011320 hx1011320 hy1011320 using 1 <;> norm_num
                  exact (outside_10113201 htau hs10113201).elim
                · have hs10113203 : InSquare (23/128) (-229/640) (1/640) tau := by
                    convert childUR hs1011320 hx1011320 hy1011320 using 1 <;> norm_num
                  exact Batch0396.cell3168.sound htau (by
                    simp only [Batch0396.cell3168, Batch0396.tau3168, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113203 (by positivity) using 1 <;> norm_num)
            · have hs1011322 : InSquare (57/320) (-113/320) (1/320) tau := by
                convert childUL hs101132 hx101132 hy101132 using 1 <;> norm_num
              rcases le_total tau.re (57/320 : ℝ) with hx1011322 | hx1011322
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011322 | hy1011322
                · have hs10113220 : InSquare (113/640) (-227/640) (1/640) tau := by
                    convert childLL hs1011322 hx1011322 hy1011322 using 1 <;> norm_num
                  exact Batch0396.cell3170.sound htau (by
                    simp only [Batch0396.cell3170, Batch0396.tau3170, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113220 (by positivity) using 1 <;> norm_num)
                · have hs10113222 : InSquare (113/640) (-45/128) (1/640) tau := by
                    convert childUL hs1011322 hx1011322 hy1011322 using 1 <;> norm_num
                  exact Batch0396.cell3172.sound htau (by
                    simp only [Batch0396.cell3172, Batch0396.tau3172, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011322 | hy1011322
                · have hs10113221 : InSquare (23/128) (-227/640) (1/640) tau := by
                    convert childLR hs1011322 hx1011322 hy1011322 using 1 <;> norm_num
                  exact Batch0396.cell3171.sound htau (by
                    simp only [Batch0396.cell3171, Batch0396.tau3171, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113221 (by positivity) using 1 <;> norm_num)
                · have hs10113223 : InSquare (23/128) (-45/128) (1/640) tau := by
                    convert childUR hs1011322 hx1011322 hy1011322 using 1 <;> norm_num
                  exact Batch0396.cell3173.sound htau (by
                    simp only [Batch0396.cell3173, Batch0396.tau3173, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101132 | hy101132
            · have hs1011321 : InSquare (59/320) (-23/64) (1/320) tau := by
                convert childLR hs101132 hx101132 hy101132 using 1 <;> norm_num
              rcases le_total tau.re (59/320 : ℝ) with hx1011321 | hx1011321
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011321 | hy1011321
                · have hs10113210 : InSquare (117/640) (-231/640) (1/640) tau := by
                    convert childLL hs1011321 hx1011321 hy1011321 using 1 <;> norm_num
                  exact (outside_10113210 htau hs10113210).elim
                · have hs10113212 : InSquare (117/640) (-229/640) (1/640) tau := by
                    convert childUL hs1011321 hx1011321 hy1011321 using 1 <;> norm_num
                  exact Batch0396.cell3169.sound htau (by
                    simp only [Batch0396.cell3169, Batch0396.tau3169, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011321 | hy1011321
                · have hs10113211 : InSquare (119/640) (-231/640) (1/640) tau := by
                    convert childLR hs1011321 hx1011321 hy1011321 using 1 <;> norm_num
                  exact (outside_10113211 htau hs10113211).elim
                · have hs10113213 : InSquare (119/640) (-229/640) (1/640) tau := by
                    convert childUR hs1011321 hx1011321 hy1011321 using 1 <;> norm_num
                  exact (outside_10113213 htau hs10113213).elim
            · have hs1011323 : InSquare (59/320) (-113/320) (1/320) tau := by
                convert childUR hs101132 hx101132 hy101132 using 1 <;> norm_num
              rcases le_total tau.re (59/320 : ℝ) with hx1011323 | hx1011323
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011323 | hy1011323
                · have hs10113230 : InSquare (117/640) (-227/640) (1/640) tau := by
                    convert childLL hs1011323 hx1011323 hy1011323 using 1 <;> norm_num
                  exact Batch0396.cell3174.sound htau (by
                    simp only [Batch0396.cell3174, Batch0396.tau3174, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113230 (by positivity) using 1 <;> norm_num)
                · have hs10113232 : InSquare (117/640) (-45/128) (1/640) tau := by
                    convert childUL hs1011323 hx1011323 hy1011323 using 1 <;> norm_num
                  exact Batch0397.cell3176.sound htau (by
                    simp only [Batch0397.cell3176, Batch0397.tau3176, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011323 | hy1011323
                · have hs10113231 : InSquare (119/640) (-227/640) (1/640) tau := by
                    convert childLR hs1011323 hx1011323 hy1011323 using 1 <;> norm_num
                  exact Batch0396.cell3175.sound htau (by
                    simp only [Batch0396.cell3175, Batch0396.tau3175, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113231 (by positivity) using 1 <;> norm_num)
                · have hs10113233 : InSquare (119/640) (-45/128) (1/640) tau := by
                    convert childUR hs1011323 hx1011323 hy1011323 using 1 <;> norm_num
                  exact Batch0397.cell3177.sound htau (by
                    simp only [Batch0397.cell3177, Batch0397.tau3177, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy10113 | hy10113
        · have hs101131 : InSquare (31/160) (-59/160) (1/160) tau := by
            convert childLR hs10113 hx10113 hy10113 using 1 <;> norm_num
          exact (outside_101131 htau hs101131).elim
        · have hs101133 : InSquare (31/160) (-57/160) (1/160) tau := by
            convert childUR hs10113 hx10113 hy10113 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx101133 | hx101133
          · rcases le_total tau.im (-57/160 : ℝ) with hy101133 | hy101133
            · have hs1011330 : InSquare (61/320) (-23/64) (1/320) tau := by
                convert childLL hs101133 hx101133 hy101133 using 1 <;> norm_num
              exact (outside_1011330 htau hs1011330).elim
            · have hs1011332 : InSquare (61/320) (-113/320) (1/320) tau := by
                convert childUL hs101133 hx101133 hy101133 using 1 <;> norm_num
              rcases le_total tau.re (61/320 : ℝ) with hx1011332 | hx1011332
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011332 | hy1011332
                · have hs10113320 : InSquare (121/640) (-227/640) (1/640) tau := by
                    convert childLL hs1011332 hx1011332 hy1011332 using 1 <;> norm_num
                  exact Batch0397.cell3178.sound htau (by
                    simp only [Batch0397.cell3178, Batch0397.tau3178, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113320 (by positivity) using 1 <;> norm_num)
                · have hs10113322 : InSquare (121/640) (-45/128) (1/640) tau := by
                    convert childUL hs1011332 hx1011332 hy1011332 using 1 <;> norm_num
                  exact Batch0397.cell3179.sound htau (by
                    simp only [Batch0397.cell3179, Batch0397.tau3179, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011332 | hy1011332
                · have hs10113321 : InSquare (123/640) (-227/640) (1/640) tau := by
                    convert childLR hs1011332 hx1011332 hy1011332 using 1 <;> norm_num
                  exact (outside_10113321 htau hs10113321).elim
                · have hs10113323 : InSquare (123/640) (-45/128) (1/640) tau := by
                    convert childUR hs1011332 hx1011332 hy1011332 using 1 <;> norm_num
                  exact Batch0397.cell3180.sound htau (by
                    simp only [Batch0397.cell3180, Batch0397.tau3180, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101133 | hy101133
            · have hs1011331 : InSquare (63/320) (-23/64) (1/320) tau := by
                convert childLR hs101133 hx101133 hy101133 using 1 <;> norm_num
              exact (outside_1011331 htau hs1011331).elim
            · have hs1011333 : InSquare (63/320) (-113/320) (1/320) tau := by
                convert childUR hs101133 hx101133 hy101133 using 1 <;> norm_num
              exact (outside_1011333 htau hs1011333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1011

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1012 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1012

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx1012 | hx1012
  · rcases le_total tau.im (-13/40 : ℝ) with hy1012 | hy1012
    · have hs10120 : InSquare (9/80) (-27/80) (1/80) tau := by
        convert childLL hs hx1012 hy1012 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx10120 | hx10120
      · rcases le_total tau.im (-27/80 : ℝ) with hy10120 | hy10120
        · have hs101200 : InSquare (17/160) (-11/32) (1/160) tau := by
            convert childLL hs10120 hx10120 hy10120 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx101200 | hx101200
          · rcases le_total tau.im (-11/32 : ℝ) with hy101200 | hy101200
            · have hs1012000 : InSquare (33/320) (-111/320) (1/320) tau := by
                convert childLL hs101200 hx101200 hy101200 using 1 <;> norm_num
              exact Batch0206.cell1651.sound htau (by
                simp only [Batch0206.cell1651, Batch0206.tau1651, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012000 (by positivity) using 1 <;> norm_num)
            · have hs1012002 : InSquare (33/320) (-109/320) (1/320) tau := by
                convert childUL hs101200 hx101200 hy101200 using 1 <;> norm_num
              exact Batch0206.cell1653.sound htau (by
                simp only [Batch0206.cell1653, Batch0206.tau1653, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101200 | hy101200
            · have hs1012001 : InSquare (7/64) (-111/320) (1/320) tau := by
                convert childLR hs101200 hx101200 hy101200 using 1 <;> norm_num
              exact Batch0206.cell1652.sound htau (by
                simp only [Batch0206.cell1652, Batch0206.tau1652, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012001 (by positivity) using 1 <;> norm_num)
            · have hs1012003 : InSquare (7/64) (-109/320) (1/320) tau := by
                convert childUR hs101200 hx101200 hy101200 using 1 <;> norm_num
              exact Batch0206.cell1654.sound htau (by
                simp only [Batch0206.cell1654, Batch0206.tau1654, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012003 (by positivity) using 1 <;> norm_num)
        · have hs101202 : InSquare (17/160) (-53/160) (1/160) tau := by
            convert childUL hs10120 hx10120 hy10120 using 1 <;> norm_num
          exact Batch0073.cell0588.sound htau (by
            simp only [Batch0073.cell0588, Batch0073.tau0588, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10120 | hy10120
        · have hs101201 : InSquare (19/160) (-11/32) (1/160) tau := by
            convert childLR hs10120 hx10120 hy10120 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx101201 | hx101201
          · rcases le_total tau.im (-11/32 : ℝ) with hy101201 | hy101201
            · have hs1012010 : InSquare (37/320) (-111/320) (1/320) tau := by
                convert childLL hs101201 hx101201 hy101201 using 1 <;> norm_num
              exact Batch0206.cell1655.sound htau (by
                simp only [Batch0206.cell1655, Batch0206.tau1655, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012010 (by positivity) using 1 <;> norm_num)
            · have hs1012012 : InSquare (37/320) (-109/320) (1/320) tau := by
                convert childUL hs101201 hx101201 hy101201 using 1 <;> norm_num
              exact Batch0207.cell1657.sound htau (by
                simp only [Batch0207.cell1657, Batch0207.tau1657, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101201 | hy101201
            · have hs1012011 : InSquare (39/320) (-111/320) (1/320) tau := by
                convert childLR hs101201 hx101201 hy101201 using 1 <;> norm_num
              exact Batch0207.cell1656.sound htau (by
                simp only [Batch0207.cell1656, Batch0207.tau1656, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012011 (by positivity) using 1 <;> norm_num)
            · have hs1012013 : InSquare (39/320) (-109/320) (1/320) tau := by
                convert childUR hs101201 hx101201 hy101201 using 1 <;> norm_num
              exact Batch0207.cell1658.sound htau (by
                simp only [Batch0207.cell1658, Batch0207.tau1658, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012013 (by positivity) using 1 <;> norm_num)
        · have hs101203 : InSquare (19/160) (-53/160) (1/160) tau := by
            convert childUR hs10120 hx10120 hy10120 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx101203 | hx101203
          · rcases le_total tau.im (-53/160 : ℝ) with hy101203 | hy101203
            · have hs1012030 : InSquare (37/320) (-107/320) (1/320) tau := by
                convert childLL hs101203 hx101203 hy101203 using 1 <;> norm_num
              exact Batch0207.cell1659.sound htau (by
                simp only [Batch0207.cell1659, Batch0207.tau1659, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012030 (by positivity) using 1 <;> norm_num)
            · have hs1012032 : InSquare (37/320) (-21/64) (1/320) tau := by
                convert childUL hs101203 hx101203 hy101203 using 1 <;> norm_num
              exact Batch0207.cell1661.sound htau (by
                simp only [Batch0207.cell1661, Batch0207.tau1661, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy101203 | hy101203
            · have hs1012031 : InSquare (39/320) (-107/320) (1/320) tau := by
                convert childLR hs101203 hx101203 hy101203 using 1 <;> norm_num
              exact Batch0207.cell1660.sound htau (by
                simp only [Batch0207.cell1660, Batch0207.tau1660, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012031 (by positivity) using 1 <;> norm_num)
            · have hs1012033 : InSquare (39/320) (-21/64) (1/320) tau := by
                convert childUR hs101203 hx101203 hy101203 using 1 <;> norm_num
              exact Batch0207.cell1662.sound htau (by
                simp only [Batch0207.cell1662, Batch0207.tau1662, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012033 (by positivity) using 1 <;> norm_num)
    · have hs10122 : InSquare (9/80) (-5/16) (1/80) tau := by
        convert childUL hs hx1012 hy1012 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx10122 | hx10122
      · rcases le_total tau.im (-5/16 : ℝ) with hy10122 | hy10122
        · have hs101220 : InSquare (17/160) (-51/160) (1/160) tau := by
            convert childLL hs10122 hx10122 hy10122 using 1 <;> norm_num
          exact Batch0073.cell0589.sound htau (by
            simp only [Batch0073.cell0589, Batch0073.tau0589, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101220 (by positivity) using 1 <;> norm_num)
        · have hs101222 : InSquare (17/160) (-49/160) (1/160) tau := by
            convert childUL hs10122 hx10122 hy10122 using 1 <;> norm_num
          exact Batch0073.cell0591.sound htau (by
            simp only [Batch0073.cell0591, Batch0073.tau0591, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10122 | hy10122
        · have hs101221 : InSquare (19/160) (-51/160) (1/160) tau := by
            convert childLR hs10122 hx10122 hy10122 using 1 <;> norm_num
          exact Batch0073.cell0590.sound htau (by
            simp only [Batch0073.cell0590, Batch0073.tau0590, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101221 (by positivity) using 1 <;> norm_num)
        · have hs101223 : InSquare (19/160) (-49/160) (1/160) tau := by
            convert childUR hs10122 hx10122 hy10122 using 1 <;> norm_num
          exact Batch0074.cell0592.sound htau (by
            simp only [Batch0074.cell0592, Batch0074.tau0592, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy1012 | hy1012
    · have hs10121 : InSquare (11/80) (-27/80) (1/80) tau := by
        convert childLR hs hx1012 hy1012 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx10121 | hx10121
      · rcases le_total tau.im (-27/80 : ℝ) with hy10121 | hy10121
        · have hs101210 : InSquare (21/160) (-11/32) (1/160) tau := by
            convert childLL hs10121 hx10121 hy10121 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx101210 | hx101210
          · rcases le_total tau.im (-11/32 : ℝ) with hy101210 | hy101210
            · have hs1012100 : InSquare (41/320) (-111/320) (1/320) tau := by
                convert childLL hs101210 hx101210 hy101210 using 1 <;> norm_num
              exact Batch0207.cell1663.sound htau (by
                simp only [Batch0207.cell1663, Batch0207.tau1663, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012100 (by positivity) using 1 <;> norm_num)
            · have hs1012102 : InSquare (41/320) (-109/320) (1/320) tau := by
                convert childUL hs101210 hx101210 hy101210 using 1 <;> norm_num
              exact Batch0208.cell1665.sound htau (by
                simp only [Batch0208.cell1665, Batch0208.tau1665, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101210 | hy101210
            · have hs1012101 : InSquare (43/320) (-111/320) (1/320) tau := by
                convert childLR hs101210 hx101210 hy101210 using 1 <;> norm_num
              exact Batch0208.cell1664.sound htau (by
                simp only [Batch0208.cell1664, Batch0208.tau1664, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012101 (by positivity) using 1 <;> norm_num)
            · have hs1012103 : InSquare (43/320) (-109/320) (1/320) tau := by
                convert childUR hs101210 hx101210 hy101210 using 1 <;> norm_num
              exact Batch0208.cell1666.sound htau (by
                simp only [Batch0208.cell1666, Batch0208.tau1666, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012103 (by positivity) using 1 <;> norm_num)
        · have hs101212 : InSquare (21/160) (-53/160) (1/160) tau := by
            convert childUL hs10121 hx10121 hy10121 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx101212 | hx101212
          · rcases le_total tau.im (-53/160 : ℝ) with hy101212 | hy101212
            · have hs1012120 : InSquare (41/320) (-107/320) (1/320) tau := by
                convert childLL hs101212 hx101212 hy101212 using 1 <;> norm_num
              exact Batch0208.cell1671.sound htau (by
                simp only [Batch0208.cell1671, Batch0208.tau1671, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012120 (by positivity) using 1 <;> norm_num)
            · have hs1012122 : InSquare (41/320) (-21/64) (1/320) tau := by
                convert childUL hs101212 hx101212 hy101212 using 1 <;> norm_num
              exact Batch0209.cell1673.sound htau (by
                simp only [Batch0209.cell1673, Batch0209.tau1673, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy101212 | hy101212
            · have hs1012121 : InSquare (43/320) (-107/320) (1/320) tau := by
                convert childLR hs101212 hx101212 hy101212 using 1 <;> norm_num
              exact Batch0209.cell1672.sound htau (by
                simp only [Batch0209.cell1672, Batch0209.tau1672, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012121 (by positivity) using 1 <;> norm_num)
            · have hs1012123 : InSquare (43/320) (-21/64) (1/320) tau := by
                convert childUR hs101212 hx101212 hy101212 using 1 <;> norm_num
              exact Batch0209.cell1674.sound htau (by
                simp only [Batch0209.cell1674, Batch0209.tau1674, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10121 | hy10121
        · have hs101211 : InSquare (23/160) (-11/32) (1/160) tau := by
            convert childLR hs10121 hx10121 hy10121 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx101211 | hx101211
          · rcases le_total tau.im (-11/32 : ℝ) with hy101211 | hy101211
            · have hs1012110 : InSquare (9/64) (-111/320) (1/320) tau := by
                convert childLL hs101211 hx101211 hy101211 using 1 <;> norm_num
              exact Batch0208.cell1667.sound htau (by
                simp only [Batch0208.cell1667, Batch0208.tau1667, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012110 (by positivity) using 1 <;> norm_num)
            · have hs1012112 : InSquare (9/64) (-109/320) (1/320) tau := by
                convert childUL hs101211 hx101211 hy101211 using 1 <;> norm_num
              exact Batch0208.cell1669.sound htau (by
                simp only [Batch0208.cell1669, Batch0208.tau1669, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101211 | hy101211
            · have hs1012111 : InSquare (47/320) (-111/320) (1/320) tau := by
                convert childLR hs101211 hx101211 hy101211 using 1 <;> norm_num
              exact Batch0208.cell1668.sound htau (by
                simp only [Batch0208.cell1668, Batch0208.tau1668, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012111 (by positivity) using 1 <;> norm_num)
            · have hs1012113 : InSquare (47/320) (-109/320) (1/320) tau := by
                convert childUR hs101211 hx101211 hy101211 using 1 <;> norm_num
              exact Batch0208.cell1670.sound htau (by
                simp only [Batch0208.cell1670, Batch0208.tau1670, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012113 (by positivity) using 1 <;> norm_num)
        · have hs101213 : InSquare (23/160) (-53/160) (1/160) tau := by
            convert childUR hs10121 hx10121 hy10121 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx101213 | hx101213
          · rcases le_total tau.im (-53/160 : ℝ) with hy101213 | hy101213
            · have hs1012130 : InSquare (9/64) (-107/320) (1/320) tau := by
                convert childLL hs101213 hx101213 hy101213 using 1 <;> norm_num
              exact Batch0209.cell1675.sound htau (by
                simp only [Batch0209.cell1675, Batch0209.tau1675, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012130 (by positivity) using 1 <;> norm_num)
            · have hs1012132 : InSquare (9/64) (-21/64) (1/320) tau := by
                convert childUL hs101213 hx101213 hy101213 using 1 <;> norm_num
              exact Batch0209.cell1677.sound htau (by
                simp only [Batch0209.cell1677, Batch0209.tau1677, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy101213 | hy101213
            · have hs1012131 : InSquare (47/320) (-107/320) (1/320) tau := by
                convert childLR hs101213 hx101213 hy101213 using 1 <;> norm_num
              exact Batch0209.cell1676.sound htau (by
                simp only [Batch0209.cell1676, Batch0209.tau1676, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012131 (by positivity) using 1 <;> norm_num)
            · have hs1012133 : InSquare (47/320) (-21/64) (1/320) tau := by
                convert childUR hs101213 hx101213 hy101213 using 1 <;> norm_num
              exact Batch0209.cell1678.sound htau (by
                simp only [Batch0209.cell1678, Batch0209.tau1678, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012133 (by positivity) using 1 <;> norm_num)
    · have hs10123 : InSquare (11/80) (-5/16) (1/80) tau := by
        convert childUR hs hx1012 hy1012 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx10123 | hx10123
      · rcases le_total tau.im (-5/16 : ℝ) with hy10123 | hy10123
        · have hs101230 : InSquare (21/160) (-51/160) (1/160) tau := by
            convert childLL hs10123 hx10123 hy10123 using 1 <;> norm_num
          exact Batch0074.cell0593.sound htau (by
            simp only [Batch0074.cell0593, Batch0074.tau0593, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101230 (by positivity) using 1 <;> norm_num)
        · have hs101232 : InSquare (21/160) (-49/160) (1/160) tau := by
            convert childUL hs10123 hx10123 hy10123 using 1 <;> norm_num
          exact Batch0074.cell0594.sound htau (by
            simp only [Batch0074.cell0594, Batch0074.tau0594, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10123 | hy10123
        · have hs101231 : InSquare (23/160) (-51/160) (1/160) tau := by
            convert childLR hs10123 hx10123 hy10123 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx101231 | hx101231
          · rcases le_total tau.im (-51/160 : ℝ) with hy101231 | hy101231
            · have hs1012310 : InSquare (9/64) (-103/320) (1/320) tau := by
                convert childLL hs101231 hx101231 hy101231 using 1 <;> norm_num
              exact Batch0209.cell1679.sound htau (by
                simp only [Batch0209.cell1679, Batch0209.tau1679, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012310 (by positivity) using 1 <;> norm_num)
            · have hs1012312 : InSquare (9/64) (-101/320) (1/320) tau := by
                convert childUL hs101231 hx101231 hy101231 using 1 <;> norm_num
              exact Batch0210.cell1681.sound htau (by
                simp only [Batch0210.cell1681, Batch0210.tau1681, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy101231 | hy101231
            · have hs1012311 : InSquare (47/320) (-103/320) (1/320) tau := by
                convert childLR hs101231 hx101231 hy101231 using 1 <;> norm_num
              exact Batch0210.cell1680.sound htau (by
                simp only [Batch0210.cell1680, Batch0210.tau1680, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012311 (by positivity) using 1 <;> norm_num)
            · have hs1012313 : InSquare (47/320) (-101/320) (1/320) tau := by
                convert childUR hs101231 hx101231 hy101231 using 1 <;> norm_num
              exact Batch0210.cell1682.sound htau (by
                simp only [Batch0210.cell1682, Batch0210.tau1682, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012313 (by positivity) using 1 <;> norm_num)
        · have hs101233 : InSquare (23/160) (-49/160) (1/160) tau := by
            convert childUR hs10123 hx10123 hy10123 using 1 <;> norm_num
          exact Batch0074.cell0595.sound htau (by
            simp only [Batch0074.cell0595, Batch0074.tau0595, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1012

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1013 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1013

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx1013 | hx1013
  · rcases le_total tau.im (-13/40 : ℝ) with hy1013 | hy1013
    · have hs10130 : InSquare (13/80) (-27/80) (1/80) tau := by
        convert childLL hs hx1013 hy1013 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx10130 | hx10130
      · rcases le_total tau.im (-27/80 : ℝ) with hy10130 | hy10130
        · have hs101300 : InSquare (5/32) (-11/32) (1/160) tau := by
            convert childLL hs10130 hx10130 hy10130 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx101300 | hx101300
          · rcases le_total tau.im (-11/32 : ℝ) with hy101300 | hy101300
            · have hs1013000 : InSquare (49/320) (-111/320) (1/320) tau := by
                convert childLL hs101300 hx101300 hy101300 using 1 <;> norm_num
              exact Batch0210.cell1683.sound htau (by
                simp only [Batch0210.cell1683, Batch0210.tau1683, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013000 (by positivity) using 1 <;> norm_num)
            · have hs1013002 : InSquare (49/320) (-109/320) (1/320) tau := by
                convert childUL hs101300 hx101300 hy101300 using 1 <;> norm_num
              exact Batch0210.cell1685.sound htau (by
                simp only [Batch0210.cell1685, Batch0210.tau1685, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101300 | hy101300
            · have hs1013001 : InSquare (51/320) (-111/320) (1/320) tau := by
                convert childLR hs101300 hx101300 hy101300 using 1 <;> norm_num
              exact Batch0210.cell1684.sound htau (by
                simp only [Batch0210.cell1684, Batch0210.tau1684, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013001 (by positivity) using 1 <;> norm_num)
            · have hs1013003 : InSquare (51/320) (-109/320) (1/320) tau := by
                convert childUR hs101300 hx101300 hy101300 using 1 <;> norm_num
              exact Batch0210.cell1686.sound htau (by
                simp only [Batch0210.cell1686, Batch0210.tau1686, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013003 (by positivity) using 1 <;> norm_num)
        · have hs101302 : InSquare (5/32) (-53/160) (1/160) tau := by
            convert childUL hs10130 hx10130 hy10130 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx101302 | hx101302
          · rcases le_total tau.im (-53/160 : ℝ) with hy101302 | hy101302
            · have hs1013020 : InSquare (49/320) (-107/320) (1/320) tau := by
                convert childLL hs101302 hx101302 hy101302 using 1 <;> norm_num
              exact Batch0211.cell1691.sound htau (by
                simp only [Batch0211.cell1691, Batch0211.tau1691, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013020 (by positivity) using 1 <;> norm_num)
            · have hs1013022 : InSquare (49/320) (-21/64) (1/320) tau := by
                convert childUL hs101302 hx101302 hy101302 using 1 <;> norm_num
              exact Batch0211.cell1693.sound htau (by
                simp only [Batch0211.cell1693, Batch0211.tau1693, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy101302 | hy101302
            · have hs1013021 : InSquare (51/320) (-107/320) (1/320) tau := by
                convert childLR hs101302 hx101302 hy101302 using 1 <;> norm_num
              exact Batch0211.cell1692.sound htau (by
                simp only [Batch0211.cell1692, Batch0211.tau1692, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013021 (by positivity) using 1 <;> norm_num)
            · have hs1013023 : InSquare (51/320) (-21/64) (1/320) tau := by
                convert childUR hs101302 hx101302 hy101302 using 1 <;> norm_num
              exact Batch0211.cell1694.sound htau (by
                simp only [Batch0211.cell1694, Batch0211.tau1694, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10130 | hy10130
        · have hs101301 : InSquare (27/160) (-11/32) (1/160) tau := by
            convert childLR hs10130 hx10130 hy10130 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx101301 | hx101301
          · rcases le_total tau.im (-11/32 : ℝ) with hy101301 | hy101301
            · have hs1013010 : InSquare (53/320) (-111/320) (1/320) tau := by
                convert childLL hs101301 hx101301 hy101301 using 1 <;> norm_num
              exact Batch0210.cell1687.sound htau (by
                simp only [Batch0210.cell1687, Batch0210.tau1687, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013010 (by positivity) using 1 <;> norm_num)
            · have hs1013012 : InSquare (53/320) (-109/320) (1/320) tau := by
                convert childUL hs101301 hx101301 hy101301 using 1 <;> norm_num
              exact Batch0211.cell1689.sound htau (by
                simp only [Batch0211.cell1689, Batch0211.tau1689, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101301 | hy101301
            · have hs1013011 : InSquare (11/64) (-111/320) (1/320) tau := by
                convert childLR hs101301 hx101301 hy101301 using 1 <;> norm_num
              exact Batch0211.cell1688.sound htau (by
                simp only [Batch0211.cell1688, Batch0211.tau1688, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013011 (by positivity) using 1 <;> norm_num)
            · have hs1013013 : InSquare (11/64) (-109/320) (1/320) tau := by
                convert childUR hs101301 hx101301 hy101301 using 1 <;> norm_num
              exact Batch0211.cell1690.sound htau (by
                simp only [Batch0211.cell1690, Batch0211.tau1690, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013013 (by positivity) using 1 <;> norm_num)
        · have hs101303 : InSquare (27/160) (-53/160) (1/160) tau := by
            convert childUR hs10130 hx10130 hy10130 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx101303 | hx101303
          · rcases le_total tau.im (-53/160 : ℝ) with hy101303 | hy101303
            · have hs1013030 : InSquare (53/320) (-107/320) (1/320) tau := by
                convert childLL hs101303 hx101303 hy101303 using 1 <;> norm_num
              exact Batch0211.cell1695.sound htau (by
                simp only [Batch0211.cell1695, Batch0211.tau1695, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013030 (by positivity) using 1 <;> norm_num)
            · have hs1013032 : InSquare (53/320) (-21/64) (1/320) tau := by
                convert childUL hs101303 hx101303 hy101303 using 1 <;> norm_num
              exact Batch0212.cell1697.sound htau (by
                simp only [Batch0212.cell1697, Batch0212.tau1697, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy101303 | hy101303
            · have hs1013031 : InSquare (11/64) (-107/320) (1/320) tau := by
                convert childLR hs101303 hx101303 hy101303 using 1 <;> norm_num
              exact Batch0212.cell1696.sound htau (by
                simp only [Batch0212.cell1696, Batch0212.tau1696, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013031 (by positivity) using 1 <;> norm_num)
            · have hs1013033 : InSquare (11/64) (-21/64) (1/320) tau := by
                convert childUR hs101303 hx101303 hy101303 using 1 <;> norm_num
              exact Batch0212.cell1698.sound htau (by
                simp only [Batch0212.cell1698, Batch0212.tau1698, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013033 (by positivity) using 1 <;> norm_num)
    · have hs10132 : InSquare (13/80) (-5/16) (1/80) tau := by
        convert childUL hs hx1013 hy1013 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx10132 | hx10132
      · rcases le_total tau.im (-5/16 : ℝ) with hy10132 | hy10132
        · have hs101320 : InSquare (5/32) (-51/160) (1/160) tau := by
            convert childLL hs10132 hx10132 hy10132 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx101320 | hx101320
          · rcases le_total tau.im (-51/160 : ℝ) with hy101320 | hy101320
            · have hs1013200 : InSquare (49/320) (-103/320) (1/320) tau := by
                convert childLL hs101320 hx101320 hy101320 using 1 <;> norm_num
              exact Batch0214.cell1713.sound htau (by
                simp only [Batch0214.cell1713, Batch0214.tau1713, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013200 (by positivity) using 1 <;> norm_num)
            · have hs1013202 : InSquare (49/320) (-101/320) (1/320) tau := by
                convert childUL hs101320 hx101320 hy101320 using 1 <;> norm_num
              exact Batch0214.cell1715.sound htau (by
                simp only [Batch0214.cell1715, Batch0214.tau1715, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy101320 | hy101320
            · have hs1013201 : InSquare (51/320) (-103/320) (1/320) tau := by
                convert childLR hs101320 hx101320 hy101320 using 1 <;> norm_num
              exact Batch0214.cell1714.sound htau (by
                simp only [Batch0214.cell1714, Batch0214.tau1714, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013201 (by positivity) using 1 <;> norm_num)
            · have hs1013203 : InSquare (51/320) (-101/320) (1/320) tau := by
                convert childUR hs101320 hx101320 hy101320 using 1 <;> norm_num
              exact Batch0214.cell1716.sound htau (by
                simp only [Batch0214.cell1716, Batch0214.tau1716, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013203 (by positivity) using 1 <;> norm_num)
        · have hs101322 : InSquare (5/32) (-49/160) (1/160) tau := by
            convert childUL hs10132 hx10132 hy10132 using 1 <;> norm_num
          exact Batch0074.cell0596.sound htau (by
            simp only [Batch0074.cell0596, Batch0074.tau0596, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10132 | hy10132
        · have hs101321 : InSquare (27/160) (-51/160) (1/160) tau := by
            convert childLR hs10132 hx10132 hy10132 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx101321 | hx101321
          · rcases le_total tau.im (-51/160 : ℝ) with hy101321 | hy101321
            · have hs1013210 : InSquare (53/320) (-103/320) (1/320) tau := by
                convert childLL hs101321 hx101321 hy101321 using 1 <;> norm_num
              exact Batch0214.cell1717.sound htau (by
                simp only [Batch0214.cell1717, Batch0214.tau1717, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013210 (by positivity) using 1 <;> norm_num)
            · have hs1013212 : InSquare (53/320) (-101/320) (1/320) tau := by
                convert childUL hs101321 hx101321 hy101321 using 1 <;> norm_num
              exact Batch0214.cell1719.sound htau (by
                simp only [Batch0214.cell1719, Batch0214.tau1719, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy101321 | hy101321
            · have hs1013211 : InSquare (11/64) (-103/320) (1/320) tau := by
                convert childLR hs101321 hx101321 hy101321 using 1 <;> norm_num
              exact Batch0214.cell1718.sound htau (by
                simp only [Batch0214.cell1718, Batch0214.tau1718, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013211 (by positivity) using 1 <;> norm_num)
            · have hs1013213 : InSquare (11/64) (-101/320) (1/320) tau := by
                convert childUR hs101321 hx101321 hy101321 using 1 <;> norm_num
              exact Batch0215.cell1720.sound htau (by
                simp only [Batch0215.cell1720, Batch0215.tau1720, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013213 (by positivity) using 1 <;> norm_num)
        · have hs101323 : InSquare (27/160) (-49/160) (1/160) tau := by
            convert childUR hs10132 hx10132 hy10132 using 1 <;> norm_num
          exact Batch0074.cell0597.sound htau (by
            simp only [Batch0074.cell0597, Batch0074.tau0597, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy1013 | hy1013
    · have hs10131 : InSquare (3/16) (-27/80) (1/80) tau := by
        convert childLR hs hx1013 hy1013 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx10131 | hx10131
      · rcases le_total tau.im (-27/80 : ℝ) with hy10131 | hy10131
        · have hs101310 : InSquare (29/160) (-11/32) (1/160) tau := by
            convert childLL hs10131 hx10131 hy10131 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx101310 | hx101310
          · rcases le_total tau.im (-11/32 : ℝ) with hy101310 | hy101310
            · have hs1013100 : InSquare (57/320) (-111/320) (1/320) tau := by
                convert childLL hs101310 hx101310 hy101310 using 1 <;> norm_num
              exact Batch0212.cell1699.sound htau (by
                simp only [Batch0212.cell1699, Batch0212.tau1699, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013100 (by positivity) using 1 <;> norm_num)
            · have hs1013102 : InSquare (57/320) (-109/320) (1/320) tau := by
                convert childUL hs101310 hx101310 hy101310 using 1 <;> norm_num
              exact Batch0212.cell1701.sound htau (by
                simp only [Batch0212.cell1701, Batch0212.tau1701, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101310 | hy101310
            · have hs1013101 : InSquare (59/320) (-111/320) (1/320) tau := by
                convert childLR hs101310 hx101310 hy101310 using 1 <;> norm_num
              exact Batch0212.cell1700.sound htau (by
                simp only [Batch0212.cell1700, Batch0212.tau1700, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013101 (by positivity) using 1 <;> norm_num)
            · have hs1013103 : InSquare (59/320) (-109/320) (1/320) tau := by
                convert childUR hs101310 hx101310 hy101310 using 1 <;> norm_num
              exact Batch0212.cell1702.sound htau (by
                simp only [Batch0212.cell1702, Batch0212.tau1702, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013103 (by positivity) using 1 <;> norm_num)
        · have hs101312 : InSquare (29/160) (-53/160) (1/160) tau := by
            convert childUL hs10131 hx10131 hy10131 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx101312 | hx101312
          · rcases le_total tau.im (-53/160 : ℝ) with hy101312 | hy101312
            · have hs1013120 : InSquare (57/320) (-107/320) (1/320) tau := by
                convert childLL hs101312 hx101312 hy101312 using 1 <;> norm_num
              exact Batch0213.cell1705.sound htau (by
                simp only [Batch0213.cell1705, Batch0213.tau1705, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013120 (by positivity) using 1 <;> norm_num)
            · have hs1013122 : InSquare (57/320) (-21/64) (1/320) tau := by
                convert childUL hs101312 hx101312 hy101312 using 1 <;> norm_num
              exact Batch0213.cell1707.sound htau (by
                simp only [Batch0213.cell1707, Batch0213.tau1707, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy101312 | hy101312
            · have hs1013121 : InSquare (59/320) (-107/320) (1/320) tau := by
                convert childLR hs101312 hx101312 hy101312 using 1 <;> norm_num
              exact Batch0213.cell1706.sound htau (by
                simp only [Batch0213.cell1706, Batch0213.tau1706, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013121 (by positivity) using 1 <;> norm_num)
            · have hs1013123 : InSquare (59/320) (-21/64) (1/320) tau := by
                convert childUR hs101312 hx101312 hy101312 using 1 <;> norm_num
              exact Batch0213.cell1708.sound htau (by
                simp only [Batch0213.cell1708, Batch0213.tau1708, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10131 | hy10131
        · have hs101311 : InSquare (31/160) (-11/32) (1/160) tau := by
            convert childLR hs10131 hx10131 hy10131 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx101311 | hx101311
          · rcases le_total tau.im (-11/32 : ℝ) with hy101311 | hy101311
            · have hs1013110 : InSquare (61/320) (-111/320) (1/320) tau := by
                convert childLL hs101311 hx101311 hy101311 using 1 <;> norm_num
              rcases le_total tau.re (61/320 : ℝ) with hx1013110 | hx1013110
              · rcases le_total tau.im (-111/320 : ℝ) with hy1013110 | hy1013110
                · have hs10131100 : InSquare (121/640) (-223/640) (1/640) tau := by
                    convert childLL hs1013110 hx1013110 hy1013110 using 1 <;> norm_num
                  exact Batch0397.cell3181.sound htau (by
                    simp only [Batch0397.cell3181, Batch0397.tau3181, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131100 (by positivity) using 1 <;> norm_num)
                · have hs10131102 : InSquare (121/640) (-221/640) (1/640) tau := by
                    convert childUL hs1013110 hx1013110 hy1013110 using 1 <;> norm_num
                  exact Batch0397.cell3183.sound htau (by
                    simp only [Batch0397.cell3183, Batch0397.tau3183, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-111/320 : ℝ) with hy1013110 | hy1013110
                · have hs10131101 : InSquare (123/640) (-223/640) (1/640) tau := by
                    convert childLR hs1013110 hx1013110 hy1013110 using 1 <;> norm_num
                  exact Batch0397.cell3182.sound htau (by
                    simp only [Batch0397.cell3182, Batch0397.tau3182, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131101 (by positivity) using 1 <;> norm_num)
                · have hs10131103 : InSquare (123/640) (-221/640) (1/640) tau := by
                    convert childUR hs1013110 hx1013110 hy1013110 using 1 <;> norm_num
                  exact Batch0398.cell3184.sound htau (by
                    simp only [Batch0398.cell3184, Batch0398.tau3184, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131103 (by positivity) using 1 <;> norm_num)
            · have hs1013112 : InSquare (61/320) (-109/320) (1/320) tau := by
                convert childUL hs101311 hx101311 hy101311 using 1 <;> norm_num
              exact Batch0212.cell1703.sound htau (by
                simp only [Batch0212.cell1703, Batch0212.tau1703, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101311 | hy101311
            · have hs1013111 : InSquare (63/320) (-111/320) (1/320) tau := by
                convert childLR hs101311 hx101311 hy101311 using 1 <;> norm_num
              rcases le_total tau.re (63/320 : ℝ) with hx1013111 | hx1013111
              · rcases le_total tau.im (-111/320 : ℝ) with hy1013111 | hy1013111
                · have hs10131110 : InSquare (25/128) (-223/640) (1/640) tau := by
                    convert childLL hs1013111 hx1013111 hy1013111 using 1 <;> norm_num
                  exact Batch0398.cell3185.sound htau (by
                    simp only [Batch0398.cell3185, Batch0398.tau3185, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131110 (by positivity) using 1 <;> norm_num)
                · have hs10131112 : InSquare (25/128) (-221/640) (1/640) tau := by
                    convert childUL hs1013111 hx1013111 hy1013111 using 1 <;> norm_num
                  exact Batch0398.cell3187.sound htau (by
                    simp only [Batch0398.cell3187, Batch0398.tau3187, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-111/320 : ℝ) with hy1013111 | hy1013111
                · have hs10131111 : InSquare (127/640) (-223/640) (1/640) tau := by
                    convert childLR hs1013111 hx1013111 hy1013111 using 1 <;> norm_num
                  exact Batch0398.cell3186.sound htau (by
                    simp only [Batch0398.cell3186, Batch0398.tau3186, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131111 (by positivity) using 1 <;> norm_num)
                · have hs10131113 : InSquare (127/640) (-221/640) (1/640) tau := by
                    convert childUR hs1013111 hx1013111 hy1013111 using 1 <;> norm_num
                  exact Batch0398.cell3188.sound htau (by
                    simp only [Batch0398.cell3188, Batch0398.tau3188, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131113 (by positivity) using 1 <;> norm_num)
            · have hs1013113 : InSquare (63/320) (-109/320) (1/320) tau := by
                convert childUR hs101311 hx101311 hy101311 using 1 <;> norm_num
              exact Batch0213.cell1704.sound htau (by
                simp only [Batch0213.cell1704, Batch0213.tau1704, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013113 (by positivity) using 1 <;> norm_num)
        · have hs101313 : InSquare (31/160) (-53/160) (1/160) tau := by
            convert childUR hs10131 hx10131 hy10131 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx101313 | hx101313
          · rcases le_total tau.im (-53/160 : ℝ) with hy101313 | hy101313
            · have hs1013130 : InSquare (61/320) (-107/320) (1/320) tau := by
                convert childLL hs101313 hx101313 hy101313 using 1 <;> norm_num
              exact Batch0213.cell1709.sound htau (by
                simp only [Batch0213.cell1709, Batch0213.tau1709, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013130 (by positivity) using 1 <;> norm_num)
            · have hs1013132 : InSquare (61/320) (-21/64) (1/320) tau := by
                convert childUL hs101313 hx101313 hy101313 using 1 <;> norm_num
              exact Batch0213.cell1711.sound htau (by
                simp only [Batch0213.cell1711, Batch0213.tau1711, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy101313 | hy101313
            · have hs1013131 : InSquare (63/320) (-107/320) (1/320) tau := by
                convert childLR hs101313 hx101313 hy101313 using 1 <;> norm_num
              exact Batch0213.cell1710.sound htau (by
                simp only [Batch0213.cell1710, Batch0213.tau1710, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013131 (by positivity) using 1 <;> norm_num)
            · have hs1013133 : InSquare (63/320) (-21/64) (1/320) tau := by
                convert childUR hs101313 hx101313 hy101313 using 1 <;> norm_num
              exact Batch0214.cell1712.sound htau (by
                simp only [Batch0214.cell1712, Batch0214.tau1712, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013133 (by positivity) using 1 <;> norm_num)
    · have hs10133 : InSquare (3/16) (-5/16) (1/80) tau := by
        convert childUR hs hx1013 hy1013 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx10133 | hx10133
      · rcases le_total tau.im (-5/16 : ℝ) with hy10133 | hy10133
        · have hs101330 : InSquare (29/160) (-51/160) (1/160) tau := by
            convert childLL hs10133 hx10133 hy10133 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx101330 | hx101330
          · rcases le_total tau.im (-51/160 : ℝ) with hy101330 | hy101330
            · have hs1013300 : InSquare (57/320) (-103/320) (1/320) tau := by
                convert childLL hs101330 hx101330 hy101330 using 1 <;> norm_num
              exact Batch0215.cell1721.sound htau (by
                simp only [Batch0215.cell1721, Batch0215.tau1721, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013300 (by positivity) using 1 <;> norm_num)
            · have hs1013302 : InSquare (57/320) (-101/320) (1/320) tau := by
                convert childUL hs101330 hx101330 hy101330 using 1 <;> norm_num
              exact Batch0215.cell1723.sound htau (by
                simp only [Batch0215.cell1723, Batch0215.tau1723, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy101330 | hy101330
            · have hs1013301 : InSquare (59/320) (-103/320) (1/320) tau := by
                convert childLR hs101330 hx101330 hy101330 using 1 <;> norm_num
              exact Batch0215.cell1722.sound htau (by
                simp only [Batch0215.cell1722, Batch0215.tau1722, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013301 (by positivity) using 1 <;> norm_num)
            · have hs1013303 : InSquare (59/320) (-101/320) (1/320) tau := by
                convert childUR hs101330 hx101330 hy101330 using 1 <;> norm_num
              exact Batch0215.cell1724.sound htau (by
                simp only [Batch0215.cell1724, Batch0215.tau1724, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013303 (by positivity) using 1 <;> norm_num)
        · have hs101332 : InSquare (29/160) (-49/160) (1/160) tau := by
            convert childUL hs10133 hx10133 hy10133 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx101332 | hx101332
          · rcases le_total tau.im (-49/160 : ℝ) with hy101332 | hy101332
            · have hs1013320 : InSquare (57/320) (-99/320) (1/320) tau := by
                convert childLL hs101332 hx101332 hy101332 using 1 <;> norm_num
              exact Batch0216.cell1729.sound htau (by
                simp only [Batch0216.cell1729, Batch0216.tau1729, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013320 (by positivity) using 1 <;> norm_num)
            · have hs1013322 : InSquare (57/320) (-97/320) (1/320) tau := by
                convert childUL hs101332 hx101332 hy101332 using 1 <;> norm_num
              exact Batch0216.cell1731.sound htau (by
                simp only [Batch0216.cell1731, Batch0216.tau1731, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy101332 | hy101332
            · have hs1013321 : InSquare (59/320) (-99/320) (1/320) tau := by
                convert childLR hs101332 hx101332 hy101332 using 1 <;> norm_num
              exact Batch0216.cell1730.sound htau (by
                simp only [Batch0216.cell1730, Batch0216.tau1730, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013321 (by positivity) using 1 <;> norm_num)
            · have hs1013323 : InSquare (59/320) (-97/320) (1/320) tau := by
                convert childUR hs101332 hx101332 hy101332 using 1 <;> norm_num
              exact Batch0216.cell1732.sound htau (by
                simp only [Batch0216.cell1732, Batch0216.tau1732, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10133 | hy10133
        · have hs101331 : InSquare (31/160) (-51/160) (1/160) tau := by
            convert childLR hs10133 hx10133 hy10133 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx101331 | hx101331
          · rcases le_total tau.im (-51/160 : ℝ) with hy101331 | hy101331
            · have hs1013310 : InSquare (61/320) (-103/320) (1/320) tau := by
                convert childLL hs101331 hx101331 hy101331 using 1 <;> norm_num
              exact Batch0215.cell1725.sound htau (by
                simp only [Batch0215.cell1725, Batch0215.tau1725, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013310 (by positivity) using 1 <;> norm_num)
            · have hs1013312 : InSquare (61/320) (-101/320) (1/320) tau := by
                convert childUL hs101331 hx101331 hy101331 using 1 <;> norm_num
              exact Batch0215.cell1727.sound htau (by
                simp only [Batch0215.cell1727, Batch0215.tau1727, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy101331 | hy101331
            · have hs1013311 : InSquare (63/320) (-103/320) (1/320) tau := by
                convert childLR hs101331 hx101331 hy101331 using 1 <;> norm_num
              exact Batch0215.cell1726.sound htau (by
                simp only [Batch0215.cell1726, Batch0215.tau1726, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013311 (by positivity) using 1 <;> norm_num)
            · have hs1013313 : InSquare (63/320) (-101/320) (1/320) tau := by
                convert childUR hs101331 hx101331 hy101331 using 1 <;> norm_num
              exact Batch0216.cell1728.sound htau (by
                simp only [Batch0216.cell1728, Batch0216.tau1728, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013313 (by positivity) using 1 <;> norm_num)
        · have hs101333 : InSquare (31/160) (-49/160) (1/160) tau := by
            convert childUR hs10133 hx10133 hy10133 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx101333 | hx101333
          · rcases le_total tau.im (-49/160 : ℝ) with hy101333 | hy101333
            · have hs1013330 : InSquare (61/320) (-99/320) (1/320) tau := by
                convert childLL hs101333 hx101333 hy101333 using 1 <;> norm_num
              exact Batch0216.cell1733.sound htau (by
                simp only [Batch0216.cell1733, Batch0216.tau1733, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013330 (by positivity) using 1 <;> norm_num)
            · have hs1013332 : InSquare (61/320) (-97/320) (1/320) tau := by
                convert childUL hs101333 hx101333 hy101333 using 1 <;> norm_num
              exact Batch0216.cell1735.sound htau (by
                simp only [Batch0216.cell1735, Batch0216.tau1735, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy101333 | hy101333
            · have hs1013331 : InSquare (63/320) (-99/320) (1/320) tau := by
                convert childLR hs101333 hx101333 hy101333 using 1 <;> norm_num
              exact Batch0216.cell1734.sound htau (by
                simp only [Batch0216.cell1734, Batch0216.tau1734, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013331 (by positivity) using 1 <;> norm_num)
            · have hs1013333 : InSquare (63/320) (-97/320) (1/320) tau := by
                convert childUR hs101333 hx101333 hy101333 using 1 <;> norm_num
              exact Batch0217.cell1736.sound htau (by
                simp only [Batch0217.cell1736, Batch0217.tau1736, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1013

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1020 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1020

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/40 : ℝ) with hx1020 | hx1020
  · rcases le_total tau.im (-11/40 : ℝ) with hy1020 | hy1020
    · have hs10200 : InSquare (1/80) (-23/80) (1/80) tau := by
        convert childLL hs hx1020 hy1020 using 1 <;> norm_num
      exact Batch0015.cell0125.sound htau (by
        simp only [Batch0015.cell0125, Batch0015.tau0125, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10200 (by positivity) using 1 <;> norm_num)
    · have hs10202 : InSquare (1/80) (-21/80) (1/80) tau := by
        convert childUL hs hx1020 hy1020 using 1 <;> norm_num
      exact Batch0015.cell0127.sound htau (by
        simp only [Batch0015.cell0127, Batch0015.tau0127, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10202 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy1020 | hy1020
    · have hs10201 : InSquare (3/80) (-23/80) (1/80) tau := by
        convert childLR hs hx1020 hy1020 using 1 <;> norm_num
      exact Batch0015.cell0126.sound htau (by
        simp only [Batch0015.cell0126, Batch0015.tau0126, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10201 (by positivity) using 1 <;> norm_num)
    · have hs10203 : InSquare (3/80) (-21/80) (1/80) tau := by
        convert childUR hs hx1020 hy1020 using 1 <;> norm_num
      exact Batch0016.cell0128.sound htau (by
        simp only [Batch0016.cell0128, Batch0016.tau0128, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10203 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1020

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1021 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1021

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx1021 | hx1021
  · rcases le_total tau.im (-11/40 : ℝ) with hy1021 | hy1021
    · have hs10210 : InSquare (1/16) (-23/80) (1/80) tau := by
        convert childLL hs hx1021 hy1021 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx10210 | hx10210
      · rcases le_total tau.im (-23/80 : ℝ) with hy10210 | hy10210
        · have hs102100 : InSquare (9/160) (-47/160) (1/160) tau := by
            convert childLL hs10210 hx10210 hy10210 using 1 <;> norm_num
          exact Batch0074.cell0598.sound htau (by
            simp only [Batch0074.cell0598, Batch0074.tau0598, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102100 (by positivity) using 1 <;> norm_num)
        · have hs102102 : InSquare (9/160) (-9/32) (1/160) tau := by
            convert childUL hs10210 hx10210 hy10210 using 1 <;> norm_num
          exact Batch0075.cell0600.sound htau (by
            simp only [Batch0075.cell0600, Batch0075.tau0600, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy10210 | hy10210
        · have hs102101 : InSquare (11/160) (-47/160) (1/160) tau := by
            convert childLR hs10210 hx10210 hy10210 using 1 <;> norm_num
          exact Batch0074.cell0599.sound htau (by
            simp only [Batch0074.cell0599, Batch0074.tau0599, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102101 (by positivity) using 1 <;> norm_num)
        · have hs102103 : InSquare (11/160) (-9/32) (1/160) tau := by
            convert childUR hs10210 hx10210 hy10210 using 1 <;> norm_num
          exact Batch0075.cell0601.sound htau (by
            simp only [Batch0075.cell0601, Batch0075.tau0601, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102103 (by positivity) using 1 <;> norm_num)
    · have hs10212 : InSquare (1/16) (-21/80) (1/80) tau := by
        convert childUL hs hx1021 hy1021 using 1 <;> norm_num
      exact Batch0016.cell0129.sound htau (by
        simp only [Batch0016.cell0129, Batch0016.tau0129, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10212 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy1021 | hy1021
    · have hs10211 : InSquare (7/80) (-23/80) (1/80) tau := by
        convert childLR hs hx1021 hy1021 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx10211 | hx10211
      · rcases le_total tau.im (-23/80 : ℝ) with hy10211 | hy10211
        · have hs102110 : InSquare (13/160) (-47/160) (1/160) tau := by
            convert childLL hs10211 hx10211 hy10211 using 1 <;> norm_num
          exact Batch0075.cell0602.sound htau (by
            simp only [Batch0075.cell0602, Batch0075.tau0602, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102110 (by positivity) using 1 <;> norm_num)
        · have hs102112 : InSquare (13/160) (-9/32) (1/160) tau := by
            convert childUL hs10211 hx10211 hy10211 using 1 <;> norm_num
          exact Batch0075.cell0604.sound htau (by
            simp only [Batch0075.cell0604, Batch0075.tau0604, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy10211 | hy10211
        · have hs102111 : InSquare (3/32) (-47/160) (1/160) tau := by
            convert childLR hs10211 hx10211 hy10211 using 1 <;> norm_num
          exact Batch0075.cell0603.sound htau (by
            simp only [Batch0075.cell0603, Batch0075.tau0603, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102111 (by positivity) using 1 <;> norm_num)
        · have hs102113 : InSquare (3/32) (-9/32) (1/160) tau := by
            convert childUR hs10211 hx10211 hy10211 using 1 <;> norm_num
          exact Batch0075.cell0605.sound htau (by
            simp only [Batch0075.cell0605, Batch0075.tau0605, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102113 (by positivity) using 1 <;> norm_num)
    · have hs10213 : InSquare (7/80) (-21/80) (1/80) tau := by
        convert childUR hs hx1021 hy1021 using 1 <;> norm_num
      exact Batch0016.cell0130.sound htau (by
        simp only [Batch0016.cell0130, Batch0016.tau0130, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10213 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1021

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1022 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1022

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/40 : ℝ) with hx1022 | hx1022
  · rcases le_total tau.im (-9/40 : ℝ) with hy1022 | hy1022
    · have hs10220 : InSquare (1/80) (-19/80) (1/80) tau := by
        convert childLL hs hx1022 hy1022 using 1 <;> norm_num
      exact Batch0016.cell0131.sound htau (by
        simp only [Batch0016.cell0131, Batch0016.tau0131, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10220 (by positivity) using 1 <;> norm_num)
    · have hs10222 : InSquare (1/80) (-17/80) (1/80) tau := by
        convert childUL hs hx1022 hy1022 using 1 <;> norm_num
      exact Batch0016.cell0133.sound htau (by
        simp only [Batch0016.cell0133, Batch0016.tau0133, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10222 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy1022 | hy1022
    · have hs10221 : InSquare (3/80) (-19/80) (1/80) tau := by
        convert childLR hs hx1022 hy1022 using 1 <;> norm_num
      exact Batch0016.cell0132.sound htau (by
        simp only [Batch0016.cell0132, Batch0016.tau0132, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10221 (by positivity) using 1 <;> norm_num)
    · have hs10223 : InSquare (3/80) (-17/80) (1/80) tau := by
        convert childUR hs hx1022 hy1022 using 1 <;> norm_num
      exact Batch0016.cell0134.sound htau (by
        simp only [Batch0016.cell0134, Batch0016.tau0134, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10223 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1022

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1023 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1023

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx1023 | hx1023
  · rcases le_total tau.im (-9/40 : ℝ) with hy1023 | hy1023
    · have hs10230 : InSquare (1/16) (-19/80) (1/80) tau := by
        convert childLL hs hx1023 hy1023 using 1 <;> norm_num
      exact Batch0016.cell0135.sound htau (by
        simp only [Batch0016.cell0135, Batch0016.tau0135, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10230 (by positivity) using 1 <;> norm_num)
    · have hs10232 : InSquare (1/16) (-17/80) (1/80) tau := by
        convert childUL hs hx1023 hy1023 using 1 <;> norm_num
      exact Batch0017.cell0137.sound htau (by
        simp only [Batch0017.cell0137, Batch0017.tau0137, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10232 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy1023 | hy1023
    · have hs10231 : InSquare (7/80) (-19/80) (1/80) tau := by
        convert childLR hs hx1023 hy1023 using 1 <;> norm_num
      exact Batch0017.cell0136.sound htau (by
        simp only [Batch0017.cell0136, Batch0017.tau0136, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10231 (by positivity) using 1 <;> norm_num)
    · have hs10233 : InSquare (7/80) (-17/80) (1/80) tau := by
        convert childUR hs hx1023 hy1023 using 1 <;> norm_num
      exact Batch0017.cell0138.sound htau (by
        simp only [Batch0017.cell0138, Batch0017.tau0138, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1023

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1030 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1030

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx1030 | hx1030
  · rcases le_total tau.im (-11/40 : ℝ) with hy1030 | hy1030
    · have hs10300 : InSquare (9/80) (-23/80) (1/80) tau := by
        convert childLL hs hx1030 hy1030 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx10300 | hx10300
      · rcases le_total tau.im (-23/80 : ℝ) with hy10300 | hy10300
        · have hs103000 : InSquare (17/160) (-47/160) (1/160) tau := by
            convert childLL hs10300 hx10300 hy10300 using 1 <;> norm_num
          exact Batch0075.cell0606.sound htau (by
            simp only [Batch0075.cell0606, Batch0075.tau0606, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103000 (by positivity) using 1 <;> norm_num)
        · have hs103002 : InSquare (17/160) (-9/32) (1/160) tau := by
            convert childUL hs10300 hx10300 hy10300 using 1 <;> norm_num
          exact Batch0076.cell0608.sound htau (by
            simp only [Batch0076.cell0608, Batch0076.tau0608, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy10300 | hy10300
        · have hs103001 : InSquare (19/160) (-47/160) (1/160) tau := by
            convert childLR hs10300 hx10300 hy10300 using 1 <;> norm_num
          exact Batch0075.cell0607.sound htau (by
            simp only [Batch0075.cell0607, Batch0075.tau0607, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103001 (by positivity) using 1 <;> norm_num)
        · have hs103003 : InSquare (19/160) (-9/32) (1/160) tau := by
            convert childUR hs10300 hx10300 hy10300 using 1 <;> norm_num
          exact Batch0076.cell0609.sound htau (by
            simp only [Batch0076.cell0609, Batch0076.tau0609, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103003 (by positivity) using 1 <;> norm_num)
    · have hs10302 : InSquare (9/80) (-21/80) (1/80) tau := by
        convert childUL hs hx1030 hy1030 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx10302 | hx10302
      · rcases le_total tau.im (-21/80 : ℝ) with hy10302 | hy10302
        · have hs103020 : InSquare (17/160) (-43/160) (1/160) tau := by
            convert childLL hs10302 hx10302 hy10302 using 1 <;> norm_num
          exact Batch0076.cell0614.sound htau (by
            simp only [Batch0076.cell0614, Batch0076.tau0614, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103020 (by positivity) using 1 <;> norm_num)
        · have hs103022 : InSquare (17/160) (-41/160) (1/160) tau := by
            convert childUL hs10302 hx10302 hy10302 using 1 <;> norm_num
          exact Batch0077.cell0616.sound htau (by
            simp only [Batch0077.cell0616, Batch0077.tau0616, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy10302 | hy10302
        · have hs103021 : InSquare (19/160) (-43/160) (1/160) tau := by
            convert childLR hs10302 hx10302 hy10302 using 1 <;> norm_num
          exact Batch0076.cell0615.sound htau (by
            simp only [Batch0076.cell0615, Batch0076.tau0615, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103021 (by positivity) using 1 <;> norm_num)
        · have hs103023 : InSquare (19/160) (-41/160) (1/160) tau := by
            convert childUR hs10302 hx10302 hy10302 using 1 <;> norm_num
          exact Batch0077.cell0617.sound htau (by
            simp only [Batch0077.cell0617, Batch0077.tau0617, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy1030 | hy1030
    · have hs10301 : InSquare (11/80) (-23/80) (1/80) tau := by
        convert childLR hs hx1030 hy1030 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx10301 | hx10301
      · rcases le_total tau.im (-23/80 : ℝ) with hy10301 | hy10301
        · have hs103010 : InSquare (21/160) (-47/160) (1/160) tau := by
            convert childLL hs10301 hx10301 hy10301 using 1 <;> norm_num
          exact Batch0076.cell0610.sound htau (by
            simp only [Batch0076.cell0610, Batch0076.tau0610, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103010 (by positivity) using 1 <;> norm_num)
        · have hs103012 : InSquare (21/160) (-9/32) (1/160) tau := by
            convert childUL hs10301 hx10301 hy10301 using 1 <;> norm_num
          exact Batch0076.cell0612.sound htau (by
            simp only [Batch0076.cell0612, Batch0076.tau0612, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy10301 | hy10301
        · have hs103011 : InSquare (23/160) (-47/160) (1/160) tau := by
            convert childLR hs10301 hx10301 hy10301 using 1 <;> norm_num
          exact Batch0076.cell0611.sound htau (by
            simp only [Batch0076.cell0611, Batch0076.tau0611, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103011 (by positivity) using 1 <;> norm_num)
        · have hs103013 : InSquare (23/160) (-9/32) (1/160) tau := by
            convert childUR hs10301 hx10301 hy10301 using 1 <;> norm_num
          exact Batch0076.cell0613.sound htau (by
            simp only [Batch0076.cell0613, Batch0076.tau0613, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103013 (by positivity) using 1 <;> norm_num)
    · have hs10303 : InSquare (11/80) (-21/80) (1/80) tau := by
        convert childUR hs hx1030 hy1030 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx10303 | hx10303
      · rcases le_total tau.im (-21/80 : ℝ) with hy10303 | hy10303
        · have hs103030 : InSquare (21/160) (-43/160) (1/160) tau := by
            convert childLL hs10303 hx10303 hy10303 using 1 <;> norm_num
          exact Batch0077.cell0618.sound htau (by
            simp only [Batch0077.cell0618, Batch0077.tau0618, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103030 (by positivity) using 1 <;> norm_num)
        · have hs103032 : InSquare (21/160) (-41/160) (1/160) tau := by
            convert childUL hs10303 hx10303 hy10303 using 1 <;> norm_num
          exact Batch0077.cell0620.sound htau (by
            simp only [Batch0077.cell0620, Batch0077.tau0620, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy10303 | hy10303
        · have hs103031 : InSquare (23/160) (-43/160) (1/160) tau := by
            convert childLR hs10303 hx10303 hy10303 using 1 <;> norm_num
          exact Batch0077.cell0619.sound htau (by
            simp only [Batch0077.cell0619, Batch0077.tau0619, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103031 (by positivity) using 1 <;> norm_num)
        · have hs103033 : InSquare (23/160) (-41/160) (1/160) tau := by
            convert childUR hs10303 hx10303 hy10303 using 1 <;> norm_num
          exact Batch0077.cell0621.sound htau (by
            simp only [Batch0077.cell0621, Batch0077.tau0621, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1030

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1031 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1031

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx1031 | hx1031
  · rcases le_total tau.im (-11/40 : ℝ) with hy1031 | hy1031
    · have hs10310 : InSquare (13/80) (-23/80) (1/80) tau := by
        convert childLL hs hx1031 hy1031 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx10310 | hx10310
      · rcases le_total tau.im (-23/80 : ℝ) with hy10310 | hy10310
        · have hs103100 : InSquare (5/32) (-47/160) (1/160) tau := by
            convert childLL hs10310 hx10310 hy10310 using 1 <;> norm_num
          exact Batch0077.cell0622.sound htau (by
            simp only [Batch0077.cell0622, Batch0077.tau0622, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103100 (by positivity) using 1 <;> norm_num)
        · have hs103102 : InSquare (5/32) (-9/32) (1/160) tau := by
            convert childUL hs10310 hx10310 hy10310 using 1 <;> norm_num
          exact Batch0078.cell0624.sound htau (by
            simp only [Batch0078.cell0624, Batch0078.tau0624, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy10310 | hy10310
        · have hs103101 : InSquare (27/160) (-47/160) (1/160) tau := by
            convert childLR hs10310 hx10310 hy10310 using 1 <;> norm_num
          exact Batch0077.cell0623.sound htau (by
            simp only [Batch0077.cell0623, Batch0077.tau0623, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103101 (by positivity) using 1 <;> norm_num)
        · have hs103103 : InSquare (27/160) (-9/32) (1/160) tau := by
            convert childUR hs10310 hx10310 hy10310 using 1 <;> norm_num
          exact Batch0078.cell0625.sound htau (by
            simp only [Batch0078.cell0625, Batch0078.tau0625, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103103 (by positivity) using 1 <;> norm_num)
    · have hs10312 : InSquare (13/80) (-21/80) (1/80) tau := by
        convert childUL hs hx1031 hy1031 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx10312 | hx10312
      · rcases le_total tau.im (-21/80 : ℝ) with hy10312 | hy10312
        · have hs103120 : InSquare (5/32) (-43/160) (1/160) tau := by
            convert childLL hs10312 hx10312 hy10312 using 1 <;> norm_num
          exact Batch0078.cell0630.sound htau (by
            simp only [Batch0078.cell0630, Batch0078.tau0630, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103120 (by positivity) using 1 <;> norm_num)
        · have hs103122 : InSquare (5/32) (-41/160) (1/160) tau := by
            convert childUL hs10312 hx10312 hy10312 using 1 <;> norm_num
          exact Batch0079.cell0632.sound htau (by
            simp only [Batch0079.cell0632, Batch0079.tau0632, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy10312 | hy10312
        · have hs103121 : InSquare (27/160) (-43/160) (1/160) tau := by
            convert childLR hs10312 hx10312 hy10312 using 1 <;> norm_num
          exact Batch0078.cell0631.sound htau (by
            simp only [Batch0078.cell0631, Batch0078.tau0631, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103121 (by positivity) using 1 <;> norm_num)
        · have hs103123 : InSquare (27/160) (-41/160) (1/160) tau := by
            convert childUR hs10312 hx10312 hy10312 using 1 <;> norm_num
          exact Batch0079.cell0633.sound htau (by
            simp only [Batch0079.cell0633, Batch0079.tau0633, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy1031 | hy1031
    · have hs10311 : InSquare (3/16) (-23/80) (1/80) tau := by
        convert childLR hs hx1031 hy1031 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx10311 | hx10311
      · rcases le_total tau.im (-23/80 : ℝ) with hy10311 | hy10311
        · have hs103110 : InSquare (29/160) (-47/160) (1/160) tau := by
            convert childLL hs10311 hx10311 hy10311 using 1 <;> norm_num
          exact Batch0078.cell0626.sound htau (by
            simp only [Batch0078.cell0626, Batch0078.tau0626, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103110 (by positivity) using 1 <;> norm_num)
        · have hs103112 : InSquare (29/160) (-9/32) (1/160) tau := by
            convert childUL hs10311 hx10311 hy10311 using 1 <;> norm_num
          exact Batch0078.cell0628.sound htau (by
            simp only [Batch0078.cell0628, Batch0078.tau0628, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy10311 | hy10311
        · have hs103111 : InSquare (31/160) (-47/160) (1/160) tau := by
            convert childLR hs10311 hx10311 hy10311 using 1 <;> norm_num
          exact Batch0078.cell0627.sound htau (by
            simp only [Batch0078.cell0627, Batch0078.tau0627, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103111 (by positivity) using 1 <;> norm_num)
        · have hs103113 : InSquare (31/160) (-9/32) (1/160) tau := by
            convert childUR hs10311 hx10311 hy10311 using 1 <;> norm_num
          exact Batch0078.cell0629.sound htau (by
            simp only [Batch0078.cell0629, Batch0078.tau0629, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103113 (by positivity) using 1 <;> norm_num)
    · have hs10313 : InSquare (3/16) (-21/80) (1/80) tau := by
        convert childUR hs hx1031 hy1031 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx10313 | hx10313
      · rcases le_total tau.im (-21/80 : ℝ) with hy10313 | hy10313
        · have hs103130 : InSquare (29/160) (-43/160) (1/160) tau := by
            convert childLL hs10313 hx10313 hy10313 using 1 <;> norm_num
          exact Batch0079.cell0634.sound htau (by
            simp only [Batch0079.cell0634, Batch0079.tau0634, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103130 (by positivity) using 1 <;> norm_num)
        · have hs103132 : InSquare (29/160) (-41/160) (1/160) tau := by
            convert childUL hs10313 hx10313 hy10313 using 1 <;> norm_num
          exact Batch0079.cell0636.sound htau (by
            simp only [Batch0079.cell0636, Batch0079.tau0636, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy10313 | hy10313
        · have hs103131 : InSquare (31/160) (-43/160) (1/160) tau := by
            convert childLR hs10313 hx10313 hy10313 using 1 <;> norm_num
          exact Batch0079.cell0635.sound htau (by
            simp only [Batch0079.cell0635, Batch0079.tau0635, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103131 (by positivity) using 1 <;> norm_num)
        · have hs103133 : InSquare (31/160) (-41/160) (1/160) tau := by
            convert childUR hs10313 hx10313 hy10313 using 1 <;> norm_num
          exact Batch0079.cell0637.sound htau (by
            simp only [Batch0079.cell0637, Batch0079.tau0637, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1031

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1032 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1032

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx1032 | hx1032
  · rcases le_total tau.im (-9/40 : ℝ) with hy1032 | hy1032
    · have hs10320 : InSquare (9/80) (-19/80) (1/80) tau := by
        convert childLL hs hx1032 hy1032 using 1 <;> norm_num
      exact Batch0017.cell0139.sound htau (by
        simp only [Batch0017.cell0139, Batch0017.tau0139, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10320 (by positivity) using 1 <;> norm_num)
    · have hs10322 : InSquare (9/80) (-17/80) (1/80) tau := by
        convert childUL hs hx1032 hy1032 using 1 <;> norm_num
      exact Batch0017.cell0141.sound htau (by
        simp only [Batch0017.cell0141, Batch0017.tau0141, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10322 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy1032 | hy1032
    · have hs10321 : InSquare (11/80) (-19/80) (1/80) tau := by
        convert childLR hs hx1032 hy1032 using 1 <;> norm_num
      exact Batch0017.cell0140.sound htau (by
        simp only [Batch0017.cell0140, Batch0017.tau0140, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10321 (by positivity) using 1 <;> norm_num)
    · have hs10323 : InSquare (11/80) (-17/80) (1/80) tau := by
        convert childUR hs hx1032 hy1032 using 1 <;> norm_num
      exact Batch0017.cell0142.sound htau (by
        simp only [Batch0017.cell0142, Batch0017.tau0142, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10323 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1032

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1033 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1033

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx1033 | hx1033
  · rcases le_total tau.im (-9/40 : ℝ) with hy1033 | hy1033
    · have hs10330 : InSquare (13/80) (-19/80) (1/80) tau := by
        convert childLL hs hx1033 hy1033 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx10330 | hx10330
      · rcases le_total tau.im (-19/80 : ℝ) with hy10330 | hy10330
        · have hs103300 : InSquare (5/32) (-39/160) (1/160) tau := by
            convert childLL hs10330 hx10330 hy10330 using 1 <;> norm_num
          exact Batch0079.cell0638.sound htau (by
            simp only [Batch0079.cell0638, Batch0079.tau0638, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103300 (by positivity) using 1 <;> norm_num)
        · have hs103302 : InSquare (5/32) (-37/160) (1/160) tau := by
            convert childUL hs10330 hx10330 hy10330 using 1 <;> norm_num
          exact Batch0080.cell0640.sound htau (by
            simp only [Batch0080.cell0640, Batch0080.tau0640, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy10330 | hy10330
        · have hs103301 : InSquare (27/160) (-39/160) (1/160) tau := by
            convert childLR hs10330 hx10330 hy10330 using 1 <;> norm_num
          exact Batch0079.cell0639.sound htau (by
            simp only [Batch0079.cell0639, Batch0079.tau0639, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103301 (by positivity) using 1 <;> norm_num)
        · have hs103303 : InSquare (27/160) (-37/160) (1/160) tau := by
            convert childUR hs10330 hx10330 hy10330 using 1 <;> norm_num
          exact Batch0080.cell0641.sound htau (by
            simp only [Batch0080.cell0641, Batch0080.tau0641, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103303 (by positivity) using 1 <;> norm_num)
    · have hs10332 : InSquare (13/80) (-17/80) (1/80) tau := by
        convert childUL hs hx1033 hy1033 using 1 <;> norm_num
      exact Batch0017.cell0143.sound htau (by
        simp only [Batch0017.cell0143, Batch0017.tau0143, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10332 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy1033 | hy1033
    · have hs10331 : InSquare (3/16) (-19/80) (1/80) tau := by
        convert childLR hs hx1033 hy1033 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx10331 | hx10331
      · rcases le_total tau.im (-19/80 : ℝ) with hy10331 | hy10331
        · have hs103310 : InSquare (29/160) (-39/160) (1/160) tau := by
            convert childLL hs10331 hx10331 hy10331 using 1 <;> norm_num
          exact Batch0080.cell0642.sound htau (by
            simp only [Batch0080.cell0642, Batch0080.tau0642, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103310 (by positivity) using 1 <;> norm_num)
        · have hs103312 : InSquare (29/160) (-37/160) (1/160) tau := by
            convert childUL hs10331 hx10331 hy10331 using 1 <;> norm_num
          exact Batch0080.cell0644.sound htau (by
            simp only [Batch0080.cell0644, Batch0080.tau0644, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy10331 | hy10331
        · have hs103311 : InSquare (31/160) (-39/160) (1/160) tau := by
            convert childLR hs10331 hx10331 hy10331 using 1 <;> norm_num
          exact Batch0080.cell0643.sound htau (by
            simp only [Batch0080.cell0643, Batch0080.tau0643, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103311 (by positivity) using 1 <;> norm_num)
        · have hs103313 : InSquare (31/160) (-37/160) (1/160) tau := by
            convert childUR hs10331 hx10331 hy10331 using 1 <;> norm_num
          exact Batch0080.cell0645.sound htau (by
            simp only [Batch0080.cell0645, Batch0080.tau0645, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103313 (by positivity) using 1 <;> norm_num)
    · have hs10333 : InSquare (3/16) (-17/80) (1/80) tau := by
        convert childUR hs hx1033 hy1033 using 1 <;> norm_num
      exact Batch0018.cell0144.sound htau (by
        simp only [Batch0018.cell0144, Batch0018.tau0144, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1033

end


