-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_FullCertificate_q01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_FullCertificate_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:04:10.161841+00:00
-- url     : https://prove2.me/theorems/7e213e51-22a6-4086-a5eb-856f1d94fe91
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/FullCertificate (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_FullCertificate_q00

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate
open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema CoverageKernel
theorem outside_0022_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (-9/40) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/20)]
  have himSq : (1/5 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/5)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_1100_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (-3/8) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/5 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/5)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_1101_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (-3/8) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/4)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_1131_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (-11/40) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/20)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_1133_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (-9/40) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/20)]
  have himSq : (1/5 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/5)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_2200_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (9/40) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/20)]
  have himSq : (1/5 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/5)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_2202_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (11/40) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/20)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate


