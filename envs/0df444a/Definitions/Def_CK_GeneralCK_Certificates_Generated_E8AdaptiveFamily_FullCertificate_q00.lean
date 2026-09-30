-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_FullCertificate_q00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_FullCertificate_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T03:53:25.299578+00:00
-- url     : https://prove2.me/theorems/e5c1e4b7-0a85-428e-a561-8cb141b41923
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/FullCertificate (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage0012__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage0031__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage0102__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage0120__18
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage0222__10
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage1001__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage1011__11
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage1102__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage1132__16
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage1330__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2003__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2020__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2032__8
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2210__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2231__11
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2322__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2332__8
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage3103__11
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage3132__13
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage3223__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage3233__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage3320__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0000
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0001
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0002
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0003
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0004
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0005
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0006



namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema CoverageKernel

theorem outside_000_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/20) (-7/20) (1/20) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/10)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_111_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/20) (-7/20) (1/20) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/10)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_222_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/20) (7/20) (1/20) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/10)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_333_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/20) (7/20) (1/20) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/10)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_0010_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (-3/8) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/4)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_0011_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (-3/8) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/5 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/5)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_0020_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (-11/40) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/20)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate


