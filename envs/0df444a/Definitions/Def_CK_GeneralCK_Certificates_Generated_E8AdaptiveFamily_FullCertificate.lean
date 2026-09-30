-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_FullCertificate
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_FullCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:37:57.842382+00:00
-- url     : https://prove2.me/theorems/0c4e5872-7131-4425-b645-cd74d9081d39
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/FullCertificate.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_FullCertificate_q01

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate
open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema CoverageKernel
theorem outside_2232_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (3/8) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/4)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_2233_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (3/8) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/5 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/5)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_3311_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (9/40) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/20)]
  have himSq : (1/5 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/5)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_3313_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (11/40) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/20)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_3322_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (3/8) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/5 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/5)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem outside_3323_priv {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (3/8) (1/40) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/4)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem global_derivative_bound (tau : ℂ) (htau : ‖tau‖ ≤ (2/5 : ℝ)) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (0 : ℝ) with hxroot | hxroot
  · rcases le_total tau.im (0 : ℝ) with hyroot | hyroot
    · have hs0 : InSquare (-1/5) (-1/5) (1/5) tau := by
        convert childLL (disc_in_root htau) hxroot hyroot using 1 <;> norm_num
      rcases le_total tau.re (-1/5 : ℝ) with hx0 | hx0
      · rcases le_total tau.im (-1/5 : ℝ) with hy0 | hy0
        · have hs00 : InSquare (-3/10) (-3/10) (1/10) tau := by
            convert childLL hs0 hx0 hy0 using 1 <;> norm_num
          rcases le_total tau.re (-3/10 : ℝ) with hx00 | hx00
          · rcases le_total tau.im (-3/10 : ℝ) with hy00 | hy00
            · have hs000 : InSquare (-7/20) (-7/20) (1/20) tau := by
                convert childLL hs00 hx00 hy00 using 1 <;> norm_num
              exact (outside_000_priv htau hs000).elim
            · have hs002 : InSquare (-7/20) (-1/4) (1/20) tau := by
                convert childUL hs00 hx00 hy00 using 1 <;> norm_num
              rcases le_total tau.re (-7/20 : ℝ) with hx002 | hx002
              · rcases le_total tau.im (-1/4 : ℝ) with hy002 | hy002
                · have hs0020 : InSquare (-3/8) (-11/40) (1/40) tau := by
                    convert childLL hs002 hx002 hy002 using 1 <;> norm_num
                  exact (outside_0020_priv htau hs0020).elim
                · have hs0022 : InSquare (-3/8) (-9/40) (1/40) tau := by
                    convert childUL hs002 hx002 hy002 using 1 <;> norm_num
                  exact (outside_0022_priv htau hs0022).elim
              · rcases le_total tau.im (-1/4 : ℝ) with hy002 | hy002
                · have hs0021 : InSquare (-13/40) (-11/40) (1/40) tau := by
                    convert childLR hs002 hx002 hy002 using 1 <;> norm_num
                  exact Coverage0021.cover htau hs0021
                · have hs0023 : InSquare (-13/40) (-9/40) (1/40) tau := by
                    convert childUR hs002 hx002 hy002 using 1 <;> norm_num
                  exact Coverage0023.cover htau hs0023
          · rcases le_total tau.im (-3/10 : ℝ) with hy00 | hy00
            · have hs001 : InSquare (-1/4) (-7/20) (1/20) tau := by
                convert childLR hs00 hx00 hy00 using 1 <;> norm_num
              rcases le_total tau.re (-1/4 : ℝ) with hx001 | hx001
              · rcases le_total tau.im (-7/20 : ℝ) with hy001 | hy001
                · have hs0010 : InSquare (-11/40) (-3/8) (1/40) tau := by
                    convert childLL hs001 hx001 hy001 using 1 <;> norm_num
                  exact (outside_0010_priv htau hs0010).elim
                · have hs0012 : InSquare (-11/40) (-13/40) (1/40) tau := by
                    convert childUL hs001 hx001 hy001 using 1 <;> norm_num
                  exact Coverage0012.cover htau hs0012
              · rcases le_total tau.im (-7/20 : ℝ) with hy001 | hy001
                · have hs0011 : InSquare (-9/40) (-3/8) (1/40) tau := by
                    convert childLR hs001 hx001 hy001 using 1 <;> norm_num
                  exact (outside_0011_priv htau hs0011).elim
                · have hs0013 : InSquare (-9/40) (-13/40) (1/40) tau := by
                    convert childUR hs001 hx001 hy001 using 1 <;> norm_num
                  exact Coverage0013.cover htau hs0013
            · have hs003 : InSquare (-1/4) (-1/4) (1/20) tau := by
                convert childUR hs00 hx00 hy00 using 1 <;> norm_num
              rcases le_total tau.re (-1/4 : ℝ) with hx003 | hx003
              · rcases le_total tau.im (-1/4 : ℝ) with hy003 | hy003
                · have hs0030 : InSquare (-11/40) (-11/40) (1/40) tau := by
                    convert childLL hs003 hx003 hy003 using 1 <;> norm_num
                  exact Coverage0030.cover htau hs0030
                · have hs0032 : InSquare (-11/40) (-9/40) (1/40) tau := by
                    convert childUL hs003 hx003 hy003 using 1 <;> norm_num
                  exact Coverage0032.cover htau hs0032
              · rcases le_total tau.im (-1/4 : ℝ) with hy003 | hy003
                · have hs0031 : InSquare (-9/40) (-11/40) (1/40) tau := by
                    convert childLR hs003 hx003 hy003 using 1 <;> norm_num
                  exact Coverage0031.cover htau hs0031
                · have hs0033 : InSquare (-9/40) (-9/40) (1/40) tau := by
                    convert childUR hs003 hx003 hy003 using 1 <;> norm_num
                  exact Coverage0033.cover htau hs0033
        · have hs02 : InSquare (-3/10) (-1/10) (1/10) tau := by
            convert childUL hs0 hx0 hy0 using 1 <;> norm_num
          rcases le_total tau.re (-3/10 : ℝ) with hx02 | hx02
          · rcases le_total tau.im (-1/10 : ℝ) with hy02 | hy02
            · have hs020 : InSquare (-7/20) (-3/20) (1/20) tau := by
                convert childLL hs02 hx02 hy02 using 1 <;> norm_num
              rcases le_total tau.re (-7/20 : ℝ) with hx020 | hx020
              · rcases le_total tau.im (-3/20 : ℝ) with hy020 | hy020
                · have hs0200 : InSquare (-3/8) (-7/40) (1/40) tau := by
                    convert childLL hs020 hx020 hy020 using 1 <;> norm_num
                  exact Coverage0200.cover htau hs0200
                · have hs0202 : InSquare (-3/8) (-1/8) (1/40) tau := by
                    convert childUL hs020 hx020 hy020 using 1 <;> norm_num
                  exact Coverage0202.cover htau hs0202
              · rcases le_total tau.im (-3/20 : ℝ) with hy020 | hy020
                · have hs0201 : InSquare (-13/40) (-7/40) (1/40) tau := by
                    convert childLR hs020 hx020 hy020 using 1 <;> norm_num
                  exact Coverage0201.cover htau hs0201
                · have hs0203 : InSquare (-13/40) (-1/8) (1/40) tau := by
                    convert childUR hs020 hx020 hy020 using 1 <;> norm_num
                  exact Coverage0203.cover htau hs0203
            · have hs022 : InSquare (-7/20) (-1/20) (1/20) tau := by
                convert childUL hs02 hx02 hy02 using 1 <;> norm_num
              rcases le_total tau.re (-7/20 : ℝ) with hx022 | hx022
              · rcases le_total tau.im (-1/20 : ℝ) with hy022 | hy022
                · have hs0220 : InSquare (-3/8) (-3/40) (1/40) tau := by
                    convert childLL hs022 hx022 hy022 using 1 <;> norm_num
                  exact Coverage0220.cover htau hs0220
                · have hs0222 : InSquare (-3/8) (-1/40) (1/40) tau := by
                    convert childUL hs022 hx022 hy022 using 1 <;> norm_num
                  exact Coverage0222.cover htau hs0222
              · rcases le_total tau.im (-1/20 : ℝ) with hy022 | hy022
                · have hs0221 : InSquare (-13/40) (-3/40) (1/40) tau := by
                    convert childLR hs022 hx022 hy022 using 1 <;> norm_num
                  exact Coverage0221.cover htau hs0221
                · have hs0223 : InSquare (-13/40) (-1/40) (1/40) tau := by
                    convert childUR hs022 hx022 hy022 using 1 <;> norm_num
                  exact Coverage0223.cover htau hs0223
          · rcases le_total tau.im (-1/10 : ℝ) with hy02 | hy02
            · have hs021 : InSquare (-1/4) (-3/20) (1/20) tau := by
                convert childLR hs02 hx02 hy02 using 1 <;> norm_num
              rcases le_total tau.re (-1/4 : ℝ) with hx021 | hx021
              · rcases le_total tau.im (-3/20 : ℝ) with hy021 | hy021
                · have hs0210 : InSquare (-11/40) (-7/40) (1/40) tau := by
                    convert childLL hs021 hx021 hy021 using 1 <;> norm_num
                  exact Coverage0210.cover htau hs0210
                · have hs0212 : InSquare (-11/40) (-1/8) (1/40) tau := by
                    convert childUL hs021 hx021 hy021 using 1 <;> norm_num
                  exact Coverage0212.cover htau hs0212
              · rcases le_total tau.im (-3/20 : ℝ) with hy021 | hy021
                · have hs0211 : InSquare (-9/40) (-7/40) (1/40) tau := by
                    convert childLR hs021 hx021 hy021 using 1 <;> norm_num
                  exact Coverage0211.cover htau hs0211
                · have hs0213 : InSquare (-9/40) (-1/8) (1/40) tau := by
                    convert childUR hs021 hx021 hy021 using 1 <;> norm_num
                  exact Coverage0213.cover htau hs0213
            · have hs023 : InSquare (-1/4) (-1/20) (1/20) tau := by
                convert childUR hs02 hx02 hy02 using 1 <;> norm_num
              rcases le_total tau.re (-1/4 : ℝ) with hx023 | hx023
              · rcases le_total tau.im (-1/20 : ℝ) with hy023 | hy023
                · have hs0230 : InSquare (-11/40) (-3/40) (1/40) tau := by
                    convert childLL hs023 hx023 hy023 using 1 <;> norm_num
                  exact Coverage0230.cover htau hs0230
                · have hs0232 : InSquare (-11/40) (-1/40) (1/40) tau := by
                    convert childUL hs023 hx023 hy023 using 1 <;> norm_num
                  exact Coverage0232.cover htau hs0232
              · rcases le_total tau.im (-1/20 : ℝ) with hy023 | hy023
                · have hs0231 : InSquare (-9/40) (-3/40) (1/40) tau := by
                    convert childLR hs023 hx023 hy023 using 1 <;> norm_num
                  exact Coverage0231.cover htau hs0231
                · have hs0233 : InSquare (-9/40) (-1/40) (1/40) tau := by
                    convert childUR hs023 hx023 hy023 using 1 <;> norm_num
                  exact Batch0000.cell0000.sound htau (by
                    simp only [Batch0000.cell0000, Batch0000.tau0000, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs0233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-1/5 : ℝ) with hy0 | hy0
        · have hs01 : InSquare (-1/10) (-3/10) (1/10) tau := by
            convert childLR hs0 hx0 hy0 using 1 <;> norm_num
          rcases le_total tau.re (-1/10 : ℝ) with hx01 | hx01
          · rcases le_total tau.im (-3/10 : ℝ) with hy01 | hy01
            · have hs010 : InSquare (-3/20) (-7/20) (1/20) tau := by
                convert childLL hs01 hx01 hy01 using 1 <;> norm_num
              rcases le_total tau.re (-3/20 : ℝ) with hx010 | hx010
              · rcases le_total tau.im (-7/20 : ℝ) with hy010 | hy010
                · have hs0100 : InSquare (-7/40) (-3/8) (1/40) tau := by
                    convert childLL hs010 hx010 hy010 using 1 <;> norm_num
                  exact Coverage0100.cover htau hs0100
                · have hs0102 : InSquare (-7/40) (-13/40) (1/40) tau := by
                    convert childUL hs010 hx010 hy010 using 1 <;> norm_num
                  exact Coverage0102.cover htau hs0102
              · rcases le_total tau.im (-7/20 : ℝ) with hy010 | hy010
                · have hs0101 : InSquare (-1/8) (-3/8) (1/40) tau := by
                    convert childLR hs010 hx010 hy010 using 1 <;> norm_num
                  exact Coverage0101.cover htau hs0101
                · have hs0103 : InSquare (-1/8) (-13/40) (1/40) tau := by
                    convert childUR hs010 hx010 hy010 using 1 <;> norm_num
                  exact Coverage0103.cover htau hs0103
            · have hs012 : InSquare (-3/20) (-1/4) (1/20) tau := by
                convert childUL hs01 hx01 hy01 using 1 <;> norm_num
              rcases le_total tau.re (-3/20 : ℝ) with hx012 | hx012
              · rcases le_total tau.im (-1/4 : ℝ) with hy012 | hy012
                · have hs0120 : InSquare (-7/40) (-11/40) (1/40) tau := by
                    convert childLL hs012 hx012 hy012 using 1 <;> norm_num
                  exact Coverage0120.cover htau hs0120
                · have hs0122 : InSquare (-7/40) (-9/40) (1/40) tau := by
                    convert childUL hs012 hx012 hy012 using 1 <;> norm_num
                  exact Coverage0122.cover htau hs0122
              · rcases le_total tau.im (-1/4 : ℝ) with hy012 | hy012
                · have hs0121 : InSquare (-1/8) (-11/40) (1/40) tau := by
                    convert childLR hs012 hx012 hy012 using 1 <;> norm_num
                  exact Coverage0121.cover htau hs0121
                · have hs0123 : InSquare (-1/8) (-9/40) (1/40) tau := by
                    convert childUR hs012 hx012 hy012 using 1 <;> norm_num
                  exact Coverage0123.cover htau hs0123
          · rcases le_total tau.im (-3/10 : ℝ) with hy01 | hy01
            · have hs011 : InSquare (-1/20) (-7/20) (1/20) tau := by
                convert childLR hs01 hx01 hy01 using 1 <;> norm_num
              rcases le_total tau.re (-1/20 : ℝ) with hx011 | hx011
              · rcases le_total tau.im (-7/20 : ℝ) with hy011 | hy011
                · have hs0110 : InSquare (-3/40) (-3/8) (1/40) tau := by
                    convert childLL hs011 hx011 hy011 using 1 <;> norm_num
                  exact Coverage0110.cover htau hs0110
                · have hs0112 : InSquare (-3/40) (-13/40) (1/40) tau := by
                    convert childUL hs011 hx011 hy011 using 1 <;> norm_num
                  exact Coverage0112.cover htau hs0112
              · rcases le_total tau.im (-7/20 : ℝ) with hy011 | hy011
                · have hs0111 : InSquare (-1/40) (-3/8) (1/40) tau := by
                    convert childLR hs011 hx011 hy011 using 1 <;> norm_num
                  exact Coverage0111.cover htau hs0111
                · have hs0113 : InSquare (-1/40) (-13/40) (1/40) tau := by
                    convert childUR hs011 hx011 hy011 using 1 <;> norm_num
                  exact Coverage0113.cover htau hs0113
            · have hs013 : InSquare (-1/20) (-1/4) (1/20) tau := by
                convert childUR hs01 hx01 hy01 using 1 <;> norm_num
              rcases le_total tau.re (-1/20 : ℝ) with hx013 | hx013
              · rcases le_total tau.im (-1/4 : ℝ) with hy013 | hy013
                · have hs0130 : InSquare (-3/40) (-11/40) (1/40) tau := by
                    convert childLL hs013 hx013 hy013 using 1 <;> norm_num
                  exact Coverage0130.cover htau hs0130
                · have hs0132 : InSquare (-3/40) (-9/40) (1/40) tau := by
                    convert childUL hs013 hx013 hy013 using 1 <;> norm_num
                  exact Coverage0132.cover htau hs0132
              · rcases le_total tau.im (-1/4 : ℝ) with hy013 | hy013
                · have hs0131 : InSquare (-1/40) (-11/40) (1/40) tau := by
                    convert childLR hs013 hx013 hy013 using 1 <;> norm_num
                  exact Coverage0131.cover htau hs0131
                · have hs0133 : InSquare (-1/40) (-9/40) (1/40) tau := by
                    convert childUR hs013 hx013 hy013 using 1 <;> norm_num
                  exact Coverage0133.cover htau hs0133
        · have hs03 : InSquare (-1/10) (-1/10) (1/10) tau := by
            convert childUR hs0 hx0 hy0 using 1 <;> norm_num
          rcases le_total tau.re (-1/10 : ℝ) with hx03 | hx03
          · rcases le_total tau.im (-1/10 : ℝ) with hy03 | hy03
            · have hs030 : InSquare (-3/20) (-3/20) (1/20) tau := by
                convert childLL hs03 hx03 hy03 using 1 <;> norm_num
              rcases le_total tau.re (-3/20 : ℝ) with hx030 | hx030
              · rcases le_total tau.im (-3/20 : ℝ) with hy030 | hy030
                · have hs0300 : InSquare (-7/40) (-7/40) (1/40) tau := by
                    convert childLL hs030 hx030 hy030 using 1 <;> norm_num
                  exact Coverage0300.cover htau hs0300
                · have hs0302 : InSquare (-7/40) (-1/8) (1/40) tau := by
                    convert childUL hs030 hx030 hy030 using 1 <;> norm_num
                  exact Coverage0302.cover htau hs0302
              · rcases le_total tau.im (-3/20 : ℝ) with hy030 | hy030
                · have hs0301 : InSquare (-1/8) (-7/40) (1/40) tau := by
                    convert childLR hs030 hx030 hy030 using 1 <;> norm_num
                  exact Coverage0301.cover htau hs0301
                · have hs0303 : InSquare (-1/8) (-1/8) (1/40) tau := by
                    convert childUR hs030 hx030 hy030 using 1 <;> norm_num
                  exact Batch0000.cell0001.sound htau (by
                    simp only [Batch0000.cell0001, Batch0000.tau0001, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs0303 (by positivity) using 1 <;> norm_num)
            · have hs032 : InSquare (-3/20) (-1/20) (1/20) tau := by
                convert childUL hs03 hx03 hy03 using 1 <;> norm_num
              rcases le_total tau.re (-3/20 : ℝ) with hx032 | hx032
              · rcases le_total tau.im (-1/20 : ℝ) with hy032 | hy032
                · have hs0320 : InSquare (-7/40) (-3/40) (1/40) tau := by
                    convert childLL hs032 hx032 hy032 using 1 <;> norm_num
                  exact Batch0000.cell0005.sound htau (by
                    simp only [Batch0000.cell0005, Batch0000.tau0005, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs0320 (by positivity) using 1 <;> norm_num)
                · have hs0322 : InSquare (-7/40) (-1/40) (1/40) tau := by
                    convert childUL hs032 hx032 hy032 using 1 <;> norm_num
                  exact Batch0000.cell0007.sound htau (by
                    simp only [Batch0000.cell0007, Batch0000.tau0007, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs0322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-1/20 : ℝ) with hy032 | hy032
                · have hs0321 : InSquare (-1/8) (-3/40) (1/40) tau := by
                    convert childLR hs032 hx032 hy032 using 1 <;> norm_num
                  exact Batch0000.cell0006.sound htau (by
                    simp only [Batch0000.cell0006, Batch0000.tau0006, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs0321 (by positivity) using 1 <;> norm_num)
                · have hs0323 : InSquare (-1/8) (-1/40) (1/40) tau := by
                    convert childUR hs032 hx032 hy032 using 1 <;> norm_num
                  exact Batch0001.cell0008.sound htau (by
                    simp only [Batch0001.cell0008, Batch0001.tau0008, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs0323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-1/10 : ℝ) with hy03 | hy03
            · have hs031 : InSquare (-1/20) (-3/20) (1/20) tau := by
                convert childLR hs03 hx03 hy03 using 1 <;> norm_num
              rcases le_total tau.re (-1/20 : ℝ) with hx031 | hx031
              · rcases le_total tau.im (-3/20 : ℝ) with hy031 | hy031
                · have hs0310 : InSquare (-3/40) (-7/40) (1/40) tau := by
                    convert childLL hs031 hx031 hy031 using 1 <;> norm_num
                  exact Coverage0310.cover htau hs0310
                · have hs0312 : InSquare (-3/40) (-1/8) (1/40) tau := by
                    convert childUL hs031 hx031 hy031 using 1 <;> norm_num
                  exact Batch0000.cell0003.sound htau (by
                    simp only [Batch0000.cell0003, Batch0000.tau0003, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs0312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-3/20 : ℝ) with hy031 | hy031
                · have hs0311 : InSquare (-1/40) (-7/40) (1/40) tau := by
                    convert childLR hs031 hx031 hy031 using 1 <;> norm_num
                  exact Batch0000.cell0002.sound htau (by
                    simp only [Batch0000.cell0002, Batch0000.tau0002, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs0311 (by positivity) using 1 <;> norm_num)
                · have hs0313 : InSquare (-1/40) (-1/8) (1/40) tau := by
                    convert childUR hs031 hx031 hy031 using 1 <;> norm_num
                  exact Batch0000.cell0004.sound htau (by
                    simp only [Batch0000.cell0004, Batch0000.tau0004, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs0313 (by positivity) using 1 <;> norm_num)
            · have hs033 : InSquare (-1/20) (-1/20) (1/20) tau := by
                convert childUR hs03 hx03 hy03 using 1 <;> norm_num
              rcases le_total tau.re (-1/20 : ℝ) with hx033 | hx033
              · rcases le_total tau.im (-1/20 : ℝ) with hy033 | hy033
                · have hs0330 : InSquare (-3/40) (-3/40) (1/40) tau := by
                    convert childLL hs033 hx033 hy033 using 1 <;> norm_num
                  exact Batch0001.cell0009.sound htau (by
                    simp only [Batch0001.cell0009, Batch0001.tau0009, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs0330 (by positivity) using 1 <;> norm_num)
                · have hs0332 : InSquare (-3/40) (-1/40) (1/40) tau := by
                    convert childUL hs033 hx033 hy033 using 1 <;> norm_num
                  exact Batch0001.cell0011.sound htau (by
                    simp only [Batch0001.cell0011, Batch0001.tau0011, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs0332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-1/20 : ℝ) with hy033 | hy033
                · have hs0331 : InSquare (-1/40) (-3/40) (1/40) tau := by
                    convert childLR hs033 hx033 hy033 using 1 <;> norm_num
                  exact Batch0001.cell0010.sound htau (by
                    simp only [Batch0001.cell0010, Batch0001.tau0010, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs0331 (by positivity) using 1 <;> norm_num)
                · have hs0333 : InSquare (-1/40) (-1/40) (1/40) tau := by
                    convert childUR hs033 hx033 hy033 using 1 <;> norm_num
                  exact Batch0001.cell0012.sound htau (by
                    simp only [Batch0001.cell0012, Batch0001.tau0012, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs0333 (by positivity) using 1 <;> norm_num)
    · have hs2 : InSquare (-1/5) (1/5) (1/5) tau := by
        convert childUL (disc_in_root htau) hxroot hyroot using 1 <;> norm_num
      rcases le_total tau.re (-1/5 : ℝ) with hx2 | hx2
      · rcases le_total tau.im (1/5 : ℝ) with hy2 | hy2
        · have hs20 : InSquare (-3/10) (1/10) (1/10) tau := by
            convert childLL hs2 hx2 hy2 using 1 <;> norm_num
          rcases le_total tau.re (-3/10 : ℝ) with hx20 | hx20
          · rcases le_total tau.im (1/10 : ℝ) with hy20 | hy20
            · have hs200 : InSquare (-7/20) (1/20) (1/20) tau := by
                convert childLL hs20 hx20 hy20 using 1 <;> norm_num
              rcases le_total tau.re (-7/20 : ℝ) with hx200 | hx200
              · rcases le_total tau.im (1/20 : ℝ) with hy200 | hy200
                · have hs2000 : InSquare (-3/8) (1/40) (1/40) tau := by
                    convert childLL hs200 hx200 hy200 using 1 <;> norm_num
                  exact Coverage2000.cover htau hs2000
                · have hs2002 : InSquare (-3/8) (3/40) (1/40) tau := by
                    convert childUL hs200 hx200 hy200 using 1 <;> norm_num
                  exact Coverage2002.cover htau hs2002
              · rcases le_total tau.im (1/20 : ℝ) with hy200 | hy200
                · have hs2001 : InSquare (-13/40) (1/40) (1/40) tau := by
                    convert childLR hs200 hx200 hy200 using 1 <;> norm_num
                  exact Coverage2001.cover htau hs2001
                · have hs2003 : InSquare (-13/40) (3/40) (1/40) tau := by
                    convert childUR hs200 hx200 hy200 using 1 <;> norm_num
                  exact Coverage2003.cover htau hs2003
            · have hs202 : InSquare (-7/20) (3/20) (1/20) tau := by
                convert childUL hs20 hx20 hy20 using 1 <;> norm_num
              rcases le_total tau.re (-7/20 : ℝ) with hx202 | hx202
              · rcases le_total tau.im (3/20 : ℝ) with hy202 | hy202
                · have hs2020 : InSquare (-3/8) (1/8) (1/40) tau := by
                    convert childLL hs202 hx202 hy202 using 1 <;> norm_num
                  exact Coverage2020.cover htau hs2020
                · have hs2022 : InSquare (-3/8) (7/40) (1/40) tau := by
                    convert childUL hs202 hx202 hy202 using 1 <;> norm_num
                  exact Coverage2022.cover htau hs2022
              · rcases le_total tau.im (3/20 : ℝ) with hy202 | hy202
                · have hs2021 : InSquare (-13/40) (1/8) (1/40) tau := by
                    convert childLR hs202 hx202 hy202 using 1 <;> norm_num
                  exact Coverage2021.cover htau hs2021
                · have hs2023 : InSquare (-13/40) (7/40) (1/40) tau := by
                    convert childUR hs202 hx202 hy202 using 1 <;> norm_num
                  exact Coverage2023.cover htau hs2023
          · rcases le_total tau.im (1/10 : ℝ) with hy20 | hy20
            · have hs201 : InSquare (-1/4) (1/20) (1/20) tau := by
                convert childLR hs20 hx20 hy20 using 1 <;> norm_num
              rcases le_total tau.re (-1/4 : ℝ) with hx201 | hx201
              · rcases le_total tau.im (1/20 : ℝ) with hy201 | hy201
                · have hs2010 : InSquare (-11/40) (1/40) (1/40) tau := by
                    convert childLL hs201 hx201 hy201 using 1 <;> norm_num
                  exact Coverage2010.cover htau hs2010
                · have hs2012 : InSquare (-11/40) (3/40) (1/40) tau := by
                    convert childUL hs201 hx201 hy201 using 1 <;> norm_num
                  exact Coverage2012.cover htau hs2012
              · rcases le_total tau.im (1/20 : ℝ) with hy201 | hy201
                · have hs2011 : InSquare (-9/40) (1/40) (1/40) tau := by
                    convert childLR hs201 hx201 hy201 using 1 <;> norm_num
                  exact Batch0003.cell0026.sound htau (by
                    simp only [Batch0003.cell0026, Batch0003.tau0026, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs2011 (by positivity) using 1 <;> norm_num)
                · have hs2013 : InSquare (-9/40) (3/40) (1/40) tau := by
                    convert childUR hs201 hx201 hy201 using 1 <;> norm_num
                  exact Coverage2013.cover htau hs2013
            · have hs203 : InSquare (-1/4) (3/20) (1/20) tau := by
                convert childUR hs20 hx20 hy20 using 1 <;> norm_num
              rcases le_total tau.re (-1/4 : ℝ) with hx203 | hx203
              · rcases le_total tau.im (3/20 : ℝ) with hy203 | hy203
                · have hs2030 : InSquare (-11/40) (1/8) (1/40) tau := by
                    convert childLL hs203 hx203 hy203 using 1 <;> norm_num
                  exact Coverage2030.cover htau hs2030
                · have hs2032 : InSquare (-11/40) (7/40) (1/40) tau := by
                    convert childUL hs203 hx203 hy203 using 1 <;> norm_num
                  exact Coverage2032.cover htau hs2032
              · rcases le_total tau.im (3/20 : ℝ) with hy203 | hy203
                · have hs2031 : InSquare (-9/40) (1/8) (1/40) tau := by
                    convert childLR hs203 hx203 hy203 using 1 <;> norm_num
                  exact Coverage2031.cover htau hs2031
                · have hs2033 : InSquare (-9/40) (7/40) (1/40) tau := by
                    convert childUR hs203 hx203 hy203 using 1 <;> norm_num
                  exact Coverage2033.cover htau hs2033
        · have hs22 : InSquare (-3/10) (3/10) (1/10) tau := by
            convert childUL hs2 hx2 hy2 using 1 <;> norm_num
          rcases le_total tau.re (-3/10 : ℝ) with hx22 | hx22
          · rcases le_total tau.im (3/10 : ℝ) with hy22 | hy22
            · have hs220 : InSquare (-7/20) (1/4) (1/20) tau := by
                convert childLL hs22 hx22 hy22 using 1 <;> norm_num
              rcases le_total tau.re (-7/20 : ℝ) with hx220 | hx220
              · rcases le_total tau.im (1/4 : ℝ) with hy220 | hy220
                · have hs2200 : InSquare (-3/8) (9/40) (1/40) tau := by
                    convert childLL hs220 hx220 hy220 using 1 <;> norm_num
                  exact (outside_2200_priv htau hs2200).elim
                · have hs2202 : InSquare (-3/8) (11/40) (1/40) tau := by
                    convert childUL hs220 hx220 hy220 using 1 <;> norm_num
                  exact (outside_2202_priv htau hs2202).elim
              · rcases le_total tau.im (1/4 : ℝ) with hy220 | hy220
                · have hs2201 : InSquare (-13/40) (9/40) (1/40) tau := by
                    convert childLR hs220 hx220 hy220 using 1 <;> norm_num
                  exact Coverage2201.cover htau hs2201
                · have hs2203 : InSquare (-13/40) (11/40) (1/40) tau := by
                    convert childUR hs220 hx220 hy220 using 1 <;> norm_num
                  exact Coverage2203.cover htau hs2203
            · have hs222 : InSquare (-7/20) (7/20) (1/20) tau := by
                convert childUL hs22 hx22 hy22 using 1 <;> norm_num
              exact (outside_222_priv htau hs222).elim
          · rcases le_total tau.im (3/10 : ℝ) with hy22 | hy22
            · have hs221 : InSquare (-1/4) (1/4) (1/20) tau := by
                convert childLR hs22 hx22 hy22 using 1 <;> norm_num
              rcases le_total tau.re (-1/4 : ℝ) with hx221 | hx221
              · rcases le_total tau.im (1/4 : ℝ) with hy221 | hy221
                · have hs2210 : InSquare (-11/40) (9/40) (1/40) tau := by
                    convert childLL hs221 hx221 hy221 using 1 <;> norm_num
                  exact Coverage2210.cover htau hs2210
                · have hs2212 : InSquare (-11/40) (11/40) (1/40) tau := by
                    convert childUL hs221 hx221 hy221 using 1 <;> norm_num
                  exact Coverage2212.cover htau hs2212
              · rcases le_total tau.im (1/4 : ℝ) with hy221 | hy221
                · have hs2211 : InSquare (-9/40) (9/40) (1/40) tau := by
                    convert childLR hs221 hx221 hy221 using 1 <;> norm_num
                  exact Coverage2211.cover htau hs2211
                · have hs2213 : InSquare (-9/40) (11/40) (1/40) tau := by
                    convert childUR hs221 hx221 hy221 using 1 <;> norm_num
                  exact Coverage2213.cover htau hs2213
            · have hs223 : InSquare (-1/4) (7/20) (1/20) tau := by
                convert childUR hs22 hx22 hy22 using 1 <;> norm_num
              rcases le_total tau.re (-1/4 : ℝ) with hx223 | hx223
              · rcases le_total tau.im (7/20 : ℝ) with hy223 | hy223
                · have hs2230 : InSquare (-11/40) (13/40) (1/40) tau := by
                    convert childLL hs223 hx223 hy223 using 1 <;> norm_num
                  exact Coverage2230.cover htau hs2230
                · have hs2232 : InSquare (-11/40) (3/8) (1/40) tau := by
                    convert childUL hs223 hx223 hy223 using 1 <;> norm_num
                  exact (outside_2232_priv htau hs2232).elim
              · rcases le_total tau.im (7/20 : ℝ) with hy223 | hy223
                · have hs2231 : InSquare (-9/40) (13/40) (1/40) tau := by
                    convert childLR hs223 hx223 hy223 using 1 <;> norm_num
                  exact Coverage2231.cover htau hs2231
                · have hs2233 : InSquare (-9/40) (3/8) (1/40) tau := by
                    convert childUR hs223 hx223 hy223 using 1 <;> norm_num
                  exact (outside_2233_priv htau hs2233).elim
      · rcases le_total tau.im (1/5 : ℝ) with hy2 | hy2
        · have hs21 : InSquare (-1/10) (1/10) (1/10) tau := by
            convert childLR hs2 hx2 hy2 using 1 <;> norm_num
          rcases le_total tau.re (-1/10 : ℝ) with hx21 | hx21
          · rcases le_total tau.im (1/10 : ℝ) with hy21 | hy21
            · have hs210 : InSquare (-3/20) (1/20) (1/20) tau := by
                convert childLL hs21 hx21 hy21 using 1 <;> norm_num
              rcases le_total tau.re (-3/20 : ℝ) with hx210 | hx210
              · rcases le_total tau.im (1/20 : ℝ) with hy210 | hy210
                · have hs2100 : InSquare (-7/40) (1/40) (1/40) tau := by
                    convert childLL hs210 hx210 hy210 using 1 <;> norm_num
                  exact Batch0003.cell0027.sound htau (by
                    simp only [Batch0003.cell0027, Batch0003.tau0027, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs2100 (by positivity) using 1 <;> norm_num)
                · have hs2102 : InSquare (-7/40) (3/40) (1/40) tau := by
                    convert childUL hs210 hx210 hy210 using 1 <;> norm_num
                  exact Batch0003.cell0029.sound htau (by
                    simp only [Batch0003.cell0029, Batch0003.tau0029, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs2102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (1/20 : ℝ) with hy210 | hy210
                · have hs2101 : InSquare (-1/8) (1/40) (1/40) tau := by
                    convert childLR hs210 hx210 hy210 using 1 <;> norm_num
                  exact Batch0003.cell0028.sound htau (by
                    simp only [Batch0003.cell0028, Batch0003.tau0028, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs2101 (by positivity) using 1 <;> norm_num)
                · have hs2103 : InSquare (-1/8) (3/40) (1/40) tau := by
                    convert childUR hs210 hx210 hy210 using 1 <;> norm_num
                  exact Batch0003.cell0030.sound htau (by
                    simp only [Batch0003.cell0030, Batch0003.tau0030, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs2103 (by positivity) using 1 <;> norm_num)
            · have hs212 : InSquare (-3/20) (3/20) (1/20) tau := by
                convert childUL hs21 hx21 hy21 using 1 <;> norm_num
              rcases le_total tau.re (-3/20 : ℝ) with hx212 | hx212
              · rcases le_total tau.im (3/20 : ℝ) with hy212 | hy212
                · have hs2120 : InSquare (-7/40) (1/8) (1/40) tau := by
                    convert childLL hs212 hx212 hy212 using 1 <;> norm_num
                  exact Coverage2120.cover htau hs2120
                · have hs2122 : InSquare (-7/40) (7/40) (1/40) tau := by
                    convert childUL hs212 hx212 hy212 using 1 <;> norm_num
                  exact Coverage2122.cover htau hs2122
              · rcases le_total tau.im (3/20 : ℝ) with hy212 | hy212
                · have hs2121 : InSquare (-1/8) (1/8) (1/40) tau := by
                    convert childLR hs212 hx212 hy212 using 1 <;> norm_num
                  exact Batch0004.cell0035.sound htau (by
                    simp only [Batch0004.cell0035, Batch0004.tau0035, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs2121 (by positivity) using 1 <;> norm_num)
                · have hs2123 : InSquare (-1/8) (7/40) (1/40) tau := by
                    convert childUR hs212 hx212 hy212 using 1 <;> norm_num
                  exact Coverage2123.cover htau hs2123
          · rcases le_total tau.im (1/10 : ℝ) with hy21 | hy21
            · have hs211 : InSquare (-1/20) (1/20) (1/20) tau := by
                convert childLR hs21 hx21 hy21 using 1 <;> norm_num
              rcases le_total tau.re (-1/20 : ℝ) with hx211 | hx211
              · rcases le_total tau.im (1/20 : ℝ) with hy211 | hy211
                · have hs2110 : InSquare (-3/40) (1/40) (1/40) tau := by
                    convert childLL hs211 hx211 hy211 using 1 <;> norm_num
                  exact Batch0003.cell0031.sound htau (by
                    simp only [Batch0003.cell0031, Batch0003.tau0031, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs2110 (by positivity) using 1 <;> norm_num)
                · have hs2112 : InSquare (-3/40) (3/40) (1/40) tau := by
                    convert childUL hs211 hx211 hy211 using 1 <;> norm_num
                  exact Batch0004.cell0033.sound htau (by
                    simp only [Batch0004.cell0033, Batch0004.tau0033, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs2112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (1/20 : ℝ) with hy211 | hy211
                · have hs2111 : InSquare (-1/40) (1/40) (1/40) tau := by
                    convert childLR hs211 hx211 hy211 using 1 <;> norm_num
                  exact Batch0004.cell0032.sound htau (by
                    simp only [Batch0004.cell0032, Batch0004.tau0032, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs2111 (by positivity) using 1 <;> norm_num)
                · have hs2113 : InSquare (-1/40) (3/40) (1/40) tau := by
                    convert childUR hs211 hx211 hy211 using 1 <;> norm_num
                  exact Batch0004.cell0034.sound htau (by
                    simp only [Batch0004.cell0034, Batch0004.tau0034, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs2113 (by positivity) using 1 <;> norm_num)
            · have hs213 : InSquare (-1/20) (3/20) (1/20) tau := by
                convert childUR hs21 hx21 hy21 using 1 <;> norm_num
              rcases le_total tau.re (-1/20 : ℝ) with hx213 | hx213
              · rcases le_total tau.im (3/20 : ℝ) with hy213 | hy213
                · have hs2130 : InSquare (-3/40) (1/8) (1/40) tau := by
                    convert childLL hs213 hx213 hy213 using 1 <;> norm_num
                  exact Batch0004.cell0036.sound htau (by
                    simp only [Batch0004.cell0036, Batch0004.tau0036, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs2130 (by positivity) using 1 <;> norm_num)
                · have hs2132 : InSquare (-3/40) (7/40) (1/40) tau := by
                    convert childUL hs213 hx213 hy213 using 1 <;> norm_num
                  exact Coverage2132.cover htau hs2132
              · rcases le_total tau.im (3/20 : ℝ) with hy213 | hy213
                · have hs2131 : InSquare (-1/40) (1/8) (1/40) tau := by
                    convert childLR hs213 hx213 hy213 using 1 <;> norm_num
                  exact Batch0004.cell0037.sound htau (by
                    simp only [Batch0004.cell0037, Batch0004.tau0037, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs2131 (by positivity) using 1 <;> norm_num)
                · have hs2133 : InSquare (-1/40) (7/40) (1/40) tau := by
                    convert childUR hs213 hx213 hy213 using 1 <;> norm_num
                  exact Batch0004.cell0038.sound htau (by
                    simp only [Batch0004.cell0038, Batch0004.tau0038, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs2133 (by positivity) using 1 <;> norm_num)
        · have hs23 : InSquare (-1/10) (3/10) (1/10) tau := by
            convert childUR hs2 hx2 hy2 using 1 <;> norm_num
          rcases le_total tau.re (-1/10 : ℝ) with hx23 | hx23
          · rcases le_total tau.im (3/10 : ℝ) with hy23 | hy23
            · have hs230 : InSquare (-3/20) (1/4) (1/20) tau := by
                convert childLL hs23 hx23 hy23 using 1 <;> norm_num
              rcases le_total tau.re (-3/20 : ℝ) with hx230 | hx230
              · rcases le_total tau.im (1/4 : ℝ) with hy230 | hy230
                · have hs2300 : InSquare (-7/40) (9/40) (1/40) tau := by
                    convert childLL hs230 hx230 hy230 using 1 <;> norm_num
                  exact Coverage2300.cover htau hs2300
                · have hs2302 : InSquare (-7/40) (11/40) (1/40) tau := by
                    convert childUL hs230 hx230 hy230 using 1 <;> norm_num
                  exact Coverage2302.cover htau hs2302
              · rcases le_total tau.im (1/4 : ℝ) with hy230 | hy230
                · have hs2301 : InSquare (-1/8) (9/40) (1/40) tau := by
                    convert childLR hs230 hx230 hy230 using 1 <;> norm_num
                  exact Coverage2301.cover htau hs2301
                · have hs2303 : InSquare (-1/8) (11/40) (1/40) tau := by
                    convert childUR hs230 hx230 hy230 using 1 <;> norm_num
                  exact Coverage2303.cover htau hs2303
            · have hs232 : InSquare (-3/20) (7/20) (1/20) tau := by
                convert childUL hs23 hx23 hy23 using 1 <;> norm_num
              rcases le_total tau.re (-3/20 : ℝ) with hx232 | hx232
              · rcases le_total tau.im (7/20 : ℝ) with hy232 | hy232
                · have hs2320 : InSquare (-7/40) (13/40) (1/40) tau := by
                    convert childLL hs232 hx232 hy232 using 1 <;> norm_num
                  exact Coverage2320.cover htau hs2320
                · have hs2322 : InSquare (-7/40) (3/8) (1/40) tau := by
                    convert childUL hs232 hx232 hy232 using 1 <;> norm_num
                  exact Coverage2322.cover htau hs2322
              · rcases le_total tau.im (7/20 : ℝ) with hy232 | hy232
                · have hs2321 : InSquare (-1/8) (13/40) (1/40) tau := by
                    convert childLR hs232 hx232 hy232 using 1 <;> norm_num
                  exact Coverage2321.cover htau hs2321
                · have hs2323 : InSquare (-1/8) (3/8) (1/40) tau := by
                    convert childUR hs232 hx232 hy232 using 1 <;> norm_num
                  exact Coverage2323.cover htau hs2323
          · rcases le_total tau.im (3/10 : ℝ) with hy23 | hy23
            · have hs231 : InSquare (-1/20) (1/4) (1/20) tau := by
                convert childLR hs23 hx23 hy23 using 1 <;> norm_num
              rcases le_total tau.re (-1/20 : ℝ) with hx231 | hx231
              · rcases le_total tau.im (1/4 : ℝ) with hy231 | hy231
                · have hs2310 : InSquare (-3/40) (9/40) (1/40) tau := by
                    convert childLL hs231 hx231 hy231 using 1 <;> norm_num
                  exact Coverage2310.cover htau hs2310
                · have hs2312 : InSquare (-3/40) (11/40) (1/40) tau := by
                    convert childUL hs231 hx231 hy231 using 1 <;> norm_num
                  exact Coverage2312.cover htau hs2312
              · rcases le_total tau.im (1/4 : ℝ) with hy231 | hy231
                · have hs2311 : InSquare (-1/40) (9/40) (1/40) tau := by
                    convert childLR hs231 hx231 hy231 using 1 <;> norm_num
                  exact Coverage2311.cover htau hs2311
                · have hs2313 : InSquare (-1/40) (11/40) (1/40) tau := by
                    convert childUR hs231 hx231 hy231 using 1 <;> norm_num
                  exact Coverage2313.cover htau hs2313
            · have hs233 : InSquare (-1/20) (7/20) (1/20) tau := by
                convert childUR hs23 hx23 hy23 using 1 <;> norm_num
              rcases le_total tau.re (-1/20 : ℝ) with hx233 | hx233
              · rcases le_total tau.im (7/20 : ℝ) with hy233 | hy233
                · have hs2330 : InSquare (-3/40) (13/40) (1/40) tau := by
                    convert childLL hs233 hx233 hy233 using 1 <;> norm_num
                  exact Coverage2330.cover htau hs2330
                · have hs2332 : InSquare (-3/40) (3/8) (1/40) tau := by
                    convert childUL hs233 hx233 hy233 using 1 <;> norm_num
                  exact Coverage2332.cover htau hs2332
              · rcases le_total tau.im (7/20 : ℝ) with hy233 | hy233
                · have hs2331 : InSquare (-1/40) (13/40) (1/40) tau := by
                    convert childLR hs233 hx233 hy233 using 1 <;> norm_num
                  exact Coverage2331.cover htau hs2331
                · have hs2333 : InSquare (-1/40) (3/8) (1/40) tau := by
                    convert childUR hs233 hx233 hy233 using 1 <;> norm_num
                  exact Coverage2333.cover htau hs2333
  · rcases le_total tau.im (0 : ℝ) with hyroot | hyroot
    · have hs1 : InSquare (1/5) (-1/5) (1/5) tau := by
        convert childLR (disc_in_root htau) hxroot hyroot using 1 <;> norm_num
      rcases le_total tau.re (1/5 : ℝ) with hx1 | hx1
      · rcases le_total tau.im (-1/5 : ℝ) with hy1 | hy1
        · have hs10 : InSquare (1/10) (-3/10) (1/10) tau := by
            convert childLL hs1 hx1 hy1 using 1 <;> norm_num
          rcases le_total tau.re (1/10 : ℝ) with hx10 | hx10
          · rcases le_total tau.im (-3/10 : ℝ) with hy10 | hy10
            · have hs100 : InSquare (1/20) (-7/20) (1/20) tau := by
                convert childLL hs10 hx10 hy10 using 1 <;> norm_num
              rcases le_total tau.re (1/20 : ℝ) with hx100 | hx100
              · rcases le_total tau.im (-7/20 : ℝ) with hy100 | hy100
                · have hs1000 : InSquare (1/40) (-3/8) (1/40) tau := by
                    convert childLL hs100 hx100 hy100 using 1 <;> norm_num
                  exact Coverage1000.cover htau hs1000
                · have hs1002 : InSquare (1/40) (-13/40) (1/40) tau := by
                    convert childUL hs100 hx100 hy100 using 1 <;> norm_num
                  exact Coverage1002.cover htau hs1002
              · rcases le_total tau.im (-7/20 : ℝ) with hy100 | hy100
                · have hs1001 : InSquare (3/40) (-3/8) (1/40) tau := by
                    convert childLR hs100 hx100 hy100 using 1 <;> norm_num
                  exact Coverage1001.cover htau hs1001
                · have hs1003 : InSquare (3/40) (-13/40) (1/40) tau := by
                    convert childUR hs100 hx100 hy100 using 1 <;> norm_num
                  exact Coverage1003.cover htau hs1003
            · have hs102 : InSquare (1/20) (-1/4) (1/20) tau := by
                convert childUL hs10 hx10 hy10 using 1 <;> norm_num
              rcases le_total tau.re (1/20 : ℝ) with hx102 | hx102
              · rcases le_total tau.im (-1/4 : ℝ) with hy102 | hy102
                · have hs1020 : InSquare (1/40) (-11/40) (1/40) tau := by
                    convert childLL hs102 hx102 hy102 using 1 <;> norm_num
                  exact Coverage1020.cover htau hs1020
                · have hs1022 : InSquare (1/40) (-9/40) (1/40) tau := by
                    convert childUL hs102 hx102 hy102 using 1 <;> norm_num
                  exact Coverage1022.cover htau hs1022
              · rcases le_total tau.im (-1/4 : ℝ) with hy102 | hy102
                · have hs1021 : InSquare (3/40) (-11/40) (1/40) tau := by
                    convert childLR hs102 hx102 hy102 using 1 <;> norm_num
                  exact Coverage1021.cover htau hs1021
                · have hs1023 : InSquare (3/40) (-9/40) (1/40) tau := by
                    convert childUR hs102 hx102 hy102 using 1 <;> norm_num
                  exact Coverage1023.cover htau hs1023
          · rcases le_total tau.im (-3/10 : ℝ) with hy10 | hy10
            · have hs101 : InSquare (3/20) (-7/20) (1/20) tau := by
                convert childLR hs10 hx10 hy10 using 1 <;> norm_num
              rcases le_total tau.re (3/20 : ℝ) with hx101 | hx101
              · rcases le_total tau.im (-7/20 : ℝ) with hy101 | hy101
                · have hs1010 : InSquare (1/8) (-3/8) (1/40) tau := by
                    convert childLL hs101 hx101 hy101 using 1 <;> norm_num
                  exact Coverage1010.cover htau hs1010
                · have hs1012 : InSquare (1/8) (-13/40) (1/40) tau := by
                    convert childUL hs101 hx101 hy101 using 1 <;> norm_num
                  exact Coverage1012.cover htau hs1012
              · rcases le_total tau.im (-7/20 : ℝ) with hy101 | hy101
                · have hs1011 : InSquare (7/40) (-3/8) (1/40) tau := by
                    convert childLR hs101 hx101 hy101 using 1 <;> norm_num
                  exact Coverage1011.cover htau hs1011
                · have hs1013 : InSquare (7/40) (-13/40) (1/40) tau := by
                    convert childUR hs101 hx101 hy101 using 1 <;> norm_num
                  exact Coverage1013.cover htau hs1013
            · have hs103 : InSquare (3/20) (-1/4) (1/20) tau := by
                convert childUR hs10 hx10 hy10 using 1 <;> norm_num
              rcases le_total tau.re (3/20 : ℝ) with hx103 | hx103
              · rcases le_total tau.im (-1/4 : ℝ) with hy103 | hy103
                · have hs1030 : InSquare (1/8) (-11/40) (1/40) tau := by
                    convert childLL hs103 hx103 hy103 using 1 <;> norm_num
                  exact Coverage1030.cover htau hs1030
                · have hs1032 : InSquare (1/8) (-9/40) (1/40) tau := by
                    convert childUL hs103 hx103 hy103 using 1 <;> norm_num
                  exact Coverage1032.cover htau hs1032
              · rcases le_total tau.im (-1/4 : ℝ) with hy103 | hy103
                · have hs1031 : InSquare (7/40) (-11/40) (1/40) tau := by
                    convert childLR hs103 hx103 hy103 using 1 <;> norm_num
                  exact Coverage1031.cover htau hs1031
                · have hs1033 : InSquare (7/40) (-9/40) (1/40) tau := by
                    convert childUR hs103 hx103 hy103 using 1 <;> norm_num
                  exact Coverage1033.cover htau hs1033
        · have hs12 : InSquare (1/10) (-1/10) (1/10) tau := by
            convert childUL hs1 hx1 hy1 using 1 <;> norm_num
          rcases le_total tau.re (1/10 : ℝ) with hx12 | hx12
          · rcases le_total tau.im (-1/10 : ℝ) with hy12 | hy12
            · have hs120 : InSquare (1/20) (-3/20) (1/20) tau := by
                convert childLL hs12 hx12 hy12 using 1 <;> norm_num
              rcases le_total tau.re (1/20 : ℝ) with hx120 | hx120
              · rcases le_total tau.im (-3/20 : ℝ) with hy120 | hy120
                · have hs1200 : InSquare (1/40) (-7/40) (1/40) tau := by
                    convert childLL hs120 hx120 hy120 using 1 <;> norm_num
                  exact Batch0001.cell0013.sound htau (by
                    simp only [Batch0001.cell0013, Batch0001.tau0013, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs1200 (by positivity) using 1 <;> norm_num)
                · have hs1202 : InSquare (1/40) (-1/8) (1/40) tau := by
                    convert childUL hs120 hx120 hy120 using 1 <;> norm_num
                  exact Batch0001.cell0014.sound htau (by
                    simp only [Batch0001.cell0014, Batch0001.tau0014, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs1202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-3/20 : ℝ) with hy120 | hy120
                · have hs1201 : InSquare (3/40) (-7/40) (1/40) tau := by
                    convert childLR hs120 hx120 hy120 using 1 <;> norm_num
                  exact Coverage1201.cover htau hs1201
                · have hs1203 : InSquare (3/40) (-1/8) (1/40) tau := by
                    convert childUR hs120 hx120 hy120 using 1 <;> norm_num
                  exact Batch0001.cell0015.sound htau (by
                    simp only [Batch0001.cell0015, Batch0001.tau0015, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs1203 (by positivity) using 1 <;> norm_num)
            · have hs122 : InSquare (1/20) (-1/20) (1/20) tau := by
                convert childUL hs12 hx12 hy12 using 1 <;> norm_num
              rcases le_total tau.re (1/20 : ℝ) with hx122 | hx122
              · rcases le_total tau.im (-1/20 : ℝ) with hy122 | hy122
                · have hs1220 : InSquare (1/40) (-3/40) (1/40) tau := by
                    convert childLL hs122 hx122 hy122 using 1 <;> norm_num
                  exact Batch0002.cell0017.sound htau (by
                    simp only [Batch0002.cell0017, Batch0002.tau0017, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs1220 (by positivity) using 1 <;> norm_num)
                · have hs1222 : InSquare (1/40) (-1/40) (1/40) tau := by
                    convert childUL hs122 hx122 hy122 using 1 <;> norm_num
                  exact Batch0002.cell0019.sound htau (by
                    simp only [Batch0002.cell0019, Batch0002.tau0019, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs1222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-1/20 : ℝ) with hy122 | hy122
                · have hs1221 : InSquare (3/40) (-3/40) (1/40) tau := by
                    convert childLR hs122 hx122 hy122 using 1 <;> norm_num
                  exact Batch0002.cell0018.sound htau (by
                    simp only [Batch0002.cell0018, Batch0002.tau0018, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs1221 (by positivity) using 1 <;> norm_num)
                · have hs1223 : InSquare (3/40) (-1/40) (1/40) tau := by
                    convert childUR hs122 hx122 hy122 using 1 <;> norm_num
                  exact Batch0002.cell0020.sound htau (by
                    simp only [Batch0002.cell0020, Batch0002.tau0020, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs1223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-1/10 : ℝ) with hy12 | hy12
            · have hs121 : InSquare (3/20) (-3/20) (1/20) tau := by
                convert childLR hs12 hx12 hy12 using 1 <;> norm_num
              rcases le_total tau.re (3/20 : ℝ) with hx121 | hx121
              · rcases le_total tau.im (-3/20 : ℝ) with hy121 | hy121
                · have hs1210 : InSquare (1/8) (-7/40) (1/40) tau := by
                    convert childLL hs121 hx121 hy121 using 1 <;> norm_num
                  exact Coverage1210.cover htau hs1210
                · have hs1212 : InSquare (1/8) (-1/8) (1/40) tau := by
                    convert childUL hs121 hx121 hy121 using 1 <;> norm_num
                  exact Batch0002.cell0016.sound htau (by
                    simp only [Batch0002.cell0016, Batch0002.tau0016, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs1212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-3/20 : ℝ) with hy121 | hy121
                · have hs1211 : InSquare (7/40) (-7/40) (1/40) tau := by
                    convert childLR hs121 hx121 hy121 using 1 <;> norm_num
                  exact Coverage1211.cover htau hs1211
                · have hs1213 : InSquare (7/40) (-1/8) (1/40) tau := by
                    convert childUR hs121 hx121 hy121 using 1 <;> norm_num
                  exact Coverage1213.cover htau hs1213
            · have hs123 : InSquare (3/20) (-1/20) (1/20) tau := by
                convert childUR hs12 hx12 hy12 using 1 <;> norm_num
              rcases le_total tau.re (3/20 : ℝ) with hx123 | hx123
              · rcases le_total tau.im (-1/20 : ℝ) with hy123 | hy123
                · have hs1230 : InSquare (1/8) (-3/40) (1/40) tau := by
                    convert childLL hs123 hx123 hy123 using 1 <;> norm_num
                  exact Batch0002.cell0021.sound htau (by
                    simp only [Batch0002.cell0021, Batch0002.tau0021, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs1230 (by positivity) using 1 <;> norm_num)
                · have hs1232 : InSquare (1/8) (-1/40) (1/40) tau := by
                    convert childUL hs123 hx123 hy123 using 1 <;> norm_num
                  exact Batch0002.cell0023.sound htau (by
                    simp only [Batch0002.cell0023, Batch0002.tau0023, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs1232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-1/20 : ℝ) with hy123 | hy123
                · have hs1231 : InSquare (7/40) (-3/40) (1/40) tau := by
                    convert childLR hs123 hx123 hy123 using 1 <;> norm_num
                  exact Batch0002.cell0022.sound htau (by
                    simp only [Batch0002.cell0022, Batch0002.tau0022, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs1231 (by positivity) using 1 <;> norm_num)
                · have hs1233 : InSquare (7/40) (-1/40) (1/40) tau := by
                    convert childUR hs123 hx123 hy123 using 1 <;> norm_num
                  exact Batch0003.cell0024.sound htau (by
                    simp only [Batch0003.cell0024, Batch0003.tau0024, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs1233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-1/5 : ℝ) with hy1 | hy1
        · have hs11 : InSquare (3/10) (-3/10) (1/10) tau := by
            convert childLR hs1 hx1 hy1 using 1 <;> norm_num
          rcases le_total tau.re (3/10 : ℝ) with hx11 | hx11
          · rcases le_total tau.im (-3/10 : ℝ) with hy11 | hy11
            · have hs110 : InSquare (1/4) (-7/20) (1/20) tau := by
                convert childLL hs11 hx11 hy11 using 1 <;> norm_num
              rcases le_total tau.re (1/4 : ℝ) with hx110 | hx110
              · rcases le_total tau.im (-7/20 : ℝ) with hy110 | hy110
                · have hs1100 : InSquare (9/40) (-3/8) (1/40) tau := by
                    convert childLL hs110 hx110 hy110 using 1 <;> norm_num
                  exact (outside_1100_priv htau hs1100).elim
                · have hs1102 : InSquare (9/40) (-13/40) (1/40) tau := by
                    convert childUL hs110 hx110 hy110 using 1 <;> norm_num
                  exact Coverage1102.cover htau hs1102
              · rcases le_total tau.im (-7/20 : ℝ) with hy110 | hy110
                · have hs1101 : InSquare (11/40) (-3/8) (1/40) tau := by
                    convert childLR hs110 hx110 hy110 using 1 <;> norm_num
                  exact (outside_1101_priv htau hs1101).elim
                · have hs1103 : InSquare (11/40) (-13/40) (1/40) tau := by
                    convert childUR hs110 hx110 hy110 using 1 <;> norm_num
                  exact Coverage1103.cover htau hs1103
            · have hs112 : InSquare (1/4) (-1/4) (1/20) tau := by
                convert childUL hs11 hx11 hy11 using 1 <;> norm_num
              rcases le_total tau.re (1/4 : ℝ) with hx112 | hx112
              · rcases le_total tau.im (-1/4 : ℝ) with hy112 | hy112
                · have hs1120 : InSquare (9/40) (-11/40) (1/40) tau := by
                    convert childLL hs112 hx112 hy112 using 1 <;> norm_num
                  exact Coverage1120.cover htau hs1120
                · have hs1122 : InSquare (9/40) (-9/40) (1/40) tau := by
                    convert childUL hs112 hx112 hy112 using 1 <;> norm_num
                  exact Coverage1122.cover htau hs1122
              · rcases le_total tau.im (-1/4 : ℝ) with hy112 | hy112
                · have hs1121 : InSquare (11/40) (-11/40) (1/40) tau := by
                    convert childLR hs112 hx112 hy112 using 1 <;> norm_num
                  exact Coverage1121.cover htau hs1121
                · have hs1123 : InSquare (11/40) (-9/40) (1/40) tau := by
                    convert childUR hs112 hx112 hy112 using 1 <;> norm_num
                  exact Coverage1123.cover htau hs1123
          · rcases le_total tau.im (-3/10 : ℝ) with hy11 | hy11
            · have hs111 : InSquare (7/20) (-7/20) (1/20) tau := by
                convert childLR hs11 hx11 hy11 using 1 <;> norm_num
              exact (outside_111_priv htau hs111).elim
            · have hs113 : InSquare (7/20) (-1/4) (1/20) tau := by
                convert childUR hs11 hx11 hy11 using 1 <;> norm_num
              rcases le_total tau.re (7/20 : ℝ) with hx113 | hx113
              · rcases le_total tau.im (-1/4 : ℝ) with hy113 | hy113
                · have hs1130 : InSquare (13/40) (-11/40) (1/40) tau := by
                    convert childLL hs113 hx113 hy113 using 1 <;> norm_num
                  exact Coverage1130.cover htau hs1130
                · have hs1132 : InSquare (13/40) (-9/40) (1/40) tau := by
                    convert childUL hs113 hx113 hy113 using 1 <;> norm_num
                  exact Coverage1132.cover htau hs1132
              · rcases le_total tau.im (-1/4 : ℝ) with hy113 | hy113
                · have hs1131 : InSquare (3/8) (-11/40) (1/40) tau := by
                    convert childLR hs113 hx113 hy113 using 1 <;> norm_num
                  exact (outside_1131_priv htau hs1131).elim
                · have hs1133 : InSquare (3/8) (-9/40) (1/40) tau := by
                    convert childUR hs113 hx113 hy113 using 1 <;> norm_num
                  exact (outside_1133_priv htau hs1133).elim
        · have hs13 : InSquare (3/10) (-1/10) (1/10) tau := by
            convert childUR hs1 hx1 hy1 using 1 <;> norm_num
          rcases le_total tau.re (3/10 : ℝ) with hx13 | hx13
          · rcases le_total tau.im (-1/10 : ℝ) with hy13 | hy13
            · have hs130 : InSquare (1/4) (-3/20) (1/20) tau := by
                convert childLL hs13 hx13 hy13 using 1 <;> norm_num
              rcases le_total tau.re (1/4 : ℝ) with hx130 | hx130
              · rcases le_total tau.im (-3/20 : ℝ) with hy130 | hy130
                · have hs1300 : InSquare (9/40) (-7/40) (1/40) tau := by
                    convert childLL hs130 hx130 hy130 using 1 <;> norm_num
                  exact Coverage1300.cover htau hs1300
                · have hs1302 : InSquare (9/40) (-1/8) (1/40) tau := by
                    convert childUL hs130 hx130 hy130 using 1 <;> norm_num
                  exact Coverage1302.cover htau hs1302
              · rcases le_total tau.im (-3/20 : ℝ) with hy130 | hy130
                · have hs1301 : InSquare (11/40) (-7/40) (1/40) tau := by
                    convert childLR hs130 hx130 hy130 using 1 <;> norm_num
                  exact Coverage1301.cover htau hs1301
                · have hs1303 : InSquare (11/40) (-1/8) (1/40) tau := by
                    convert childUR hs130 hx130 hy130 using 1 <;> norm_num
                  exact Coverage1303.cover htau hs1303
            · have hs132 : InSquare (1/4) (-1/20) (1/20) tau := by
                convert childUL hs13 hx13 hy13 using 1 <;> norm_num
              rcases le_total tau.re (1/4 : ℝ) with hx132 | hx132
              · rcases le_total tau.im (-1/20 : ℝ) with hy132 | hy132
                · have hs1320 : InSquare (9/40) (-3/40) (1/40) tau := by
                    convert childLL hs132 hx132 hy132 using 1 <;> norm_num
                  exact Coverage1320.cover htau hs1320
                · have hs1322 : InSquare (9/40) (-1/40) (1/40) tau := by
                    convert childUL hs132 hx132 hy132 using 1 <;> norm_num
                  exact Batch0003.cell0025.sound htau (by
                    simp only [Batch0003.cell0025, Batch0003.tau0025, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs1322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-1/20 : ℝ) with hy132 | hy132
                · have hs1321 : InSquare (11/40) (-3/40) (1/40) tau := by
                    convert childLR hs132 hx132 hy132 using 1 <;> norm_num
                  exact Coverage1321.cover htau hs1321
                · have hs1323 : InSquare (11/40) (-1/40) (1/40) tau := by
                    convert childUR hs132 hx132 hy132 using 1 <;> norm_num
                  exact Coverage1323.cover htau hs1323
          · rcases le_total tau.im (-1/10 : ℝ) with hy13 | hy13
            · have hs131 : InSquare (7/20) (-3/20) (1/20) tau := by
                convert childLR hs13 hx13 hy13 using 1 <;> norm_num
              rcases le_total tau.re (7/20 : ℝ) with hx131 | hx131
              · rcases le_total tau.im (-3/20 : ℝ) with hy131 | hy131
                · have hs1310 : InSquare (13/40) (-7/40) (1/40) tau := by
                    convert childLL hs131 hx131 hy131 using 1 <;> norm_num
                  exact Coverage1310.cover htau hs1310
                · have hs1312 : InSquare (13/40) (-1/8) (1/40) tau := by
                    convert childUL hs131 hx131 hy131 using 1 <;> norm_num
                  exact Coverage1312.cover htau hs1312
              · rcases le_total tau.im (-3/20 : ℝ) with hy131 | hy131
                · have hs1311 : InSquare (3/8) (-7/40) (1/40) tau := by
                    convert childLR hs131 hx131 hy131 using 1 <;> norm_num
                  exact Coverage1311.cover htau hs1311
                · have hs1313 : InSquare (3/8) (-1/8) (1/40) tau := by
                    convert childUR hs131 hx131 hy131 using 1 <;> norm_num
                  exact Coverage1313.cover htau hs1313
            · have hs133 : InSquare (7/20) (-1/20) (1/20) tau := by
                convert childUR hs13 hx13 hy13 using 1 <;> norm_num
              rcases le_total tau.re (7/20 : ℝ) with hx133 | hx133
              · rcases le_total tau.im (-1/20 : ℝ) with hy133 | hy133
                · have hs1330 : InSquare (13/40) (-3/40) (1/40) tau := by
                    convert childLL hs133 hx133 hy133 using 1 <;> norm_num
                  exact Coverage1330.cover htau hs1330
                · have hs1332 : InSquare (13/40) (-1/40) (1/40) tau := by
                    convert childUL hs133 hx133 hy133 using 1 <;> norm_num
                  exact Coverage1332.cover htau hs1332
              · rcases le_total tau.im (-1/20 : ℝ) with hy133 | hy133
                · have hs1331 : InSquare (3/8) (-3/40) (1/40) tau := by
                    convert childLR hs133 hx133 hy133 using 1 <;> norm_num
                  exact Coverage1331.cover htau hs1331
                · have hs1333 : InSquare (3/8) (-1/40) (1/40) tau := by
                    convert childUR hs133 hx133 hy133 using 1 <;> norm_num
                  exact Coverage1333.cover htau hs1333
    · have hs3 : InSquare (1/5) (1/5) (1/5) tau := by
        convert childUR (disc_in_root htau) hxroot hyroot using 1 <;> norm_num
      rcases le_total tau.re (1/5 : ℝ) with hx3 | hx3
      · rcases le_total tau.im (1/5 : ℝ) with hy3 | hy3
        · have hs30 : InSquare (1/10) (1/10) (1/10) tau := by
            convert childLL hs3 hx3 hy3 using 1 <;> norm_num
          rcases le_total tau.re (1/10 : ℝ) with hx30 | hx30
          · rcases le_total tau.im (1/10 : ℝ) with hy30 | hy30
            · have hs300 : InSquare (1/20) (1/20) (1/20) tau := by
                convert childLL hs30 hx30 hy30 using 1 <;> norm_num
              rcases le_total tau.re (1/20 : ℝ) with hx300 | hx300
              · rcases le_total tau.im (1/20 : ℝ) with hy300 | hy300
                · have hs3000 : InSquare (1/40) (1/40) (1/40) tau := by
                    convert childLL hs300 hx300 hy300 using 1 <;> norm_num
                  exact Batch0004.cell0039.sound htau (by
                    simp only [Batch0004.cell0039, Batch0004.tau0039, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs3000 (by positivity) using 1 <;> norm_num)
                · have hs3002 : InSquare (1/40) (3/40) (1/40) tau := by
                    convert childUL hs300 hx300 hy300 using 1 <;> norm_num
                  exact Batch0005.cell0041.sound htau (by
                    simp only [Batch0005.cell0041, Batch0005.tau0041, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs3002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (1/20 : ℝ) with hy300 | hy300
                · have hs3001 : InSquare (3/40) (1/40) (1/40) tau := by
                    convert childLR hs300 hx300 hy300 using 1 <;> norm_num
                  exact Batch0005.cell0040.sound htau (by
                    simp only [Batch0005.cell0040, Batch0005.tau0040, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs3001 (by positivity) using 1 <;> norm_num)
                · have hs3003 : InSquare (3/40) (3/40) (1/40) tau := by
                    convert childUR hs300 hx300 hy300 using 1 <;> norm_num
                  exact Batch0005.cell0042.sound htau (by
                    simp only [Batch0005.cell0042, Batch0005.tau0042, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs3003 (by positivity) using 1 <;> norm_num)
            · have hs302 : InSquare (1/20) (3/20) (1/20) tau := by
                convert childUL hs30 hx30 hy30 using 1 <;> norm_num
              rcases le_total tau.re (1/20 : ℝ) with hx302 | hx302
              · rcases le_total tau.im (3/20 : ℝ) with hy302 | hy302
                · have hs3020 : InSquare (1/40) (1/8) (1/40) tau := by
                    convert childLL hs302 hx302 hy302 using 1 <;> norm_num
                  exact Batch0005.cell0047.sound htau (by
                    simp only [Batch0005.cell0047, Batch0005.tau0047, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs3020 (by positivity) using 1 <;> norm_num)
                · have hs3022 : InSquare (1/40) (7/40) (1/40) tau := by
                    convert childUL hs302 hx302 hy302 using 1 <;> norm_num
                  exact Batch0006.cell0049.sound htau (by
                    simp only [Batch0006.cell0049, Batch0006.tau0049, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs3022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (3/20 : ℝ) with hy302 | hy302
                · have hs3021 : InSquare (3/40) (1/8) (1/40) tau := by
                    convert childLR hs302 hx302 hy302 using 1 <;> norm_num
                  exact Batch0006.cell0048.sound htau (by
                    simp only [Batch0006.cell0048, Batch0006.tau0048, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs3021 (by positivity) using 1 <;> norm_num)
                · have hs3023 : InSquare (3/40) (7/40) (1/40) tau := by
                    convert childUR hs302 hx302 hy302 using 1 <;> norm_num
                  exact Coverage3023.cover htau hs3023
          · rcases le_total tau.im (1/10 : ℝ) with hy30 | hy30
            · have hs301 : InSquare (3/20) (1/20) (1/20) tau := by
                convert childLR hs30 hx30 hy30 using 1 <;> norm_num
              rcases le_total tau.re (3/20 : ℝ) with hx301 | hx301
              · rcases le_total tau.im (1/20 : ℝ) with hy301 | hy301
                · have hs3010 : InSquare (1/8) (1/40) (1/40) tau := by
                    convert childLL hs301 hx301 hy301 using 1 <;> norm_num
                  exact Batch0005.cell0043.sound htau (by
                    simp only [Batch0005.cell0043, Batch0005.tau0043, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs3010 (by positivity) using 1 <;> norm_num)
                · have hs3012 : InSquare (1/8) (3/40) (1/40) tau := by
                    convert childUL hs301 hx301 hy301 using 1 <;> norm_num
                  exact Batch0005.cell0045.sound htau (by
                    simp only [Batch0005.cell0045, Batch0005.tau0045, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs3012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (1/20 : ℝ) with hy301 | hy301
                · have hs3011 : InSquare (7/40) (1/40) (1/40) tau := by
                    convert childLR hs301 hx301 hy301 using 1 <;> norm_num
                  exact Batch0005.cell0044.sound htau (by
                    simp only [Batch0005.cell0044, Batch0005.tau0044, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs3011 (by positivity) using 1 <;> norm_num)
                · have hs3013 : InSquare (7/40) (3/40) (1/40) tau := by
                    convert childUR hs301 hx301 hy301 using 1 <;> norm_num
                  exact Batch0005.cell0046.sound htau (by
                    simp only [Batch0005.cell0046, Batch0005.tau0046, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs3013 (by positivity) using 1 <;> norm_num)
            · have hs303 : InSquare (3/20) (3/20) (1/20) tau := by
                convert childUR hs30 hx30 hy30 using 1 <;> norm_num
              rcases le_total tau.re (3/20 : ℝ) with hx303 | hx303
              · rcases le_total tau.im (3/20 : ℝ) with hy303 | hy303
                · have hs3030 : InSquare (1/8) (1/8) (1/40) tau := by
                    convert childLL hs303 hx303 hy303 using 1 <;> norm_num
                  exact Batch0006.cell0050.sound htau (by
                    simp only [Batch0006.cell0050, Batch0006.tau0050, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs3030 (by positivity) using 1 <;> norm_num)
                · have hs3032 : InSquare (1/8) (7/40) (1/40) tau := by
                    convert childUL hs303 hx303 hy303 using 1 <;> norm_num
                  exact Coverage3032.cover htau hs3032
              · rcases le_total tau.im (3/20 : ℝ) with hy303 | hy303
                · have hs3031 : InSquare (7/40) (1/8) (1/40) tau := by
                    convert childLR hs303 hx303 hy303 using 1 <;> norm_num
                  exact Coverage3031.cover htau hs3031
                · have hs3033 : InSquare (7/40) (7/40) (1/40) tau := by
                    convert childUR hs303 hx303 hy303 using 1 <;> norm_num
                  exact Coverage3033.cover htau hs3033
        · have hs32 : InSquare (1/10) (3/10) (1/10) tau := by
            convert childUL hs3 hx3 hy3 using 1 <;> norm_num
          rcases le_total tau.re (1/10 : ℝ) with hx32 | hx32
          · rcases le_total tau.im (3/10 : ℝ) with hy32 | hy32
            · have hs320 : InSquare (1/20) (1/4) (1/20) tau := by
                convert childLL hs32 hx32 hy32 using 1 <;> norm_num
              rcases le_total tau.re (1/20 : ℝ) with hx320 | hx320
              · rcases le_total tau.im (1/4 : ℝ) with hy320 | hy320
                · have hs3200 : InSquare (1/40) (9/40) (1/40) tau := by
                    convert childLL hs320 hx320 hy320 using 1 <;> norm_num
                  exact Coverage3200.cover htau hs3200
                · have hs3202 : InSquare (1/40) (11/40) (1/40) tau := by
                    convert childUL hs320 hx320 hy320 using 1 <;> norm_num
                  exact Coverage3202.cover htau hs3202
              · rcases le_total tau.im (1/4 : ℝ) with hy320 | hy320
                · have hs3201 : InSquare (3/40) (9/40) (1/40) tau := by
                    convert childLR hs320 hx320 hy320 using 1 <;> norm_num
                  exact Coverage3201.cover htau hs3201
                · have hs3203 : InSquare (3/40) (11/40) (1/40) tau := by
                    convert childUR hs320 hx320 hy320 using 1 <;> norm_num
                  exact Coverage3203.cover htau hs3203
            · have hs322 : InSquare (1/20) (7/20) (1/20) tau := by
                convert childUL hs32 hx32 hy32 using 1 <;> norm_num
              rcases le_total tau.re (1/20 : ℝ) with hx322 | hx322
              · rcases le_total tau.im (7/20 : ℝ) with hy322 | hy322
                · have hs3220 : InSquare (1/40) (13/40) (1/40) tau := by
                    convert childLL hs322 hx322 hy322 using 1 <;> norm_num
                  exact Coverage3220.cover htau hs3220
                · have hs3222 : InSquare (1/40) (3/8) (1/40) tau := by
                    convert childUL hs322 hx322 hy322 using 1 <;> norm_num
                  exact Coverage3222.cover htau hs3222
              · rcases le_total tau.im (7/20 : ℝ) with hy322 | hy322
                · have hs3221 : InSquare (3/40) (13/40) (1/40) tau := by
                    convert childLR hs322 hx322 hy322 using 1 <;> norm_num
                  exact Coverage3221.cover htau hs3221
                · have hs3223 : InSquare (3/40) (3/8) (1/40) tau := by
                    convert childUR hs322 hx322 hy322 using 1 <;> norm_num
                  exact Coverage3223.cover htau hs3223
          · rcases le_total tau.im (3/10 : ℝ) with hy32 | hy32
            · have hs321 : InSquare (3/20) (1/4) (1/20) tau := by
                convert childLR hs32 hx32 hy32 using 1 <;> norm_num
              rcases le_total tau.re (3/20 : ℝ) with hx321 | hx321
              · rcases le_total tau.im (1/4 : ℝ) with hy321 | hy321
                · have hs3210 : InSquare (1/8) (9/40) (1/40) tau := by
                    convert childLL hs321 hx321 hy321 using 1 <;> norm_num
                  exact Coverage3210.cover htau hs3210
                · have hs3212 : InSquare (1/8) (11/40) (1/40) tau := by
                    convert childUL hs321 hx321 hy321 using 1 <;> norm_num
                  exact Coverage3212.cover htau hs3212
              · rcases le_total tau.im (1/4 : ℝ) with hy321 | hy321
                · have hs3211 : InSquare (7/40) (9/40) (1/40) tau := by
                    convert childLR hs321 hx321 hy321 using 1 <;> norm_num
                  exact Coverage3211.cover htau hs3211
                · have hs3213 : InSquare (7/40) (11/40) (1/40) tau := by
                    convert childUR hs321 hx321 hy321 using 1 <;> norm_num
                  exact Coverage3213.cover htau hs3213
            · have hs323 : InSquare (3/20) (7/20) (1/20) tau := by
                convert childUR hs32 hx32 hy32 using 1 <;> norm_num
              rcases le_total tau.re (3/20 : ℝ) with hx323 | hx323
              · rcases le_total tau.im (7/20 : ℝ) with hy323 | hy323
                · have hs3230 : InSquare (1/8) (13/40) (1/40) tau := by
                    convert childLL hs323 hx323 hy323 using 1 <;> norm_num
                  exact Coverage3230.cover htau hs3230
                · have hs3232 : InSquare (1/8) (3/8) (1/40) tau := by
                    convert childUL hs323 hx323 hy323 using 1 <;> norm_num
                  exact Coverage3232.cover htau hs3232
              · rcases le_total tau.im (7/20 : ℝ) with hy323 | hy323
                · have hs3231 : InSquare (7/40) (13/40) (1/40) tau := by
                    convert childLR hs323 hx323 hy323 using 1 <;> norm_num
                  exact Coverage3231.cover htau hs3231
                · have hs3233 : InSquare (7/40) (3/8) (1/40) tau := by
                    convert childUR hs323 hx323 hy323 using 1 <;> norm_num
                  exact Coverage3233.cover htau hs3233
      · rcases le_total tau.im (1/5 : ℝ) with hy3 | hy3
        · have hs31 : InSquare (3/10) (1/10) (1/10) tau := by
            convert childLR hs3 hx3 hy3 using 1 <;> norm_num
          rcases le_total tau.re (3/10 : ℝ) with hx31 | hx31
          · rcases le_total tau.im (1/10 : ℝ) with hy31 | hy31
            · have hs310 : InSquare (1/4) (1/20) (1/20) tau := by
                convert childLL hs31 hx31 hy31 using 1 <;> norm_num
              rcases le_total tau.re (1/4 : ℝ) with hx310 | hx310
              · rcases le_total tau.im (1/20 : ℝ) with hy310 | hy310
                · have hs3100 : InSquare (9/40) (1/40) (1/40) tau := by
                    convert childLL hs310 hx310 hy310 using 1 <;> norm_num
                  exact Batch0006.cell0051.sound htau (by
                    simp only [Batch0006.cell0051, Batch0006.tau0051, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs3100 (by positivity) using 1 <;> norm_num)
                · have hs3102 : InSquare (9/40) (3/40) (1/40) tau := by
                    convert childUL hs310 hx310 hy310 using 1 <;> norm_num
                  exact Coverage3102.cover htau hs3102
              · rcases le_total tau.im (1/20 : ℝ) with hy310 | hy310
                · have hs3101 : InSquare (11/40) (1/40) (1/40) tau := by
                    convert childLR hs310 hx310 hy310 using 1 <;> norm_num
                  exact Coverage3101.cover htau hs3101
                · have hs3103 : InSquare (11/40) (3/40) (1/40) tau := by
                    convert childUR hs310 hx310 hy310 using 1 <;> norm_num
                  exact Coverage3103.cover htau hs3103
            · have hs312 : InSquare (1/4) (3/20) (1/20) tau := by
                convert childUL hs31 hx31 hy31 using 1 <;> norm_num
              rcases le_total tau.re (1/4 : ℝ) with hx312 | hx312
              · rcases le_total tau.im (3/20 : ℝ) with hy312 | hy312
                · have hs3120 : InSquare (9/40) (1/8) (1/40) tau := by
                    convert childLL hs312 hx312 hy312 using 1 <;> norm_num
                  exact Coverage3120.cover htau hs3120
                · have hs3122 : InSquare (9/40) (7/40) (1/40) tau := by
                    convert childUL hs312 hx312 hy312 using 1 <;> norm_num
                  exact Coverage3122.cover htau hs3122
              · rcases le_total tau.im (3/20 : ℝ) with hy312 | hy312
                · have hs3121 : InSquare (11/40) (1/8) (1/40) tau := by
                    convert childLR hs312 hx312 hy312 using 1 <;> norm_num
                  exact Coverage3121.cover htau hs3121
                · have hs3123 : InSquare (11/40) (7/40) (1/40) tau := by
                    convert childUR hs312 hx312 hy312 using 1 <;> norm_num
                  exact Coverage3123.cover htau hs3123
          · rcases le_total tau.im (1/10 : ℝ) with hy31 | hy31
            · have hs311 : InSquare (7/20) (1/20) (1/20) tau := by
                convert childLR hs31 hx31 hy31 using 1 <;> norm_num
              rcases le_total tau.re (7/20 : ℝ) with hx311 | hx311
              · rcases le_total tau.im (1/20 : ℝ) with hy311 | hy311
                · have hs3110 : InSquare (13/40) (1/40) (1/40) tau := by
                    convert childLL hs311 hx311 hy311 using 1 <;> norm_num
                  exact Coverage3110.cover htau hs3110
                · have hs3112 : InSquare (13/40) (3/40) (1/40) tau := by
                    convert childUL hs311 hx311 hy311 using 1 <;> norm_num
                  exact Coverage3112.cover htau hs3112
              · rcases le_total tau.im (1/20 : ℝ) with hy311 | hy311
                · have hs3111 : InSquare (3/8) (1/40) (1/40) tau := by
                    convert childLR hs311 hx311 hy311 using 1 <;> norm_num
                  exact Coverage3111.cover htau hs3111
                · have hs3113 : InSquare (3/8) (3/40) (1/40) tau := by
                    convert childUR hs311 hx311 hy311 using 1 <;> norm_num
                  exact Coverage3113.cover htau hs3113
            · have hs313 : InSquare (7/20) (3/20) (1/20) tau := by
                convert childUR hs31 hx31 hy31 using 1 <;> norm_num
              rcases le_total tau.re (7/20 : ℝ) with hx313 | hx313
              · rcases le_total tau.im (3/20 : ℝ) with hy313 | hy313
                · have hs3130 : InSquare (13/40) (1/8) (1/40) tau := by
                    convert childLL hs313 hx313 hy313 using 1 <;> norm_num
                  exact Coverage3130.cover htau hs3130
                · have hs3132 : InSquare (13/40) (7/40) (1/40) tau := by
                    convert childUL hs313 hx313 hy313 using 1 <;> norm_num
                  exact Coverage3132.cover htau hs3132
              · rcases le_total tau.im (3/20 : ℝ) with hy313 | hy313
                · have hs3131 : InSquare (3/8) (1/8) (1/40) tau := by
                    convert childLR hs313 hx313 hy313 using 1 <;> norm_num
                  exact Coverage3131.cover htau hs3131
                · have hs3133 : InSquare (3/8) (7/40) (1/40) tau := by
                    convert childUR hs313 hx313 hy313 using 1 <;> norm_num
                  exact Coverage3133.cover htau hs3133
        · have hs33 : InSquare (3/10) (3/10) (1/10) tau := by
            convert childUR hs3 hx3 hy3 using 1 <;> norm_num
          rcases le_total tau.re (3/10 : ℝ) with hx33 | hx33
          · rcases le_total tau.im (3/10 : ℝ) with hy33 | hy33
            · have hs330 : InSquare (1/4) (1/4) (1/20) tau := by
                convert childLL hs33 hx33 hy33 using 1 <;> norm_num
              rcases le_total tau.re (1/4 : ℝ) with hx330 | hx330
              · rcases le_total tau.im (1/4 : ℝ) with hy330 | hy330
                · have hs3300 : InSquare (9/40) (9/40) (1/40) tau := by
                    convert childLL hs330 hx330 hy330 using 1 <;> norm_num
                  exact Coverage3300.cover htau hs3300
                · have hs3302 : InSquare (9/40) (11/40) (1/40) tau := by
                    convert childUL hs330 hx330 hy330 using 1 <;> norm_num
                  exact Coverage3302.cover htau hs3302
              · rcases le_total tau.im (1/4 : ℝ) with hy330 | hy330
                · have hs3301 : InSquare (11/40) (9/40) (1/40) tau := by
                    convert childLR hs330 hx330 hy330 using 1 <;> norm_num
                  exact Coverage3301.cover htau hs3301
                · have hs3303 : InSquare (11/40) (11/40) (1/40) tau := by
                    convert childUR hs330 hx330 hy330 using 1 <;> norm_num
                  exact Coverage3303.cover htau hs3303
            · have hs332 : InSquare (1/4) (7/20) (1/20) tau := by
                convert childUL hs33 hx33 hy33 using 1 <;> norm_num
              rcases le_total tau.re (1/4 : ℝ) with hx332 | hx332
              · rcases le_total tau.im (7/20 : ℝ) with hy332 | hy332
                · have hs3320 : InSquare (9/40) (13/40) (1/40) tau := by
                    convert childLL hs332 hx332 hy332 using 1 <;> norm_num
                  exact Coverage3320.cover htau hs3320
                · have hs3322 : InSquare (9/40) (3/8) (1/40) tau := by
                    convert childUL hs332 hx332 hy332 using 1 <;> norm_num
                  exact (outside_3322_priv htau hs3322).elim
              · rcases le_total tau.im (7/20 : ℝ) with hy332 | hy332
                · have hs3321 : InSquare (11/40) (13/40) (1/40) tau := by
                    convert childLR hs332 hx332 hy332 using 1 <;> norm_num
                  exact Coverage3321.cover htau hs3321
                · have hs3323 : InSquare (11/40) (3/8) (1/40) tau := by
                    convert childUR hs332 hx332 hy332 using 1 <;> norm_num
                  exact (outside_3323_priv htau hs3323).elim
          · rcases le_total tau.im (3/10 : ℝ) with hy33 | hy33
            · have hs331 : InSquare (7/20) (1/4) (1/20) tau := by
                convert childLR hs33 hx33 hy33 using 1 <;> norm_num
              rcases le_total tau.re (7/20 : ℝ) with hx331 | hx331
              · rcases le_total tau.im (1/4 : ℝ) with hy331 | hy331
                · have hs3310 : InSquare (13/40) (9/40) (1/40) tau := by
                    convert childLL hs331 hx331 hy331 using 1 <;> norm_num
                  exact Coverage3310.cover htau hs3310
                · have hs3312 : InSquare (13/40) (11/40) (1/40) tau := by
                    convert childUL hs331 hx331 hy331 using 1 <;> norm_num
                  exact Coverage3312.cover htau hs3312
              · rcases le_total tau.im (1/4 : ℝ) with hy331 | hy331
                · have hs3311 : InSquare (3/8) (9/40) (1/40) tau := by
                    convert childLR hs331 hx331 hy331 using 1 <;> norm_num
                  exact (outside_3311_priv htau hs3311).elim
                · have hs3313 : InSquare (3/8) (11/40) (1/40) tau := by
                    convert childUR hs331 hx331 hy331 using 1 <;> norm_num
                  exact (outside_3313_priv htau hs3313).elim
            · have hs333 : InSquare (7/20) (7/20) (1/20) tau := by
                convert childUR hs33 hx33 hy33 using 1 <;> norm_num
              exact (outside_333_priv htau hs333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate


