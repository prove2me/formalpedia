-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2020__6
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2020__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:17:15.414545+00:00
-- url     : https://prove2.me/theorems/4e12be69-1e37-4fce-baa6-80f447f01ba6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2020 (+5 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2021, GeneralCK.Certific…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2020 (+5 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2021, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2022, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2023, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2030, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2031)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2020 (+5 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2021, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2022, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2023, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2030, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2031)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2020 (+5 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2021, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2022, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2023, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2030, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2031) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2020 (+5 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2021, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2022, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2023, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2030, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2031).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0098
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0099
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0027
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0100
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0101
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0102
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0235
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0103
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0104
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0028

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2020 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2020

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_202000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (17/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (1/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_202002 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (19/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (9/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_202020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (21/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (1/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_202022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (23/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (11/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/8 : ℝ) with hx2020 | hx2020
  · rcases le_total tau.im (1/8 : ℝ) with hy2020 | hy2020
    · have hs20200 : InSquare (-31/80) (9/80) (1/80) tau := by
        convert childLL hs hx2020 hy2020 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx20200 | hx20200
      · rcases le_total tau.im (9/80 : ℝ) with hy20200 | hy20200
        · have hs202000 : InSquare (-63/160) (17/160) (1/160) tau := by
            convert childLL hs20200 hx20200 hy20200 using 1 <;> norm_num
          exact (outside_202000 htau hs202000).elim
        · have hs202002 : InSquare (-63/160) (19/160) (1/160) tau := by
            convert childUL hs20200 hx20200 hy20200 using 1 <;> norm_num
          exact (outside_202002 htau hs202002).elim
      · rcases le_total tau.im (9/80 : ℝ) with hy20200 | hy20200
        · have hs202001 : InSquare (-61/160) (17/160) (1/160) tau := by
            convert childLR hs20200 hx20200 hy20200 using 1 <;> norm_num
          exact Batch0098.cell0788.sound htau (by
            simp only [Batch0098.cell0788, Batch0098.tau0788, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202001 (by positivity) using 1 <;> norm_num)
        · have hs202003 : InSquare (-61/160) (19/160) (1/160) tau := by
            convert childUR hs20200 hx20200 hy20200 using 1 <;> norm_num
          exact Batch0098.cell0789.sound htau (by
            simp only [Batch0098.cell0789, Batch0098.tau0789, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202003 (by positivity) using 1 <;> norm_num)
    · have hs20202 : InSquare (-31/80) (11/80) (1/80) tau := by
        convert childUL hs hx2020 hy2020 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx20202 | hx20202
      · rcases le_total tau.im (11/80 : ℝ) with hy20202 | hy20202
        · have hs202020 : InSquare (-63/160) (21/160) (1/160) tau := by
            convert childLL hs20202 hx20202 hy20202 using 1 <;> norm_num
          exact (outside_202020 htau hs202020).elim
        · have hs202022 : InSquare (-63/160) (23/160) (1/160) tau := by
            convert childUL hs20202 hx20202 hy20202 using 1 <;> norm_num
          exact (outside_202022 htau hs202022).elim
      · rcases le_total tau.im (11/80 : ℝ) with hy20202 | hy20202
        · have hs202021 : InSquare (-61/160) (21/160) (1/160) tau := by
            convert childLR hs20202 hx20202 hy20202 using 1 <;> norm_num
          exact Batch0099.cell0794.sound htau (by
            simp only [Batch0099.cell0794, Batch0099.tau0794, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202021 (by positivity) using 1 <;> norm_num)
        · have hs202023 : InSquare (-61/160) (23/160) (1/160) tau := by
            convert childUR hs20202 hx20202 hy20202 using 1 <;> norm_num
          exact Batch0099.cell0795.sound htau (by
            simp only [Batch0099.cell0795, Batch0099.tau0795, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy2020 | hy2020
    · have hs20201 : InSquare (-29/80) (9/80) (1/80) tau := by
        convert childLR hs hx2020 hy2020 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx20201 | hx20201
      · rcases le_total tau.im (9/80 : ℝ) with hy20201 | hy20201
        · have hs202010 : InSquare (-59/160) (17/160) (1/160) tau := by
            convert childLL hs20201 hx20201 hy20201 using 1 <;> norm_num
          exact Batch0098.cell0790.sound htau (by
            simp only [Batch0098.cell0790, Batch0098.tau0790, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202010 (by positivity) using 1 <;> norm_num)
        · have hs202012 : InSquare (-59/160) (19/160) (1/160) tau := by
            convert childUL hs20201 hx20201 hy20201 using 1 <;> norm_num
          exact Batch0099.cell0792.sound htau (by
            simp only [Batch0099.cell0792, Batch0099.tau0792, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (9/80 : ℝ) with hy20201 | hy20201
        · have hs202011 : InSquare (-57/160) (17/160) (1/160) tau := by
            convert childLR hs20201 hx20201 hy20201 using 1 <;> norm_num
          exact Batch0098.cell0791.sound htau (by
            simp only [Batch0098.cell0791, Batch0098.tau0791, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202011 (by positivity) using 1 <;> norm_num)
        · have hs202013 : InSquare (-57/160) (19/160) (1/160) tau := by
            convert childUR hs20201 hx20201 hy20201 using 1 <;> norm_num
          exact Batch0099.cell0793.sound htau (by
            simp only [Batch0099.cell0793, Batch0099.tau0793, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202013 (by positivity) using 1 <;> norm_num)
    · have hs20203 : InSquare (-29/80) (11/80) (1/80) tau := by
        convert childUR hs hx2020 hy2020 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx20203 | hx20203
      · rcases le_total tau.im (11/80 : ℝ) with hy20203 | hy20203
        · have hs202030 : InSquare (-59/160) (21/160) (1/160) tau := by
            convert childLL hs20203 hx20203 hy20203 using 1 <;> norm_num
          exact Batch0099.cell0796.sound htau (by
            simp only [Batch0099.cell0796, Batch0099.tau0796, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202030 (by positivity) using 1 <;> norm_num)
        · have hs202032 : InSquare (-59/160) (23/160) (1/160) tau := by
            convert childUL hs20203 hx20203 hy20203 using 1 <;> norm_num
          exact Batch0099.cell0798.sound htau (by
            simp only [Batch0099.cell0798, Batch0099.tau0798, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (11/80 : ℝ) with hy20203 | hy20203
        · have hs202031 : InSquare (-57/160) (21/160) (1/160) tau := by
            convert childLR hs20203 hx20203 hy20203 using 1 <;> norm_num
          exact Batch0099.cell0797.sound htau (by
            simp only [Batch0099.cell0797, Batch0099.tau0797, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202031 (by positivity) using 1 <;> norm_num)
        · have hs202033 : InSquare (-57/160) (23/160) (1/160) tau := by
            convert childUR hs20203 hx20203 hy20203 using 1 <;> norm_num
          exact Batch0099.cell0799.sound htau (by
            simp only [Batch0099.cell0799, Batch0099.tau0799, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2020

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2021 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2021

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx2021 | hx2021
  · rcases le_total tau.im (1/8 : ℝ) with hy2021 | hy2021
    · have hs20210 : InSquare (-27/80) (9/80) (1/80) tau := by
        convert childLL hs hx2021 hy2021 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx20210 | hx20210
      · rcases le_total tau.im (9/80 : ℝ) with hy20210 | hy20210
        · have hs202100 : InSquare (-11/32) (17/160) (1/160) tau := by
            convert childLL hs20210 hx20210 hy20210 using 1 <;> norm_num
          exact Batch0100.cell0800.sound htau (by
            simp only [Batch0100.cell0800, Batch0100.tau0800, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202100 (by positivity) using 1 <;> norm_num)
        · have hs202102 : InSquare (-11/32) (19/160) (1/160) tau := by
            convert childUL hs20210 hx20210 hy20210 using 1 <;> norm_num
          exact Batch0100.cell0802.sound htau (by
            simp only [Batch0100.cell0802, Batch0100.tau0802, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (9/80 : ℝ) with hy20210 | hy20210
        · have hs202101 : InSquare (-53/160) (17/160) (1/160) tau := by
            convert childLR hs20210 hx20210 hy20210 using 1 <;> norm_num
          exact Batch0100.cell0801.sound htau (by
            simp only [Batch0100.cell0801, Batch0100.tau0801, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202101 (by positivity) using 1 <;> norm_num)
        · have hs202103 : InSquare (-53/160) (19/160) (1/160) tau := by
            convert childUR hs20210 hx20210 hy20210 using 1 <;> norm_num
          exact Batch0100.cell0803.sound htau (by
            simp only [Batch0100.cell0803, Batch0100.tau0803, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202103 (by positivity) using 1 <;> norm_num)
    · have hs20212 : InSquare (-27/80) (11/80) (1/80) tau := by
        convert childUL hs hx2021 hy2021 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx20212 | hx20212
      · rcases le_total tau.im (11/80 : ℝ) with hy20212 | hy20212
        · have hs202120 : InSquare (-11/32) (21/160) (1/160) tau := by
            convert childLL hs20212 hx20212 hy20212 using 1 <;> norm_num
          exact Batch0100.cell0804.sound htau (by
            simp only [Batch0100.cell0804, Batch0100.tau0804, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202120 (by positivity) using 1 <;> norm_num)
        · have hs202122 : InSquare (-11/32) (23/160) (1/160) tau := by
            convert childUL hs20212 hx20212 hy20212 using 1 <;> norm_num
          exact Batch0100.cell0806.sound htau (by
            simp only [Batch0100.cell0806, Batch0100.tau0806, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (11/80 : ℝ) with hy20212 | hy20212
        · have hs202121 : InSquare (-53/160) (21/160) (1/160) tau := by
            convert childLR hs20212 hx20212 hy20212 using 1 <;> norm_num
          exact Batch0100.cell0805.sound htau (by
            simp only [Batch0100.cell0805, Batch0100.tau0805, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202121 (by positivity) using 1 <;> norm_num)
        · have hs202123 : InSquare (-53/160) (23/160) (1/160) tau := by
            convert childUR hs20212 hx20212 hy20212 using 1 <;> norm_num
          exact Batch0100.cell0807.sound htau (by
            simp only [Batch0100.cell0807, Batch0100.tau0807, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy2021 | hy2021
    · have hs20211 : InSquare (-5/16) (9/80) (1/80) tau := by
        convert childLR hs hx2021 hy2021 using 1 <;> norm_num
      exact Batch0027.cell0222.sound htau (by
        simp only [Batch0027.cell0222, Batch0027.tau0222, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20211 (by positivity) using 1 <;> norm_num)
    · have hs20213 : InSquare (-5/16) (11/80) (1/80) tau := by
        convert childUR hs hx2021 hy2021 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx20213 | hx20213
      · rcases le_total tau.im (11/80 : ℝ) with hy20213 | hy20213
        · have hs202130 : InSquare (-51/160) (21/160) (1/160) tau := by
            convert childLL hs20213 hx20213 hy20213 using 1 <;> norm_num
          exact Batch0101.cell0808.sound htau (by
            simp only [Batch0101.cell0808, Batch0101.tau0808, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202130 (by positivity) using 1 <;> norm_num)
        · have hs202132 : InSquare (-51/160) (23/160) (1/160) tau := by
            convert childUL hs20213 hx20213 hy20213 using 1 <;> norm_num
          exact Batch0101.cell0810.sound htau (by
            simp only [Batch0101.cell0810, Batch0101.tau0810, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (11/80 : ℝ) with hy20213 | hy20213
        · have hs202131 : InSquare (-49/160) (21/160) (1/160) tau := by
            convert childLR hs20213 hx20213 hy20213 using 1 <;> norm_num
          exact Batch0101.cell0809.sound htau (by
            simp only [Batch0101.cell0809, Batch0101.tau0809, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202131 (by positivity) using 1 <;> norm_num)
        · have hs202133 : InSquare (-49/160) (23/160) (1/160) tau := by
            convert childUR hs20213 hx20213 hy20213 using 1 <;> norm_num
          exact Batch0101.cell0811.sound htau (by
            simp only [Batch0101.cell0811, Batch0101.tau0811, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2021

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2022 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2022

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_20220 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/80) (13/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/8)]
  have himSq : (3/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_20222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/80) (3/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/8)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_202230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-59/160) (29/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/80)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_202232 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-59/160) (31/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/80)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2022330 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/64) (61/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+57/160)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2022332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/64) (63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+57/160)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2022333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-113/320) (63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/20)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/8 : ℝ) with hx2022 | hx2022
  · rcases le_total tau.im (7/40 : ℝ) with hy2022 | hy2022
    · have hs20220 : InSquare (-31/80) (13/80) (1/80) tau := by
        convert childLL hs hx2022 hy2022 using 1 <;> norm_num
      exact (outside_20220 htau hs20220).elim
    · have hs20222 : InSquare (-31/80) (3/16) (1/80) tau := by
        convert childUL hs hx2022 hy2022 using 1 <;> norm_num
      exact (outside_20222 htau hs20222).elim
  · rcases le_total tau.im (7/40 : ℝ) with hy2022 | hy2022
    · have hs20221 : InSquare (-29/80) (13/80) (1/80) tau := by
        convert childLR hs hx2022 hy2022 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx20221 | hx20221
      · rcases le_total tau.im (13/80 : ℝ) with hy20221 | hy20221
        · have hs202210 : InSquare (-59/160) (5/32) (1/160) tau := by
            convert childLL hs20221 hx20221 hy20221 using 1 <;> norm_num
          exact Batch0101.cell0812.sound htau (by
            simp only [Batch0101.cell0812, Batch0101.tau0812, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202210 (by positivity) using 1 <;> norm_num)
        · have hs202212 : InSquare (-59/160) (27/160) (1/160) tau := by
            convert childUL hs20221 hx20221 hy20221 using 1 <;> norm_num
          exact Batch0101.cell0814.sound htau (by
            simp only [Batch0101.cell0814, Batch0101.tau0814, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy20221 | hy20221
        · have hs202211 : InSquare (-57/160) (5/32) (1/160) tau := by
            convert childLR hs20221 hx20221 hy20221 using 1 <;> norm_num
          exact Batch0101.cell0813.sound htau (by
            simp only [Batch0101.cell0813, Batch0101.tau0813, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202211 (by positivity) using 1 <;> norm_num)
        · have hs202213 : InSquare (-57/160) (27/160) (1/160) tau := by
            convert childUR hs20221 hx20221 hy20221 using 1 <;> norm_num
          exact Batch0101.cell0815.sound htau (by
            simp only [Batch0101.cell0815, Batch0101.tau0815, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202213 (by positivity) using 1 <;> norm_num)
    · have hs20223 : InSquare (-29/80) (3/16) (1/80) tau := by
        convert childUR hs hx2022 hy2022 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx20223 | hx20223
      · rcases le_total tau.im (3/16 : ℝ) with hy20223 | hy20223
        · have hs202230 : InSquare (-59/160) (29/160) (1/160) tau := by
            convert childLL hs20223 hx20223 hy20223 using 1 <;> norm_num
          exact (outside_202230 htau hs202230).elim
        · have hs202232 : InSquare (-59/160) (31/160) (1/160) tau := by
            convert childUL hs20223 hx20223 hy20223 using 1 <;> norm_num
          exact (outside_202232 htau hs202232).elim
      · rcases le_total tau.im (3/16 : ℝ) with hy20223 | hy20223
        · have hs202231 : InSquare (-57/160) (29/160) (1/160) tau := by
            convert childLR hs20223 hx20223 hy20223 using 1 <;> norm_num
          exact Batch0102.cell0816.sound htau (by
            simp only [Batch0102.cell0816, Batch0102.tau0816, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202231 (by positivity) using 1 <;> norm_num)
        · have hs202233 : InSquare (-57/160) (31/160) (1/160) tau := by
            convert childUR hs20223 hx20223 hy20223 using 1 <;> norm_num
          rcases le_total tau.re (-57/160 : ℝ) with hx202233 | hx202233
          · rcases le_total tau.im (31/160 : ℝ) with hy202233 | hy202233
            · have hs2022330 : InSquare (-23/64) (61/320) (1/320) tau := by
                convert childLL hs202233 hx202233 hy202233 using 1 <;> norm_num
              exact (outside_2022330 htau hs2022330).elim
            · have hs2022332 : InSquare (-23/64) (63/320) (1/320) tau := by
                convert childUL hs202233 hx202233 hy202233 using 1 <;> norm_num
              exact (outside_2022332 htau hs2022332).elim
          · rcases le_total tau.im (31/160 : ℝ) with hy202233 | hy202233
            · have hs2022331 : InSquare (-113/320) (61/320) (1/320) tau := by
                convert childLR hs202233 hx202233 hy202233 using 1 <;> norm_num
              exact Batch0235.cell1882.sound htau (by
                simp only [Batch0235.cell1882, Batch0235.tau1882, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2022331 (by positivity) using 1 <;> norm_num)
            · have hs2022333 : InSquare (-113/320) (63/320) (1/320) tau := by
                convert childUR hs202233 hx202233 hy202233 using 1 <;> norm_num
              exact (outside_2022333 htau hs2022333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2022

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2023 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2023

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx2023 | hx2023
  · rcases le_total tau.im (7/40 : ℝ) with hy2023 | hy2023
    · have hs20230 : InSquare (-27/80) (13/80) (1/80) tau := by
        convert childLL hs hx2023 hy2023 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx20230 | hx20230
      · rcases le_total tau.im (13/80 : ℝ) with hy20230 | hy20230
        · have hs202300 : InSquare (-11/32) (5/32) (1/160) tau := by
            convert childLL hs20230 hx20230 hy20230 using 1 <;> norm_num
          exact Batch0102.cell0817.sound htau (by
            simp only [Batch0102.cell0817, Batch0102.tau0817, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202300 (by positivity) using 1 <;> norm_num)
        · have hs202302 : InSquare (-11/32) (27/160) (1/160) tau := by
            convert childUL hs20230 hx20230 hy20230 using 1 <;> norm_num
          exact Batch0102.cell0819.sound htau (by
            simp only [Batch0102.cell0819, Batch0102.tau0819, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy20230 | hy20230
        · have hs202301 : InSquare (-53/160) (5/32) (1/160) tau := by
            convert childLR hs20230 hx20230 hy20230 using 1 <;> norm_num
          exact Batch0102.cell0818.sound htau (by
            simp only [Batch0102.cell0818, Batch0102.tau0818, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202301 (by positivity) using 1 <;> norm_num)
        · have hs202303 : InSquare (-53/160) (27/160) (1/160) tau := by
            convert childUR hs20230 hx20230 hy20230 using 1 <;> norm_num
          exact Batch0102.cell0820.sound htau (by
            simp only [Batch0102.cell0820, Batch0102.tau0820, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202303 (by positivity) using 1 <;> norm_num)
    · have hs20232 : InSquare (-27/80) (3/16) (1/80) tau := by
        convert childUL hs hx2023 hy2023 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx20232 | hx20232
      · rcases le_total tau.im (3/16 : ℝ) with hy20232 | hy20232
        · have hs202320 : InSquare (-11/32) (29/160) (1/160) tau := by
            convert childLL hs20232 hx20232 hy20232 using 1 <;> norm_num
          exact Batch0103.cell0825.sound htau (by
            simp only [Batch0103.cell0825, Batch0103.tau0825, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202320 (by positivity) using 1 <;> norm_num)
        · have hs202322 : InSquare (-11/32) (31/160) (1/160) tau := by
            convert childUL hs20232 hx20232 hy20232 using 1 <;> norm_num
          exact Batch0103.cell0827.sound htau (by
            simp only [Batch0103.cell0827, Batch0103.tau0827, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy20232 | hy20232
        · have hs202321 : InSquare (-53/160) (29/160) (1/160) tau := by
            convert childLR hs20232 hx20232 hy20232 using 1 <;> norm_num
          exact Batch0103.cell0826.sound htau (by
            simp only [Batch0103.cell0826, Batch0103.tau0826, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202321 (by positivity) using 1 <;> norm_num)
        · have hs202323 : InSquare (-53/160) (31/160) (1/160) tau := by
            convert childUR hs20232 hx20232 hy20232 using 1 <;> norm_num
          exact Batch0103.cell0828.sound htau (by
            simp only [Batch0103.cell0828, Batch0103.tau0828, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy2023 | hy2023
    · have hs20231 : InSquare (-5/16) (13/80) (1/80) tau := by
        convert childLR hs hx2023 hy2023 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx20231 | hx20231
      · rcases le_total tau.im (13/80 : ℝ) with hy20231 | hy20231
        · have hs202310 : InSquare (-51/160) (5/32) (1/160) tau := by
            convert childLL hs20231 hx20231 hy20231 using 1 <;> norm_num
          exact Batch0102.cell0821.sound htau (by
            simp only [Batch0102.cell0821, Batch0102.tau0821, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202310 (by positivity) using 1 <;> norm_num)
        · have hs202312 : InSquare (-51/160) (27/160) (1/160) tau := by
            convert childUL hs20231 hx20231 hy20231 using 1 <;> norm_num
          exact Batch0102.cell0823.sound htau (by
            simp only [Batch0102.cell0823, Batch0102.tau0823, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy20231 | hy20231
        · have hs202311 : InSquare (-49/160) (5/32) (1/160) tau := by
            convert childLR hs20231 hx20231 hy20231 using 1 <;> norm_num
          exact Batch0102.cell0822.sound htau (by
            simp only [Batch0102.cell0822, Batch0102.tau0822, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202311 (by positivity) using 1 <;> norm_num)
        · have hs202313 : InSquare (-49/160) (27/160) (1/160) tau := by
            convert childUR hs20231 hx20231 hy20231 using 1 <;> norm_num
          exact Batch0103.cell0824.sound htau (by
            simp only [Batch0103.cell0824, Batch0103.tau0824, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202313 (by positivity) using 1 <;> norm_num)
    · have hs20233 : InSquare (-5/16) (3/16) (1/80) tau := by
        convert childUR hs hx2023 hy2023 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx20233 | hx20233
      · rcases le_total tau.im (3/16 : ℝ) with hy20233 | hy20233
        · have hs202330 : InSquare (-51/160) (29/160) (1/160) tau := by
            convert childLL hs20233 hx20233 hy20233 using 1 <;> norm_num
          exact Batch0103.cell0829.sound htau (by
            simp only [Batch0103.cell0829, Batch0103.tau0829, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202330 (by positivity) using 1 <;> norm_num)
        · have hs202332 : InSquare (-51/160) (31/160) (1/160) tau := by
            convert childUL hs20233 hx20233 hy20233 using 1 <;> norm_num
          exact Batch0103.cell0831.sound htau (by
            simp only [Batch0103.cell0831, Batch0103.tau0831, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy20233 | hy20233
        · have hs202331 : InSquare (-49/160) (29/160) (1/160) tau := by
            convert childLR hs20233 hx20233 hy20233 using 1 <;> norm_num
          exact Batch0103.cell0830.sound htau (by
            simp only [Batch0103.cell0830, Batch0103.tau0830, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202331 (by positivity) using 1 <;> norm_num)
        · have hs202333 : InSquare (-49/160) (31/160) (1/160) tau := by
            convert childUR hs20233 hx20233 hy20233 using 1 <;> norm_num
          exact Batch0104.cell0832.sound htau (by
            simp only [Batch0104.cell0832, Batch0104.tau0832, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2023

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2030 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2030

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx2030 | hx2030
  · rcases le_total tau.im (1/8 : ℝ) with hy2030 | hy2030
    · have hs20300 : InSquare (-23/80) (9/80) (1/80) tau := by
        convert childLL hs hx2030 hy2030 using 1 <;> norm_num
      exact Batch0027.cell0223.sound htau (by
        simp only [Batch0027.cell0223, Batch0027.tau0223, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20300 (by positivity) using 1 <;> norm_num)
    · have hs20302 : InSquare (-23/80) (11/80) (1/80) tau := by
        convert childUL hs hx2030 hy2030 using 1 <;> norm_num
      exact Batch0028.cell0225.sound htau (by
        simp only [Batch0028.cell0225, Batch0028.tau0225, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20302 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy2030 | hy2030
    · have hs20301 : InSquare (-21/80) (9/80) (1/80) tau := by
        convert childLR hs hx2030 hy2030 using 1 <;> norm_num
      exact Batch0028.cell0224.sound htau (by
        simp only [Batch0028.cell0224, Batch0028.tau0224, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20301 (by positivity) using 1 <;> norm_num)
    · have hs20303 : InSquare (-21/80) (11/80) (1/80) tau := by
        convert childUR hs hx2030 hy2030 using 1 <;> norm_num
      exact Batch0028.cell0226.sound htau (by
        simp only [Batch0028.cell0226, Batch0028.tau0226, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20303 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2030

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2031 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2031

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx2031 | hx2031
  · rcases le_total tau.im (1/8 : ℝ) with hy2031 | hy2031
    · have hs20310 : InSquare (-19/80) (9/80) (1/80) tau := by
        convert childLL hs hx2031 hy2031 using 1 <;> norm_num
      exact Batch0028.cell0227.sound htau (by
        simp only [Batch0028.cell0227, Batch0028.tau0227, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20310 (by positivity) using 1 <;> norm_num)
    · have hs20312 : InSquare (-19/80) (11/80) (1/80) tau := by
        convert childUL hs hx2031 hy2031 using 1 <;> norm_num
      exact Batch0028.cell0229.sound htau (by
        simp only [Batch0028.cell0229, Batch0028.tau0229, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20312 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy2031 | hy2031
    · have hs20311 : InSquare (-17/80) (9/80) (1/80) tau := by
        convert childLR hs hx2031 hy2031 using 1 <;> norm_num
      exact Batch0028.cell0228.sound htau (by
        simp only [Batch0028.cell0228, Batch0028.tau0228, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20311 (by positivity) using 1 <;> norm_num)
    · have hs20313 : InSquare (-17/80) (11/80) (1/80) tau := by
        convert childUR hs hx2031 hy2031 using 1 <;> norm_num
      exact Batch0028.cell0230.sound htau (by
        simp only [Batch0028.cell0230, Batch0028.tau0230, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20313 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2031

end


