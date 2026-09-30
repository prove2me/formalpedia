-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage1330__7
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage1330__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:20:20.877538+00:00
-- url     : https://prove2.me/theorems/0b6b1352-9551-4dbd-a9f5-396b41ef6a81
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1330 (+6 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1331, GeneralCK.Certific…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1330 (+6 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1331, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1332, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1333, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2000, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2001, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2002)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1330 (+6 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1331, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1332, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1333, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2000, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2001, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2002)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1330 (+6 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1331, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1332, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1333, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2000, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2001, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2002) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1330 (+6 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1331, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1332, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1333, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2000, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2001, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2002).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0023
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0094
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0095
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0024
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0096
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0025
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0097
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0098

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1330 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1330

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (-3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx1330 | hx1330
  · rcases le_total tau.im (-3/40 : ℝ) with hy1330 | hy1330
    · have hs13300 : InSquare (5/16) (-7/80) (1/80) tau := by
        convert childLL hs hx1330 hy1330 using 1 <;> norm_num
      exact Batch0023.cell0186.sound htau (by
        simp only [Batch0023.cell0186, Batch0023.tau0186, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13300 (by positivity) using 1 <;> norm_num)
    · have hs13302 : InSquare (5/16) (-1/16) (1/80) tau := by
        convert childUL hs hx1330 hy1330 using 1 <;> norm_num
      exact Batch0023.cell0188.sound htau (by
        simp only [Batch0023.cell0188, Batch0023.tau0188, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13302 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/40 : ℝ) with hy1330 | hy1330
    · have hs13301 : InSquare (27/80) (-7/80) (1/80) tau := by
        convert childLR hs hx1330 hy1330 using 1 <;> norm_num
      exact Batch0023.cell0187.sound htau (by
        simp only [Batch0023.cell0187, Batch0023.tau0187, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13301 (by positivity) using 1 <;> norm_num)
    · have hs13303 : InSquare (27/80) (-1/16) (1/80) tau := by
        convert childUR hs hx1330 hy1330 using 1 <;> norm_num
      exact Batch0023.cell0189.sound htau (by
        simp only [Batch0023.cell0189, Batch0023.tau0189, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13303 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1330

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1331 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1331

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (-3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx1331 | hx1331
  · rcases le_total tau.im (-3/40 : ℝ) with hy1331 | hy1331
    · have hs13310 : InSquare (29/80) (-7/80) (1/80) tau := by
        convert childLL hs hx1331 hy1331 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx13310 | hx13310
      · rcases le_total tau.im (-7/80 : ℝ) with hy13310 | hy13310
        · have hs133100 : InSquare (57/160) (-3/32) (1/160) tau := by
            convert childLL hs13310 hx13310 hy13310 using 1 <;> norm_num
          exact Batch0094.cell0756.sound htau (by
            simp only [Batch0094.cell0756, Batch0094.tau0756, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133100 (by positivity) using 1 <;> norm_num)
        · have hs133102 : InSquare (57/160) (-13/160) (1/160) tau := by
            convert childUL hs13310 hx13310 hy13310 using 1 <;> norm_num
          exact Batch0094.cell0758.sound htau (by
            simp only [Batch0094.cell0758, Batch0094.tau0758, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-7/80 : ℝ) with hy13310 | hy13310
        · have hs133101 : InSquare (59/160) (-3/32) (1/160) tau := by
            convert childLR hs13310 hx13310 hy13310 using 1 <;> norm_num
          exact Batch0094.cell0757.sound htau (by
            simp only [Batch0094.cell0757, Batch0094.tau0757, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133101 (by positivity) using 1 <;> norm_num)
        · have hs133103 : InSquare (59/160) (-13/160) (1/160) tau := by
            convert childUR hs13310 hx13310 hy13310 using 1 <;> norm_num
          exact Batch0094.cell0759.sound htau (by
            simp only [Batch0094.cell0759, Batch0094.tau0759, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133103 (by positivity) using 1 <;> norm_num)
    · have hs13312 : InSquare (29/80) (-1/16) (1/80) tau := by
        convert childUL hs hx1331 hy1331 using 1 <;> norm_num
      exact Batch0023.cell0190.sound htau (by
        simp only [Batch0023.cell0190, Batch0023.tau0190, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13312 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/40 : ℝ) with hy1331 | hy1331
    · have hs13311 : InSquare (31/80) (-7/80) (1/80) tau := by
        convert childLR hs hx1331 hy1331 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx13311 | hx13311
      · rcases le_total tau.im (-7/80 : ℝ) with hy13311 | hy13311
        · have hs133110 : InSquare (61/160) (-3/32) (1/160) tau := by
            convert childLL hs13311 hx13311 hy13311 using 1 <;> norm_num
          exact Batch0095.cell0760.sound htau (by
            simp only [Batch0095.cell0760, Batch0095.tau0760, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133110 (by positivity) using 1 <;> norm_num)
        · have hs133112 : InSquare (61/160) (-13/160) (1/160) tau := by
            convert childUL hs13311 hx13311 hy13311 using 1 <;> norm_num
          exact Batch0095.cell0762.sound htau (by
            simp only [Batch0095.cell0762, Batch0095.tau0762, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-7/80 : ℝ) with hy13311 | hy13311
        · have hs133111 : InSquare (63/160) (-3/32) (1/160) tau := by
            convert childLR hs13311 hx13311 hy13311 using 1 <;> norm_num
          exact Batch0095.cell0761.sound htau (by
            simp only [Batch0095.cell0761, Batch0095.tau0761, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133111 (by positivity) using 1 <;> norm_num)
        · have hs133113 : InSquare (63/160) (-13/160) (1/160) tau := by
            convert childUR hs13311 hx13311 hy13311 using 1 <;> norm_num
          exact Batch0095.cell0763.sound htau (by
            simp only [Batch0095.cell0763, Batch0095.tau0763, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133113 (by positivity) using 1 <;> norm_num)
    · have hs13313 : InSquare (31/80) (-1/16) (1/80) tau := by
        convert childUR hs hx1331 hy1331 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx13313 | hx13313
      · rcases le_total tau.im (-1/16 : ℝ) with hy13313 | hy13313
        · have hs133130 : InSquare (61/160) (-11/160) (1/160) tau := by
            convert childLL hs13313 hx13313 hy13313 using 1 <;> norm_num
          exact Batch0095.cell0764.sound htau (by
            simp only [Batch0095.cell0764, Batch0095.tau0764, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133130 (by positivity) using 1 <;> norm_num)
        · have hs133132 : InSquare (61/160) (-9/160) (1/160) tau := by
            convert childUL hs13313 hx13313 hy13313 using 1 <;> norm_num
          exact Batch0095.cell0766.sound htau (by
            simp only [Batch0095.cell0766, Batch0095.tau0766, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-1/16 : ℝ) with hy13313 | hy13313
        · have hs133131 : InSquare (63/160) (-11/160) (1/160) tau := by
            convert childLR hs13313 hx13313 hy13313 using 1 <;> norm_num
          exact Batch0095.cell0765.sound htau (by
            simp only [Batch0095.cell0765, Batch0095.tau0765, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133131 (by positivity) using 1 <;> norm_num)
        · have hs133133 : InSquare (63/160) (-9/160) (1/160) tau := by
            convert childUR hs13313 hx13313 hy13313 using 1 <;> norm_num
          exact Batch0095.cell0767.sound htau (by
            simp only [Batch0095.cell0767, Batch0095.tau0767, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1331

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1332 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1332

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (-1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx1332 | hx1332
  · rcases le_total tau.im (-1/40 : ℝ) with hy1332 | hy1332
    · have hs13320 : InSquare (5/16) (-3/80) (1/80) tau := by
        convert childLL hs hx1332 hy1332 using 1 <;> norm_num
      exact Batch0023.cell0191.sound htau (by
        simp only [Batch0023.cell0191, Batch0023.tau0191, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13320 (by positivity) using 1 <;> norm_num)
    · have hs13322 : InSquare (5/16) (-1/80) (1/80) tau := by
        convert childUL hs hx1332 hy1332 using 1 <;> norm_num
      exact Batch0024.cell0193.sound htau (by
        simp only [Batch0024.cell0193, Batch0024.tau0193, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13322 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/40 : ℝ) with hy1332 | hy1332
    · have hs13321 : InSquare (27/80) (-3/80) (1/80) tau := by
        convert childLR hs hx1332 hy1332 using 1 <;> norm_num
      exact Batch0024.cell0192.sound htau (by
        simp only [Batch0024.cell0192, Batch0024.tau0192, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13321 (by positivity) using 1 <;> norm_num)
    · have hs13323 : InSquare (27/80) (-1/80) (1/80) tau := by
        convert childUR hs hx1332 hy1332 using 1 <;> norm_num
      exact Batch0024.cell0194.sound htau (by
        simp only [Batch0024.cell0194, Batch0024.tau0194, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13323 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1332

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1333 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1333

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (-1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx1333 | hx1333
  · rcases le_total tau.im (-1/40 : ℝ) with hy1333 | hy1333
    · have hs13330 : InSquare (29/80) (-3/80) (1/80) tau := by
        convert childLL hs hx1333 hy1333 using 1 <;> norm_num
      exact Batch0024.cell0195.sound htau (by
        simp only [Batch0024.cell0195, Batch0024.tau0195, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13330 (by positivity) using 1 <;> norm_num)
    · have hs13332 : InSquare (29/80) (-1/80) (1/80) tau := by
        convert childUL hs hx1333 hy1333 using 1 <;> norm_num
      exact Batch0024.cell0196.sound htau (by
        simp only [Batch0024.cell0196, Batch0024.tau0196, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13332 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/40 : ℝ) with hy1333 | hy1333
    · have hs13331 : InSquare (31/80) (-3/80) (1/80) tau := by
        convert childLR hs hx1333 hy1333 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx13331 | hx13331
      · rcases le_total tau.im (-3/80 : ℝ) with hy13331 | hy13331
        · have hs133310 : InSquare (61/160) (-7/160) (1/160) tau := by
            convert childLL hs13331 hx13331 hy13331 using 1 <;> norm_num
          exact Batch0096.cell0768.sound htau (by
            simp only [Batch0096.cell0768, Batch0096.tau0768, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133310 (by positivity) using 1 <;> norm_num)
        · have hs133312 : InSquare (61/160) (-1/32) (1/160) tau := by
            convert childUL hs13331 hx13331 hy13331 using 1 <;> norm_num
          exact Batch0096.cell0770.sound htau (by
            simp only [Batch0096.cell0770, Batch0096.tau0770, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/80 : ℝ) with hy13331 | hy13331
        · have hs133311 : InSquare (63/160) (-7/160) (1/160) tau := by
            convert childLR hs13331 hx13331 hy13331 using 1 <;> norm_num
          exact Batch0096.cell0769.sound htau (by
            simp only [Batch0096.cell0769, Batch0096.tau0769, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133311 (by positivity) using 1 <;> norm_num)
        · have hs133313 : InSquare (63/160) (-1/32) (1/160) tau := by
            convert childUR hs13331 hx13331 hy13331 using 1 <;> norm_num
          exact Batch0096.cell0771.sound htau (by
            simp only [Batch0096.cell0771, Batch0096.tau0771, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133313 (by positivity) using 1 <;> norm_num)
    · have hs13333 : InSquare (31/80) (-1/80) (1/80) tau := by
        convert childUR hs hx1333 hy1333 using 1 <;> norm_num
      exact Batch0024.cell0197.sound htau (by
        simp only [Batch0024.cell0197, Batch0024.tau0197, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1333

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2000 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2000

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/8 : ℝ) with hx2000 | hx2000
  · rcases le_total tau.im (1/40 : ℝ) with hy2000 | hy2000
    · have hs20000 : InSquare (-31/80) (1/80) (1/80) tau := by
        convert childLL hs hx2000 hy2000 using 1 <;> norm_num
      exact Batch0024.cell0198.sound htau (by
        simp only [Batch0024.cell0198, Batch0024.tau0198, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20000 (by positivity) using 1 <;> norm_num)
    · have hs20002 : InSquare (-31/80) (3/80) (1/80) tau := by
        convert childUL hs hx2000 hy2000 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx20002 | hx20002
      · rcases le_total tau.im (3/80 : ℝ) with hy20002 | hy20002
        · have hs200020 : InSquare (-63/160) (1/32) (1/160) tau := by
            convert childLL hs20002 hx20002 hy20002 using 1 <;> norm_num
          exact Batch0096.cell0772.sound htau (by
            simp only [Batch0096.cell0772, Batch0096.tau0772, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200020 (by positivity) using 1 <;> norm_num)
        · have hs200022 : InSquare (-63/160) (7/160) (1/160) tau := by
            convert childUL hs20002 hx20002 hy20002 using 1 <;> norm_num
          exact Batch0096.cell0774.sound htau (by
            simp only [Batch0096.cell0774, Batch0096.tau0774, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/80 : ℝ) with hy20002 | hy20002
        · have hs200021 : InSquare (-61/160) (1/32) (1/160) tau := by
            convert childLR hs20002 hx20002 hy20002 using 1 <;> norm_num
          exact Batch0096.cell0773.sound htau (by
            simp only [Batch0096.cell0773, Batch0096.tau0773, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200021 (by positivity) using 1 <;> norm_num)
        · have hs200023 : InSquare (-61/160) (7/160) (1/160) tau := by
            convert childUR hs20002 hx20002 hy20002 using 1 <;> norm_num
          exact Batch0096.cell0775.sound htau (by
            simp only [Batch0096.cell0775, Batch0096.tau0775, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/40 : ℝ) with hy2000 | hy2000
    · have hs20001 : InSquare (-29/80) (1/80) (1/80) tau := by
        convert childLR hs hx2000 hy2000 using 1 <;> norm_num
      exact Batch0024.cell0199.sound htau (by
        simp only [Batch0024.cell0199, Batch0024.tau0199, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20001 (by positivity) using 1 <;> norm_num)
    · have hs20003 : InSquare (-29/80) (3/80) (1/80) tau := by
        convert childUR hs hx2000 hy2000 using 1 <;> norm_num
      exact Batch0025.cell0200.sound htau (by
        simp only [Batch0025.cell0200, Batch0025.tau0200, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20003 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2000

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2001 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2001

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx2001 | hx2001
  · rcases le_total tau.im (1/40 : ℝ) with hy2001 | hy2001
    · have hs20010 : InSquare (-27/80) (1/80) (1/80) tau := by
        convert childLL hs hx2001 hy2001 using 1 <;> norm_num
      exact Batch0025.cell0201.sound htau (by
        simp only [Batch0025.cell0201, Batch0025.tau0201, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20010 (by positivity) using 1 <;> norm_num)
    · have hs20012 : InSquare (-27/80) (3/80) (1/80) tau := by
        convert childUL hs hx2001 hy2001 using 1 <;> norm_num
      exact Batch0025.cell0203.sound htau (by
        simp only [Batch0025.cell0203, Batch0025.tau0203, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20012 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/40 : ℝ) with hy2001 | hy2001
    · have hs20011 : InSquare (-5/16) (1/80) (1/80) tau := by
        convert childLR hs hx2001 hy2001 using 1 <;> norm_num
      exact Batch0025.cell0202.sound htau (by
        simp only [Batch0025.cell0202, Batch0025.tau0202, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20011 (by positivity) using 1 <;> norm_num)
    · have hs20013 : InSquare (-5/16) (3/80) (1/80) tau := by
        convert childUR hs hx2001 hy2001 using 1 <;> norm_num
      exact Batch0025.cell0204.sound htau (by
        simp only [Batch0025.cell0204, Batch0025.tau0204, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20013 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2001

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2002 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2002

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/8 : ℝ) with hx2002 | hx2002
  · rcases le_total tau.im (3/40 : ℝ) with hy2002 | hy2002
    · have hs20020 : InSquare (-31/80) (1/16) (1/80) tau := by
        convert childLL hs hx2002 hy2002 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx20020 | hx20020
      · rcases le_total tau.im (1/16 : ℝ) with hy20020 | hy20020
        · have hs200200 : InSquare (-63/160) (9/160) (1/160) tau := by
            convert childLL hs20020 hx20020 hy20020 using 1 <;> norm_num
          exact Batch0097.cell0776.sound htau (by
            simp only [Batch0097.cell0776, Batch0097.tau0776, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200200 (by positivity) using 1 <;> norm_num)
        · have hs200202 : InSquare (-63/160) (11/160) (1/160) tau := by
            convert childUL hs20020 hx20020 hy20020 using 1 <;> norm_num
          exact Batch0097.cell0778.sound htau (by
            simp only [Batch0097.cell0778, Batch0097.tau0778, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (1/16 : ℝ) with hy20020 | hy20020
        · have hs200201 : InSquare (-61/160) (9/160) (1/160) tau := by
            convert childLR hs20020 hx20020 hy20020 using 1 <;> norm_num
          exact Batch0097.cell0777.sound htau (by
            simp only [Batch0097.cell0777, Batch0097.tau0777, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200201 (by positivity) using 1 <;> norm_num)
        · have hs200203 : InSquare (-61/160) (11/160) (1/160) tau := by
            convert childUR hs20020 hx20020 hy20020 using 1 <;> norm_num
          exact Batch0097.cell0779.sound htau (by
            simp only [Batch0097.cell0779, Batch0097.tau0779, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200203 (by positivity) using 1 <;> norm_num)
    · have hs20022 : InSquare (-31/80) (7/80) (1/80) tau := by
        convert childUL hs hx2002 hy2002 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx20022 | hx20022
      · rcases le_total tau.im (7/80 : ℝ) with hy20022 | hy20022
        · have hs200220 : InSquare (-63/160) (13/160) (1/160) tau := by
            convert childLL hs20022 hx20022 hy20022 using 1 <;> norm_num
          exact Batch0097.cell0780.sound htau (by
            simp only [Batch0097.cell0780, Batch0097.tau0780, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200220 (by positivity) using 1 <;> norm_num)
        · have hs200222 : InSquare (-63/160) (3/32) (1/160) tau := by
            convert childUL hs20022 hx20022 hy20022 using 1 <;> norm_num
          exact Batch0097.cell0782.sound htau (by
            simp only [Batch0097.cell0782, Batch0097.tau0782, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (7/80 : ℝ) with hy20022 | hy20022
        · have hs200221 : InSquare (-61/160) (13/160) (1/160) tau := by
            convert childLR hs20022 hx20022 hy20022 using 1 <;> norm_num
          exact Batch0097.cell0781.sound htau (by
            simp only [Batch0097.cell0781, Batch0097.tau0781, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200221 (by positivity) using 1 <;> norm_num)
        · have hs200223 : InSquare (-61/160) (3/32) (1/160) tau := by
            convert childUR hs20022 hx20022 hy20022 using 1 <;> norm_num
          exact Batch0097.cell0783.sound htau (by
            simp only [Batch0097.cell0783, Batch0097.tau0783, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy2002 | hy2002
    · have hs20021 : InSquare (-29/80) (1/16) (1/80) tau := by
        convert childLR hs hx2002 hy2002 using 1 <;> norm_num
      exact Batch0025.cell0205.sound htau (by
        simp only [Batch0025.cell0205, Batch0025.tau0205, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20021 (by positivity) using 1 <;> norm_num)
    · have hs20023 : InSquare (-29/80) (7/80) (1/80) tau := by
        convert childUR hs hx2002 hy2002 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx20023 | hx20023
      · rcases le_total tau.im (7/80 : ℝ) with hy20023 | hy20023
        · have hs200230 : InSquare (-59/160) (13/160) (1/160) tau := by
            convert childLL hs20023 hx20023 hy20023 using 1 <;> norm_num
          exact Batch0098.cell0784.sound htau (by
            simp only [Batch0098.cell0784, Batch0098.tau0784, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200230 (by positivity) using 1 <;> norm_num)
        · have hs200232 : InSquare (-59/160) (3/32) (1/160) tau := by
            convert childUL hs20023 hx20023 hy20023 using 1 <;> norm_num
          exact Batch0098.cell0786.sound htau (by
            simp only [Batch0098.cell0786, Batch0098.tau0786, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (7/80 : ℝ) with hy20023 | hy20023
        · have hs200231 : InSquare (-57/160) (13/160) (1/160) tau := by
            convert childLR hs20023 hx20023 hy20023 using 1 <;> norm_num
          exact Batch0098.cell0785.sound htau (by
            simp only [Batch0098.cell0785, Batch0098.tau0785, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200231 (by positivity) using 1 <;> norm_num)
        · have hs200233 : InSquare (-57/160) (3/32) (1/160) tau := by
            convert childUR hs20023 hx20023 hy20023 using 1 <;> norm_num
          exact Batch0098.cell0787.sound htau (by
            simp only [Batch0098.cell0787, Batch0098.tau0787, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2002

end


