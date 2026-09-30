-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage0031__5
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage0031__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:19:27.794583+00:00
-- url     : https://prove2.me/theorems/43fda55a-ce0c-4b08-8fed-ee0614376973
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0031 (+4 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0032, GeneralCK.Certific…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0031 (+4 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0032, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0033, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0100, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0101)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0031 (+4 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0032, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0033, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0100, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0101)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0031 (+4 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0032, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0033, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0100, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0101) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0031 (+4 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0032, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0033, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0100, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0101).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0044
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0045
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0164
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0165
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0166
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0167
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0046
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0047
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0048
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0049
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0168
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0322
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0323
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0324
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0325
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0326
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0327
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0328
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0169
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0170
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0329
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0330
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0331
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0332
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0333
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0334
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0335
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0336
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0337
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0338
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0339

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0031 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0031

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx0031 | hx0031
  · rcases le_total tau.im (-11/40 : ℝ) with hy0031 | hy0031
    · have hs00310 : InSquare (-19/80) (-23/80) (1/80) tau := by
        convert childLL hs hx0031 hy0031 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx00310 | hx00310
      · rcases le_total tau.im (-23/80 : ℝ) with hy00310 | hy00310
        · have hs003100 : InSquare (-39/160) (-47/160) (1/160) tau := by
            convert childLL hs00310 hx00310 hy00310 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx003100 | hx003100
          · rcases le_total tau.im (-47/160 : ℝ) with hy003100 | hy003100
            · have hs0031000 : InSquare (-79/320) (-19/64) (1/320) tau := by
                convert childLL hs003100 hx003100 hy003100 using 1 <;> norm_num
              exact Batch0164.cell1316.sound htau (by
                simp only [Batch0164.cell1316, Batch0164.tau1316, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031000 (by positivity) using 1 <;> norm_num)
            · have hs0031002 : InSquare (-79/320) (-93/320) (1/320) tau := by
                convert childUL hs003100 hx003100 hy003100 using 1 <;> norm_num
              exact Batch0164.cell1318.sound htau (by
                simp only [Batch0164.cell1318, Batch0164.tau1318, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy003100 | hy003100
            · have hs0031001 : InSquare (-77/320) (-19/64) (1/320) tau := by
                convert childLR hs003100 hx003100 hy003100 using 1 <;> norm_num
              exact Batch0164.cell1317.sound htau (by
                simp only [Batch0164.cell1317, Batch0164.tau1317, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031001 (by positivity) using 1 <;> norm_num)
            · have hs0031003 : InSquare (-77/320) (-93/320) (1/320) tau := by
                convert childUR hs003100 hx003100 hy003100 using 1 <;> norm_num
              exact Batch0164.cell1319.sound htau (by
                simp only [Batch0164.cell1319, Batch0164.tau1319, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031003 (by positivity) using 1 <;> norm_num)
        · have hs003102 : InSquare (-39/160) (-9/32) (1/160) tau := by
            convert childUL hs00310 hx00310 hy00310 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx003102 | hx003102
          · rcases le_total tau.im (-9/32 : ℝ) with hy003102 | hy003102
            · have hs0031020 : InSquare (-79/320) (-91/320) (1/320) tau := by
                convert childLL hs003102 hx003102 hy003102 using 1 <;> norm_num
              exact Batch0165.cell1324.sound htau (by
                simp only [Batch0165.cell1324, Batch0165.tau1324, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031020 (by positivity) using 1 <;> norm_num)
            · have hs0031022 : InSquare (-79/320) (-89/320) (1/320) tau := by
                convert childUL hs003102 hx003102 hy003102 using 1 <;> norm_num
              exact Batch0165.cell1326.sound htau (by
                simp only [Batch0165.cell1326, Batch0165.tau1326, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy003102 | hy003102
            · have hs0031021 : InSquare (-77/320) (-91/320) (1/320) tau := by
                convert childLR hs003102 hx003102 hy003102 using 1 <;> norm_num
              exact Batch0165.cell1325.sound htau (by
                simp only [Batch0165.cell1325, Batch0165.tau1325, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031021 (by positivity) using 1 <;> norm_num)
            · have hs0031023 : InSquare (-77/320) (-89/320) (1/320) tau := by
                convert childUR hs003102 hx003102 hy003102 using 1 <;> norm_num
              exact Batch0165.cell1327.sound htau (by
                simp only [Batch0165.cell1327, Batch0165.tau1327, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy00310 | hy00310
        · have hs003101 : InSquare (-37/160) (-47/160) (1/160) tau := by
            convert childLR hs00310 hx00310 hy00310 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx003101 | hx003101
          · rcases le_total tau.im (-47/160 : ℝ) with hy003101 | hy003101
            · have hs0031010 : InSquare (-15/64) (-19/64) (1/320) tau := by
                convert childLL hs003101 hx003101 hy003101 using 1 <;> norm_num
              exact Batch0165.cell1320.sound htau (by
                simp only [Batch0165.cell1320, Batch0165.tau1320, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031010 (by positivity) using 1 <;> norm_num)
            · have hs0031012 : InSquare (-15/64) (-93/320) (1/320) tau := by
                convert childUL hs003101 hx003101 hy003101 using 1 <;> norm_num
              exact Batch0165.cell1322.sound htau (by
                simp only [Batch0165.cell1322, Batch0165.tau1322, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy003101 | hy003101
            · have hs0031011 : InSquare (-73/320) (-19/64) (1/320) tau := by
                convert childLR hs003101 hx003101 hy003101 using 1 <;> norm_num
              exact Batch0165.cell1321.sound htau (by
                simp only [Batch0165.cell1321, Batch0165.tau1321, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031011 (by positivity) using 1 <;> norm_num)
            · have hs0031013 : InSquare (-73/320) (-93/320) (1/320) tau := by
                convert childUR hs003101 hx003101 hy003101 using 1 <;> norm_num
              exact Batch0165.cell1323.sound htau (by
                simp only [Batch0165.cell1323, Batch0165.tau1323, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031013 (by positivity) using 1 <;> norm_num)
        · have hs003103 : InSquare (-37/160) (-9/32) (1/160) tau := by
            convert childUR hs00310 hx00310 hy00310 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx003103 | hx003103
          · rcases le_total tau.im (-9/32 : ℝ) with hy003103 | hy003103
            · have hs0031030 : InSquare (-15/64) (-91/320) (1/320) tau := by
                convert childLL hs003103 hx003103 hy003103 using 1 <;> norm_num
              exact Batch0166.cell1328.sound htau (by
                simp only [Batch0166.cell1328, Batch0166.tau1328, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031030 (by positivity) using 1 <;> norm_num)
            · have hs0031032 : InSquare (-15/64) (-89/320) (1/320) tau := by
                convert childUL hs003103 hx003103 hy003103 using 1 <;> norm_num
              exact Batch0166.cell1330.sound htau (by
                simp only [Batch0166.cell1330, Batch0166.tau1330, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy003103 | hy003103
            · have hs0031031 : InSquare (-73/320) (-91/320) (1/320) tau := by
                convert childLR hs003103 hx003103 hy003103 using 1 <;> norm_num
              exact Batch0166.cell1329.sound htau (by
                simp only [Batch0166.cell1329, Batch0166.tau1329, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031031 (by positivity) using 1 <;> norm_num)
            · have hs0031033 : InSquare (-73/320) (-89/320) (1/320) tau := by
                convert childUR hs003103 hx003103 hy003103 using 1 <;> norm_num
              exact Batch0166.cell1331.sound htau (by
                simp only [Batch0166.cell1331, Batch0166.tau1331, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031033 (by positivity) using 1 <;> norm_num)
    · have hs00312 : InSquare (-19/80) (-21/80) (1/80) tau := by
        convert childUL hs hx0031 hy0031 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx00312 | hx00312
      · rcases le_total tau.im (-21/80 : ℝ) with hy00312 | hy00312
        · have hs003120 : InSquare (-39/160) (-43/160) (1/160) tau := by
            convert childLL hs00312 hx00312 hy00312 using 1 <;> norm_num
          exact Batch0044.cell0354.sound htau (by
            simp only [Batch0044.cell0354, Batch0044.tau0354, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003120 (by positivity) using 1 <;> norm_num)
        · have hs003122 : InSquare (-39/160) (-41/160) (1/160) tau := by
            convert childUL hs00312 hx00312 hy00312 using 1 <;> norm_num
          exact Batch0044.cell0356.sound htau (by
            simp only [Batch0044.cell0356, Batch0044.tau0356, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy00312 | hy00312
        · have hs003121 : InSquare (-37/160) (-43/160) (1/160) tau := by
            convert childLR hs00312 hx00312 hy00312 using 1 <;> norm_num
          exact Batch0044.cell0355.sound htau (by
            simp only [Batch0044.cell0355, Batch0044.tau0355, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003121 (by positivity) using 1 <;> norm_num)
        · have hs003123 : InSquare (-37/160) (-41/160) (1/160) tau := by
            convert childUR hs00312 hx00312 hy00312 using 1 <;> norm_num
          exact Batch0044.cell0357.sound htau (by
            simp only [Batch0044.cell0357, Batch0044.tau0357, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy0031 | hy0031
    · have hs00311 : InSquare (-17/80) (-23/80) (1/80) tau := by
        convert childLR hs hx0031 hy0031 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx00311 | hx00311
      · rcases le_total tau.im (-23/80 : ℝ) with hy00311 | hy00311
        · have hs003110 : InSquare (-7/32) (-47/160) (1/160) tau := by
            convert childLL hs00311 hx00311 hy00311 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx003110 | hx003110
          · rcases le_total tau.im (-47/160 : ℝ) with hy003110 | hy003110
            · have hs0031100 : InSquare (-71/320) (-19/64) (1/320) tau := by
                convert childLL hs003110 hx003110 hy003110 using 1 <;> norm_num
              exact Batch0166.cell1332.sound htau (by
                simp only [Batch0166.cell1332, Batch0166.tau1332, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031100 (by positivity) using 1 <;> norm_num)
            · have hs0031102 : InSquare (-71/320) (-93/320) (1/320) tau := by
                convert childUL hs003110 hx003110 hy003110 using 1 <;> norm_num
              exact Batch0166.cell1334.sound htau (by
                simp only [Batch0166.cell1334, Batch0166.tau1334, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy003110 | hy003110
            · have hs0031101 : InSquare (-69/320) (-19/64) (1/320) tau := by
                convert childLR hs003110 hx003110 hy003110 using 1 <;> norm_num
              exact Batch0166.cell1333.sound htau (by
                simp only [Batch0166.cell1333, Batch0166.tau1333, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031101 (by positivity) using 1 <;> norm_num)
            · have hs0031103 : InSquare (-69/320) (-93/320) (1/320) tau := by
                convert childUR hs003110 hx003110 hy003110 using 1 <;> norm_num
              exact Batch0166.cell1335.sound htau (by
                simp only [Batch0166.cell1335, Batch0166.tau1335, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031103 (by positivity) using 1 <;> norm_num)
        · have hs003112 : InSquare (-7/32) (-9/32) (1/160) tau := by
            convert childUL hs00311 hx00311 hy00311 using 1 <;> norm_num
          exact Batch0044.cell0352.sound htau (by
            simp only [Batch0044.cell0352, Batch0044.tau0352, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy00311 | hy00311
        · have hs003111 : InSquare (-33/160) (-47/160) (1/160) tau := by
            convert childLR hs00311 hx00311 hy00311 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx003111 | hx003111
          · rcases le_total tau.im (-47/160 : ℝ) with hy003111 | hy003111
            · have hs0031110 : InSquare (-67/320) (-19/64) (1/320) tau := by
                convert childLL hs003111 hx003111 hy003111 using 1 <;> norm_num
              exact Batch0167.cell1336.sound htau (by
                simp only [Batch0167.cell1336, Batch0167.tau1336, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031110 (by positivity) using 1 <;> norm_num)
            · have hs0031112 : InSquare (-67/320) (-93/320) (1/320) tau := by
                convert childUL hs003111 hx003111 hy003111 using 1 <;> norm_num
              exact Batch0167.cell1338.sound htau (by
                simp only [Batch0167.cell1338, Batch0167.tau1338, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy003111 | hy003111
            · have hs0031111 : InSquare (-13/64) (-19/64) (1/320) tau := by
                convert childLR hs003111 hx003111 hy003111 using 1 <;> norm_num
              exact Batch0167.cell1337.sound htau (by
                simp only [Batch0167.cell1337, Batch0167.tau1337, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031111 (by positivity) using 1 <;> norm_num)
            · have hs0031113 : InSquare (-13/64) (-93/320) (1/320) tau := by
                convert childUR hs003111 hx003111 hy003111 using 1 <;> norm_num
              exact Batch0167.cell1339.sound htau (by
                simp only [Batch0167.cell1339, Batch0167.tau1339, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031113 (by positivity) using 1 <;> norm_num)
        · have hs003113 : InSquare (-33/160) (-9/32) (1/160) tau := by
            convert childUR hs00311 hx00311 hy00311 using 1 <;> norm_num
          exact Batch0044.cell0353.sound htau (by
            simp only [Batch0044.cell0353, Batch0044.tau0353, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003113 (by positivity) using 1 <;> norm_num)
    · have hs00313 : InSquare (-17/80) (-21/80) (1/80) tau := by
        convert childUR hs hx0031 hy0031 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx00313 | hx00313
      · rcases le_total tau.im (-21/80 : ℝ) with hy00313 | hy00313
        · have hs003130 : InSquare (-7/32) (-43/160) (1/160) tau := by
            convert childLL hs00313 hx00313 hy00313 using 1 <;> norm_num
          exact Batch0044.cell0358.sound htau (by
            simp only [Batch0044.cell0358, Batch0044.tau0358, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003130 (by positivity) using 1 <;> norm_num)
        · have hs003132 : InSquare (-7/32) (-41/160) (1/160) tau := by
            convert childUL hs00313 hx00313 hy00313 using 1 <;> norm_num
          exact Batch0045.cell0360.sound htau (by
            simp only [Batch0045.cell0360, Batch0045.tau0360, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy00313 | hy00313
        · have hs003131 : InSquare (-33/160) (-43/160) (1/160) tau := by
            convert childLR hs00313 hx00313 hy00313 using 1 <;> norm_num
          exact Batch0044.cell0359.sound htau (by
            simp only [Batch0044.cell0359, Batch0044.tau0359, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003131 (by positivity) using 1 <;> norm_num)
        · have hs003133 : InSquare (-33/160) (-41/160) (1/160) tau := by
            convert childUR hs00313 hx00313 hy00313 using 1 <;> norm_num
          exact Batch0045.cell0361.sound htau (by
            simp only [Batch0045.cell0361, Batch0045.tau0361, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0031

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0032 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0032

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx0032 | hx0032
  · rcases le_total tau.im (-9/40 : ℝ) with hy0032 | hy0032
    · have hs00320 : InSquare (-23/80) (-19/80) (1/80) tau := by
        convert childLL hs hx0032 hy0032 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx00320 | hx00320
      · rcases le_total tau.im (-19/80 : ℝ) with hy00320 | hy00320
        · have hs003200 : InSquare (-47/160) (-39/160) (1/160) tau := by
            convert childLL hs00320 hx00320 hy00320 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx003200 | hx003200
          · rcases le_total tau.im (-39/160 : ℝ) with hy003200 | hy003200
            · have hs0032000 : InSquare (-19/64) (-79/320) (1/320) tau := by
                convert childLL hs003200 hx003200 hy003200 using 1 <;> norm_num
              exact Batch0167.cell1340.sound htau (by
                simp only [Batch0167.cell1340, Batch0167.tau1340, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0032000 (by positivity) using 1 <;> norm_num)
            · have hs0032002 : InSquare (-19/64) (-77/320) (1/320) tau := by
                convert childUL hs003200 hx003200 hy003200 using 1 <;> norm_num
              exact Batch0167.cell1342.sound htau (by
                simp only [Batch0167.cell1342, Batch0167.tau1342, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0032002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-39/160 : ℝ) with hy003200 | hy003200
            · have hs0032001 : InSquare (-93/320) (-79/320) (1/320) tau := by
                convert childLR hs003200 hx003200 hy003200 using 1 <;> norm_num
              exact Batch0167.cell1341.sound htau (by
                simp only [Batch0167.cell1341, Batch0167.tau1341, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0032001 (by positivity) using 1 <;> norm_num)
            · have hs0032003 : InSquare (-93/320) (-77/320) (1/320) tau := by
                convert childUR hs003200 hx003200 hy003200 using 1 <;> norm_num
              exact Batch0167.cell1343.sound htau (by
                simp only [Batch0167.cell1343, Batch0167.tau1343, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0032003 (by positivity) using 1 <;> norm_num)
        · have hs003202 : InSquare (-47/160) (-37/160) (1/160) tau := by
            convert childUL hs00320 hx00320 hy00320 using 1 <;> norm_num
          exact Batch0045.cell0363.sound htau (by
            simp only [Batch0045.cell0363, Batch0045.tau0363, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy00320 | hy00320
        · have hs003201 : InSquare (-9/32) (-39/160) (1/160) tau := by
            convert childLR hs00320 hx00320 hy00320 using 1 <;> norm_num
          exact Batch0045.cell0362.sound htau (by
            simp only [Batch0045.cell0362, Batch0045.tau0362, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003201 (by positivity) using 1 <;> norm_num)
        · have hs003203 : InSquare (-9/32) (-37/160) (1/160) tau := by
            convert childUR hs00320 hx00320 hy00320 using 1 <;> norm_num
          exact Batch0045.cell0364.sound htau (by
            simp only [Batch0045.cell0364, Batch0045.tau0364, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003203 (by positivity) using 1 <;> norm_num)
    · have hs00322 : InSquare (-23/80) (-17/80) (1/80) tau := by
        convert childUL hs hx0032 hy0032 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx00322 | hx00322
      · rcases le_total tau.im (-17/80 : ℝ) with hy00322 | hy00322
        · have hs003220 : InSquare (-47/160) (-7/32) (1/160) tau := by
            convert childLL hs00322 hx00322 hy00322 using 1 <;> norm_num
          exact Batch0046.cell0369.sound htau (by
            simp only [Batch0046.cell0369, Batch0046.tau0369, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003220 (by positivity) using 1 <;> norm_num)
        · have hs003222 : InSquare (-47/160) (-33/160) (1/160) tau := by
            convert childUL hs00322 hx00322 hy00322 using 1 <;> norm_num
          exact Batch0046.cell0371.sound htau (by
            simp only [Batch0046.cell0371, Batch0046.tau0371, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy00322 | hy00322
        · have hs003221 : InSquare (-9/32) (-7/32) (1/160) tau := by
            convert childLR hs00322 hx00322 hy00322 using 1 <;> norm_num
          exact Batch0046.cell0370.sound htau (by
            simp only [Batch0046.cell0370, Batch0046.tau0370, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003221 (by positivity) using 1 <;> norm_num)
        · have hs003223 : InSquare (-9/32) (-33/160) (1/160) tau := by
            convert childUR hs00322 hx00322 hy00322 using 1 <;> norm_num
          exact Batch0046.cell0372.sound htau (by
            simp only [Batch0046.cell0372, Batch0046.tau0372, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy0032 | hy0032
    · have hs00321 : InSquare (-21/80) (-19/80) (1/80) tau := by
        convert childLR hs hx0032 hy0032 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx00321 | hx00321
      · rcases le_total tau.im (-19/80 : ℝ) with hy00321 | hy00321
        · have hs003210 : InSquare (-43/160) (-39/160) (1/160) tau := by
            convert childLL hs00321 hx00321 hy00321 using 1 <;> norm_num
          exact Batch0045.cell0365.sound htau (by
            simp only [Batch0045.cell0365, Batch0045.tau0365, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003210 (by positivity) using 1 <;> norm_num)
        · have hs003212 : InSquare (-43/160) (-37/160) (1/160) tau := by
            convert childUL hs00321 hx00321 hy00321 using 1 <;> norm_num
          exact Batch0045.cell0367.sound htau (by
            simp only [Batch0045.cell0367, Batch0045.tau0367, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy00321 | hy00321
        · have hs003211 : InSquare (-41/160) (-39/160) (1/160) tau := by
            convert childLR hs00321 hx00321 hy00321 using 1 <;> norm_num
          exact Batch0045.cell0366.sound htau (by
            simp only [Batch0045.cell0366, Batch0045.tau0366, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003211 (by positivity) using 1 <;> norm_num)
        · have hs003213 : InSquare (-41/160) (-37/160) (1/160) tau := by
            convert childUR hs00321 hx00321 hy00321 using 1 <;> norm_num
          exact Batch0046.cell0368.sound htau (by
            simp only [Batch0046.cell0368, Batch0046.tau0368, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003213 (by positivity) using 1 <;> norm_num)
    · have hs00323 : InSquare (-21/80) (-17/80) (1/80) tau := by
        convert childUR hs hx0032 hy0032 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx00323 | hx00323
      · rcases le_total tau.im (-17/80 : ℝ) with hy00323 | hy00323
        · have hs003230 : InSquare (-43/160) (-7/32) (1/160) tau := by
            convert childLL hs00323 hx00323 hy00323 using 1 <;> norm_num
          exact Batch0046.cell0373.sound htau (by
            simp only [Batch0046.cell0373, Batch0046.tau0373, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003230 (by positivity) using 1 <;> norm_num)
        · have hs003232 : InSquare (-43/160) (-33/160) (1/160) tau := by
            convert childUL hs00323 hx00323 hy00323 using 1 <;> norm_num
          exact Batch0046.cell0375.sound htau (by
            simp only [Batch0046.cell0375, Batch0046.tau0375, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy00323 | hy00323
        · have hs003231 : InSquare (-41/160) (-7/32) (1/160) tau := by
            convert childLR hs00323 hx00323 hy00323 using 1 <;> norm_num
          exact Batch0046.cell0374.sound htau (by
            simp only [Batch0046.cell0374, Batch0046.tau0374, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003231 (by positivity) using 1 <;> norm_num)
        · have hs003233 : InSquare (-41/160) (-33/160) (1/160) tau := by
            convert childUR hs00323 hx00323 hy00323 using 1 <;> norm_num
          exact Batch0047.cell0376.sound htau (by
            simp only [Batch0047.cell0376, Batch0047.tau0376, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0032

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0033 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0033

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx0033 | hx0033
  · rcases le_total tau.im (-9/40 : ℝ) with hy0033 | hy0033
    · have hs00330 : InSquare (-19/80) (-19/80) (1/80) tau := by
        convert childLL hs hx0033 hy0033 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx00330 | hx00330
      · rcases le_total tau.im (-19/80 : ℝ) with hy00330 | hy00330
        · have hs003300 : InSquare (-39/160) (-39/160) (1/160) tau := by
            convert childLL hs00330 hx00330 hy00330 using 1 <;> norm_num
          exact Batch0047.cell0377.sound htau (by
            simp only [Batch0047.cell0377, Batch0047.tau0377, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003300 (by positivity) using 1 <;> norm_num)
        · have hs003302 : InSquare (-39/160) (-37/160) (1/160) tau := by
            convert childUL hs00330 hx00330 hy00330 using 1 <;> norm_num
          exact Batch0047.cell0379.sound htau (by
            simp only [Batch0047.cell0379, Batch0047.tau0379, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy00330 | hy00330
        · have hs003301 : InSquare (-37/160) (-39/160) (1/160) tau := by
            convert childLR hs00330 hx00330 hy00330 using 1 <;> norm_num
          exact Batch0047.cell0378.sound htau (by
            simp only [Batch0047.cell0378, Batch0047.tau0378, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003301 (by positivity) using 1 <;> norm_num)
        · have hs003303 : InSquare (-37/160) (-37/160) (1/160) tau := by
            convert childUR hs00330 hx00330 hy00330 using 1 <;> norm_num
          exact Batch0047.cell0380.sound htau (by
            simp only [Batch0047.cell0380, Batch0047.tau0380, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003303 (by positivity) using 1 <;> norm_num)
    · have hs00332 : InSquare (-19/80) (-17/80) (1/80) tau := by
        convert childUL hs hx0033 hy0033 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx00332 | hx00332
      · rcases le_total tau.im (-17/80 : ℝ) with hy00332 | hy00332
        · have hs003320 : InSquare (-39/160) (-7/32) (1/160) tau := by
            convert childLL hs00332 hx00332 hy00332 using 1 <;> norm_num
          exact Batch0048.cell0385.sound htau (by
            simp only [Batch0048.cell0385, Batch0048.tau0385, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003320 (by positivity) using 1 <;> norm_num)
        · have hs003322 : InSquare (-39/160) (-33/160) (1/160) tau := by
            convert childUL hs00332 hx00332 hy00332 using 1 <;> norm_num
          exact Batch0048.cell0387.sound htau (by
            simp only [Batch0048.cell0387, Batch0048.tau0387, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy00332 | hy00332
        · have hs003321 : InSquare (-37/160) (-7/32) (1/160) tau := by
            convert childLR hs00332 hx00332 hy00332 using 1 <;> norm_num
          exact Batch0048.cell0386.sound htau (by
            simp only [Batch0048.cell0386, Batch0048.tau0386, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003321 (by positivity) using 1 <;> norm_num)
        · have hs003323 : InSquare (-37/160) (-33/160) (1/160) tau := by
            convert childUR hs00332 hx00332 hy00332 using 1 <;> norm_num
          exact Batch0048.cell0388.sound htau (by
            simp only [Batch0048.cell0388, Batch0048.tau0388, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy0033 | hy0033
    · have hs00331 : InSquare (-17/80) (-19/80) (1/80) tau := by
        convert childLR hs hx0033 hy0033 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx00331 | hx00331
      · rcases le_total tau.im (-19/80 : ℝ) with hy00331 | hy00331
        · have hs003310 : InSquare (-7/32) (-39/160) (1/160) tau := by
            convert childLL hs00331 hx00331 hy00331 using 1 <;> norm_num
          exact Batch0047.cell0381.sound htau (by
            simp only [Batch0047.cell0381, Batch0047.tau0381, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003310 (by positivity) using 1 <;> norm_num)
        · have hs003312 : InSquare (-7/32) (-37/160) (1/160) tau := by
            convert childUL hs00331 hx00331 hy00331 using 1 <;> norm_num
          exact Batch0047.cell0383.sound htau (by
            simp only [Batch0047.cell0383, Batch0047.tau0383, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy00331 | hy00331
        · have hs003311 : InSquare (-33/160) (-39/160) (1/160) tau := by
            convert childLR hs00331 hx00331 hy00331 using 1 <;> norm_num
          exact Batch0047.cell0382.sound htau (by
            simp only [Batch0047.cell0382, Batch0047.tau0382, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003311 (by positivity) using 1 <;> norm_num)
        · have hs003313 : InSquare (-33/160) (-37/160) (1/160) tau := by
            convert childUR hs00331 hx00331 hy00331 using 1 <;> norm_num
          exact Batch0048.cell0384.sound htau (by
            simp only [Batch0048.cell0384, Batch0048.tau0384, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003313 (by positivity) using 1 <;> norm_num)
    · have hs00333 : InSquare (-17/80) (-17/80) (1/80) tau := by
        convert childUR hs hx0033 hy0033 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx00333 | hx00333
      · rcases le_total tau.im (-17/80 : ℝ) with hy00333 | hy00333
        · have hs003330 : InSquare (-7/32) (-7/32) (1/160) tau := by
            convert childLL hs00333 hx00333 hy00333 using 1 <;> norm_num
          exact Batch0048.cell0389.sound htau (by
            simp only [Batch0048.cell0389, Batch0048.tau0389, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003330 (by positivity) using 1 <;> norm_num)
        · have hs003332 : InSquare (-7/32) (-33/160) (1/160) tau := by
            convert childUL hs00333 hx00333 hy00333 using 1 <;> norm_num
          exact Batch0048.cell0391.sound htau (by
            simp only [Batch0048.cell0391, Batch0048.tau0391, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy00333 | hy00333
        · have hs003331 : InSquare (-33/160) (-7/32) (1/160) tau := by
            convert childLR hs00333 hx00333 hy00333 using 1 <;> norm_num
          exact Batch0048.cell0390.sound htau (by
            simp only [Batch0048.cell0390, Batch0048.tau0390, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003331 (by positivity) using 1 <;> norm_num)
        · have hs003333 : InSquare (-33/160) (-33/160) (1/160) tau := by
            convert childUR hs00333 hx00333 hy00333 using 1 <;> norm_num
          exact Batch0049.cell0392.sound htau (by
            simp only [Batch0049.cell0392, Batch0049.tau0392, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0033

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0100 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0100

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_01000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/16) (-31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/40)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/80) (-31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/20)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_010020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/160) (-59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/16)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_010021 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-29/160) (-59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/40)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0100220 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/320) (-23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/160)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0100221 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-61/320) (-23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/16)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0100222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/320) (-113/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/160)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0100300 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/64) (-119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/160)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0100301 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-53/320) (-119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/80)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0100310 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-51/320) (-119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+5/32)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01002230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-123/640) (-227/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (61/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+61/320)]
  have himSq : (113/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+113/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01002300 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-119/640) (-231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+59/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01002301 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-117/640) (-231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/160)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01002302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-119/640) (-229/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+59/320)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01002310 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/128) (-231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+57/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01003020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/640) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/64)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01003021 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-109/640) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/160)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01003022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/640) (-233/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/64)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01003030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-107/640) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+53/320)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01003031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-21/128) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/80)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01003110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-99/640) (-239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+49/320)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01003111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-97/640) (-239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/20)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (-3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx0100 | hx0100
  · rcases le_total tau.im (-3/8 : ℝ) with hy0100 | hy0100
    · have hs01000 : InSquare (-3/16) (-31/80) (1/80) tau := by
        convert childLL hs hx0100 hy0100 using 1 <;> norm_num
      exact (outside_01000 htau hs01000).elim
    · have hs01002 : InSquare (-3/16) (-29/80) (1/80) tau := by
        convert childUL hs hx0100 hy0100 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx01002 | hx01002
      · rcases le_total tau.im (-29/80 : ℝ) with hy01002 | hy01002
        · have hs010020 : InSquare (-31/160) (-59/160) (1/160) tau := by
            convert childLL hs01002 hx01002 hy01002 using 1 <;> norm_num
          exact (outside_010020 htau hs010020).elim
        · have hs010022 : InSquare (-31/160) (-57/160) (1/160) tau := by
            convert childUL hs01002 hx01002 hy01002 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx010022 | hx010022
          · rcases le_total tau.im (-57/160 : ℝ) with hy010022 | hy010022
            · have hs0100220 : InSquare (-63/320) (-23/64) (1/320) tau := by
                convert childLL hs010022 hx010022 hy010022 using 1 <;> norm_num
              exact (outside_0100220 htau hs0100220).elim
            · have hs0100222 : InSquare (-63/320) (-113/320) (1/320) tau := by
                convert childUL hs010022 hx010022 hy010022 using 1 <;> norm_num
              exact (outside_0100222 htau hs0100222).elim
          · rcases le_total tau.im (-57/160 : ℝ) with hy010022 | hy010022
            · have hs0100221 : InSquare (-61/320) (-23/64) (1/320) tau := by
                convert childLR hs010022 hx010022 hy010022 using 1 <;> norm_num
              exact (outside_0100221 htau hs0100221).elim
            · have hs0100223 : InSquare (-61/320) (-113/320) (1/320) tau := by
                convert childUR hs010022 hx010022 hy010022 using 1 <;> norm_num
              rcases le_total tau.re (-61/320 : ℝ) with hx0100223 | hx0100223
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100223 | hy0100223
                · have hs01002230 : InSquare (-123/640) (-227/640) (1/640) tau := by
                    convert childLL hs0100223 hx0100223 hy0100223 using 1 <;> norm_num
                  exact (outside_01002230 htau hs01002230).elim
                · have hs01002232 : InSquare (-123/640) (-45/128) (1/640) tau := by
                    convert childUL hs0100223 hx0100223 hy0100223 using 1 <;> norm_num
                  exact Batch0322.cell2580.sound htau (by
                    simp only [Batch0322.cell2580, Batch0322.tau2580, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100223 | hy0100223
                · have hs01002231 : InSquare (-121/640) (-227/640) (1/640) tau := by
                    convert childLR hs0100223 hx0100223 hy0100223 using 1 <;> norm_num
                  exact Batch0322.cell2579.sound htau (by
                    simp only [Batch0322.cell2579, Batch0322.tau2579, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002231 (by positivity) using 1 <;> norm_num)
                · have hs01002233 : InSquare (-121/640) (-45/128) (1/640) tau := by
                    convert childUR hs0100223 hx0100223 hy0100223 using 1 <;> norm_num
                  exact Batch0322.cell2581.sound htau (by
                    simp only [Batch0322.cell2581, Batch0322.tau2581, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01002 | hy01002
        · have hs010021 : InSquare (-29/160) (-59/160) (1/160) tau := by
            convert childLR hs01002 hx01002 hy01002 using 1 <;> norm_num
          exact (outside_010021 htau hs010021).elim
        · have hs010023 : InSquare (-29/160) (-57/160) (1/160) tau := by
            convert childUR hs01002 hx01002 hy01002 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx010023 | hx010023
          · rcases le_total tau.im (-57/160 : ℝ) with hy010023 | hy010023
            · have hs0100230 : InSquare (-59/320) (-23/64) (1/320) tau := by
                convert childLL hs010023 hx010023 hy010023 using 1 <;> norm_num
              rcases le_total tau.re (-59/320 : ℝ) with hx0100230 | hx0100230
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100230 | hy0100230
                · have hs01002300 : InSquare (-119/640) (-231/640) (1/640) tau := by
                    convert childLL hs0100230 hx0100230 hy0100230 using 1 <;> norm_num
                  exact (outside_01002300 htau hs01002300).elim
                · have hs01002302 : InSquare (-119/640) (-229/640) (1/640) tau := by
                    convert childUL hs0100230 hx0100230 hy0100230 using 1 <;> norm_num
                  exact (outside_01002302 htau hs01002302).elim
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100230 | hy0100230
                · have hs01002301 : InSquare (-117/640) (-231/640) (1/640) tau := by
                    convert childLR hs0100230 hx0100230 hy0100230 using 1 <;> norm_num
                  exact (outside_01002301 htau hs01002301).elim
                · have hs01002303 : InSquare (-117/640) (-229/640) (1/640) tau := by
                    convert childUR hs0100230 hx0100230 hy0100230 using 1 <;> norm_num
                  exact Batch0322.cell2582.sound htau (by
                    simp only [Batch0322.cell2582, Batch0322.tau2582, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002303 (by positivity) using 1 <;> norm_num)
            · have hs0100232 : InSquare (-59/320) (-113/320) (1/320) tau := by
                convert childUL hs010023 hx010023 hy010023 using 1 <;> norm_num
              rcases le_total tau.re (-59/320 : ℝ) with hx0100232 | hx0100232
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100232 | hy0100232
                · have hs01002320 : InSquare (-119/640) (-227/640) (1/640) tau := by
                    convert childLL hs0100232 hx0100232 hy0100232 using 1 <;> norm_num
                  exact Batch0323.cell2586.sound htau (by
                    simp only [Batch0323.cell2586, Batch0323.tau2586, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002320 (by positivity) using 1 <;> norm_num)
                · have hs01002322 : InSquare (-119/640) (-45/128) (1/640) tau := by
                    convert childUL hs0100232 hx0100232 hy0100232 using 1 <;> norm_num
                  exact Batch0323.cell2588.sound htau (by
                    simp only [Batch0323.cell2588, Batch0323.tau2588, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100232 | hy0100232
                · have hs01002321 : InSquare (-117/640) (-227/640) (1/640) tau := by
                    convert childLR hs0100232 hx0100232 hy0100232 using 1 <;> norm_num
                  exact Batch0323.cell2587.sound htau (by
                    simp only [Batch0323.cell2587, Batch0323.tau2587, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002321 (by positivity) using 1 <;> norm_num)
                · have hs01002323 : InSquare (-117/640) (-45/128) (1/640) tau := by
                    convert childUR hs0100232 hx0100232 hy0100232 using 1 <;> norm_num
                  exact Batch0323.cell2589.sound htau (by
                    simp only [Batch0323.cell2589, Batch0323.tau2589, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy010023 | hy010023
            · have hs0100231 : InSquare (-57/320) (-23/64) (1/320) tau := by
                convert childLR hs010023 hx010023 hy010023 using 1 <;> norm_num
              rcases le_total tau.re (-57/320 : ℝ) with hx0100231 | hx0100231
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100231 | hy0100231
                · have hs01002310 : InSquare (-23/128) (-231/640) (1/640) tau := by
                    convert childLL hs0100231 hx0100231 hy0100231 using 1 <;> norm_num
                  exact (outside_01002310 htau hs01002310).elim
                · have hs01002312 : InSquare (-23/128) (-229/640) (1/640) tau := by
                    convert childUL hs0100231 hx0100231 hy0100231 using 1 <;> norm_num
                  exact Batch0323.cell2584.sound htau (by
                    simp only [Batch0323.cell2584, Batch0323.tau2584, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100231 | hy0100231
                · have hs01002311 : InSquare (-113/640) (-231/640) (1/640) tau := by
                    convert childLR hs0100231 hx0100231 hy0100231 using 1 <;> norm_num
                  exact Batch0322.cell2583.sound htau (by
                    simp only [Batch0322.cell2583, Batch0322.tau2583, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002311 (by positivity) using 1 <;> norm_num)
                · have hs01002313 : InSquare (-113/640) (-229/640) (1/640) tau := by
                    convert childUR hs0100231 hx0100231 hy0100231 using 1 <;> norm_num
                  exact Batch0323.cell2585.sound htau (by
                    simp only [Batch0323.cell2585, Batch0323.tau2585, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002313 (by positivity) using 1 <;> norm_num)
            · have hs0100233 : InSquare (-57/320) (-113/320) (1/320) tau := by
                convert childUR hs010023 hx010023 hy010023 using 1 <;> norm_num
              rcases le_total tau.re (-57/320 : ℝ) with hx0100233 | hx0100233
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100233 | hy0100233
                · have hs01002330 : InSquare (-23/128) (-227/640) (1/640) tau := by
                    convert childLL hs0100233 hx0100233 hy0100233 using 1 <;> norm_num
                  exact Batch0323.cell2590.sound htau (by
                    simp only [Batch0323.cell2590, Batch0323.tau2590, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002330 (by positivity) using 1 <;> norm_num)
                · have hs01002332 : InSquare (-23/128) (-45/128) (1/640) tau := by
                    convert childUL hs0100233 hx0100233 hy0100233 using 1 <;> norm_num
                  exact Batch0324.cell2592.sound htau (by
                    simp only [Batch0324.cell2592, Batch0324.tau2592, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100233 | hy0100233
                · have hs01002331 : InSquare (-113/640) (-227/640) (1/640) tau := by
                    convert childLR hs0100233 hx0100233 hy0100233 using 1 <;> norm_num
                  exact Batch0323.cell2591.sound htau (by
                    simp only [Batch0323.cell2591, Batch0323.tau2591, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002331 (by positivity) using 1 <;> norm_num)
                · have hs01002333 : InSquare (-113/640) (-45/128) (1/640) tau := by
                    convert childUR hs0100233 hx0100233 hy0100233 using 1 <;> norm_num
                  exact Batch0324.cell2593.sound htau (by
                    simp only [Batch0324.cell2593, Batch0324.tau2593, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002333 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/8 : ℝ) with hy0100 | hy0100
    · have hs01001 : InSquare (-13/80) (-31/80) (1/80) tau := by
        convert childLR hs hx0100 hy0100 using 1 <;> norm_num
      exact (outside_01001 htau hs01001).elim
    · have hs01003 : InSquare (-13/80) (-29/80) (1/80) tau := by
        convert childUR hs hx0100 hy0100 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx01003 | hx01003
      · rcases le_total tau.im (-29/80 : ℝ) with hy01003 | hy01003
        · have hs010030 : InSquare (-27/160) (-59/160) (1/160) tau := by
            convert childLL hs01003 hx01003 hy01003 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx010030 | hx010030
          · rcases le_total tau.im (-59/160 : ℝ) with hy010030 | hy010030
            · have hs0100300 : InSquare (-11/64) (-119/320) (1/320) tau := by
                convert childLL hs010030 hx010030 hy010030 using 1 <;> norm_num
              exact (outside_0100300 htau hs0100300).elim
            · have hs0100302 : InSquare (-11/64) (-117/320) (1/320) tau := by
                convert childUL hs010030 hx010030 hy010030 using 1 <;> norm_num
              rcases le_total tau.re (-11/64 : ℝ) with hx0100302 | hx0100302
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100302 | hy0100302
                · have hs01003020 : InSquare (-111/640) (-47/128) (1/640) tau := by
                    convert childLL hs0100302 hx0100302 hy0100302 using 1 <;> norm_num
                  exact (outside_01003020 htau hs01003020).elim
                · have hs01003022 : InSquare (-111/640) (-233/640) (1/640) tau := by
                    convert childUL hs0100302 hx0100302 hy0100302 using 1 <;> norm_num
                  exact (outside_01003022 htau hs01003022).elim
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100302 | hy0100302
                · have hs01003021 : InSquare (-109/640) (-47/128) (1/640) tau := by
                    convert childLR hs0100302 hx0100302 hy0100302 using 1 <;> norm_num
                  exact (outside_01003021 htau hs01003021).elim
                · have hs01003023 : InSquare (-109/640) (-233/640) (1/640) tau := by
                    convert childUR hs0100302 hx0100302 hy0100302 using 1 <;> norm_num
                  exact Batch0324.cell2594.sound htau (by
                    simp only [Batch0324.cell2594, Batch0324.tau2594, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy010030 | hy010030
            · have hs0100301 : InSquare (-53/320) (-119/320) (1/320) tau := by
                convert childLR hs010030 hx010030 hy010030 using 1 <;> norm_num
              exact (outside_0100301 htau hs0100301).elim
            · have hs0100303 : InSquare (-53/320) (-117/320) (1/320) tau := by
                convert childUR hs010030 hx010030 hy010030 using 1 <;> norm_num
              rcases le_total tau.re (-53/320 : ℝ) with hx0100303 | hx0100303
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100303 | hy0100303
                · have hs01003030 : InSquare (-107/640) (-47/128) (1/640) tau := by
                    convert childLL hs0100303 hx0100303 hy0100303 using 1 <;> norm_num
                  exact (outside_01003030 htau hs01003030).elim
                · have hs01003032 : InSquare (-107/640) (-233/640) (1/640) tau := by
                    convert childUL hs0100303 hx0100303 hy0100303 using 1 <;> norm_num
                  exact Batch0324.cell2595.sound htau (by
                    simp only [Batch0324.cell2595, Batch0324.tau2595, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100303 | hy0100303
                · have hs01003031 : InSquare (-21/128) (-47/128) (1/640) tau := by
                    convert childLR hs0100303 hx0100303 hy0100303 using 1 <;> norm_num
                  exact (outside_01003031 htau hs01003031).elim
                · have hs01003033 : InSquare (-21/128) (-233/640) (1/640) tau := by
                    convert childUR hs0100303 hx0100303 hy0100303 using 1 <;> norm_num
                  exact Batch0324.cell2596.sound htau (by
                    simp only [Batch0324.cell2596, Batch0324.tau2596, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003033 (by positivity) using 1 <;> norm_num)
        · have hs010032 : InSquare (-27/160) (-57/160) (1/160) tau := by
            convert childUL hs01003 hx01003 hy01003 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx010032 | hx010032
          · rcases le_total tau.im (-57/160 : ℝ) with hy010032 | hy010032
            · have hs0100320 : InSquare (-11/64) (-23/64) (1/320) tau := by
                convert childLL hs010032 hx010032 hy010032 using 1 <;> norm_num
              rcases le_total tau.re (-11/64 : ℝ) with hx0100320 | hx0100320
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100320 | hy0100320
                · have hs01003200 : InSquare (-111/640) (-231/640) (1/640) tau := by
                    convert childLL hs0100320 hx0100320 hy0100320 using 1 <;> norm_num
                  exact Batch0325.cell2607.sound htau (by
                    simp only [Batch0325.cell2607, Batch0325.tau2607, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003200 (by positivity) using 1 <;> norm_num)
                · have hs01003202 : InSquare (-111/640) (-229/640) (1/640) tau := by
                    convert childUL hs0100320 hx0100320 hy0100320 using 1 <;> norm_num
                  exact Batch0326.cell2609.sound htau (by
                    simp only [Batch0326.cell2609, Batch0326.tau2609, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100320 | hy0100320
                · have hs01003201 : InSquare (-109/640) (-231/640) (1/640) tau := by
                    convert childLR hs0100320 hx0100320 hy0100320 using 1 <;> norm_num
                  exact Batch0326.cell2608.sound htau (by
                    simp only [Batch0326.cell2608, Batch0326.tau2608, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003201 (by positivity) using 1 <;> norm_num)
                · have hs01003203 : InSquare (-109/640) (-229/640) (1/640) tau := by
                    convert childUR hs0100320 hx0100320 hy0100320 using 1 <;> norm_num
                  exact Batch0326.cell2610.sound htau (by
                    simp only [Batch0326.cell2610, Batch0326.tau2610, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003203 (by positivity) using 1 <;> norm_num)
            · have hs0100322 : InSquare (-11/64) (-113/320) (1/320) tau := by
                convert childUL hs010032 hx010032 hy010032 using 1 <;> norm_num
              rcases le_total tau.re (-11/64 : ℝ) with hx0100322 | hx0100322
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100322 | hy0100322
                · have hs01003220 : InSquare (-111/640) (-227/640) (1/640) tau := by
                    convert childLL hs0100322 hx0100322 hy0100322 using 1 <;> norm_num
                  exact Batch0326.cell2615.sound htau (by
                    simp only [Batch0326.cell2615, Batch0326.tau2615, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003220 (by positivity) using 1 <;> norm_num)
                · have hs01003222 : InSquare (-111/640) (-45/128) (1/640) tau := by
                    convert childUL hs0100322 hx0100322 hy0100322 using 1 <;> norm_num
                  exact Batch0327.cell2617.sound htau (by
                    simp only [Batch0327.cell2617, Batch0327.tau2617, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100322 | hy0100322
                · have hs01003221 : InSquare (-109/640) (-227/640) (1/640) tau := by
                    convert childLR hs0100322 hx0100322 hy0100322 using 1 <;> norm_num
                  exact Batch0327.cell2616.sound htau (by
                    simp only [Batch0327.cell2616, Batch0327.tau2616, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003221 (by positivity) using 1 <;> norm_num)
                · have hs01003223 : InSquare (-109/640) (-45/128) (1/640) tau := by
                    convert childUR hs0100322 hx0100322 hy0100322 using 1 <;> norm_num
                  exact Batch0327.cell2618.sound htau (by
                    simp only [Batch0327.cell2618, Batch0327.tau2618, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy010032 | hy010032
            · have hs0100321 : InSquare (-53/320) (-23/64) (1/320) tau := by
                convert childLR hs010032 hx010032 hy010032 using 1 <;> norm_num
              rcases le_total tau.re (-53/320 : ℝ) with hx0100321 | hx0100321
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100321 | hy0100321
                · have hs01003210 : InSquare (-107/640) (-231/640) (1/640) tau := by
                    convert childLL hs0100321 hx0100321 hy0100321 using 1 <;> norm_num
                  exact Batch0326.cell2611.sound htau (by
                    simp only [Batch0326.cell2611, Batch0326.tau2611, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003210 (by positivity) using 1 <;> norm_num)
                · have hs01003212 : InSquare (-107/640) (-229/640) (1/640) tau := by
                    convert childUL hs0100321 hx0100321 hy0100321 using 1 <;> norm_num
                  exact Batch0326.cell2613.sound htau (by
                    simp only [Batch0326.cell2613, Batch0326.tau2613, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100321 | hy0100321
                · have hs01003211 : InSquare (-21/128) (-231/640) (1/640) tau := by
                    convert childLR hs0100321 hx0100321 hy0100321 using 1 <;> norm_num
                  exact Batch0326.cell2612.sound htau (by
                    simp only [Batch0326.cell2612, Batch0326.tau2612, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003211 (by positivity) using 1 <;> norm_num)
                · have hs01003213 : InSquare (-21/128) (-229/640) (1/640) tau := by
                    convert childUR hs0100321 hx0100321 hy0100321 using 1 <;> norm_num
                  exact Batch0326.cell2614.sound htau (by
                    simp only [Batch0326.cell2614, Batch0326.tau2614, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003213 (by positivity) using 1 <;> norm_num)
            · have hs0100323 : InSquare (-53/320) (-113/320) (1/320) tau := by
                convert childUR hs010032 hx010032 hy010032 using 1 <;> norm_num
              exact Batch0168.cell1344.sound htau (by
                simp only [Batch0168.cell1344, Batch0168.tau1344, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0100323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01003 | hy01003
        · have hs010031 : InSquare (-5/32) (-59/160) (1/160) tau := by
            convert childLR hs01003 hx01003 hy01003 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx010031 | hx010031
          · rcases le_total tau.im (-59/160 : ℝ) with hy010031 | hy010031
            · have hs0100310 : InSquare (-51/320) (-119/320) (1/320) tau := by
                convert childLL hs010031 hx010031 hy010031 using 1 <;> norm_num
              exact (outside_0100310 htau hs0100310).elim
            · have hs0100312 : InSquare (-51/320) (-117/320) (1/320) tau := by
                convert childUL hs010031 hx010031 hy010031 using 1 <;> norm_num
              rcases le_total tau.re (-51/320 : ℝ) with hx0100312 | hx0100312
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100312 | hy0100312
                · have hs01003120 : InSquare (-103/640) (-47/128) (1/640) tau := by
                    convert childLL hs0100312 hx0100312 hy0100312 using 1 <;> norm_num
                  exact Batch0324.cell2599.sound htau (by
                    simp only [Batch0324.cell2599, Batch0324.tau2599, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003120 (by positivity) using 1 <;> norm_num)
                · have hs01003122 : InSquare (-103/640) (-233/640) (1/640) tau := by
                    convert childUL hs0100312 hx0100312 hy0100312 using 1 <;> norm_num
                  exact Batch0325.cell2601.sound htau (by
                    simp only [Batch0325.cell2601, Batch0325.tau2601, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100312 | hy0100312
                · have hs01003121 : InSquare (-101/640) (-47/128) (1/640) tau := by
                    convert childLR hs0100312 hx0100312 hy0100312 using 1 <;> norm_num
                  exact Batch0325.cell2600.sound htau (by
                    simp only [Batch0325.cell2600, Batch0325.tau2600, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003121 (by positivity) using 1 <;> norm_num)
                · have hs01003123 : InSquare (-101/640) (-233/640) (1/640) tau := by
                    convert childUR hs0100312 hx0100312 hy0100312 using 1 <;> norm_num
                  exact Batch0325.cell2602.sound htau (by
                    simp only [Batch0325.cell2602, Batch0325.tau2602, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy010031 | hy010031
            · have hs0100311 : InSquare (-49/320) (-119/320) (1/320) tau := by
                convert childLR hs010031 hx010031 hy010031 using 1 <;> norm_num
              rcases le_total tau.re (-49/320 : ℝ) with hx0100311 | hx0100311
              · rcases le_total tau.im (-119/320 : ℝ) with hy0100311 | hy0100311
                · have hs01003110 : InSquare (-99/640) (-239/640) (1/640) tau := by
                    convert childLL hs0100311 hx0100311 hy0100311 using 1 <;> norm_num
                  exact (outside_01003110 htau hs01003110).elim
                · have hs01003112 : InSquare (-99/640) (-237/640) (1/640) tau := by
                    convert childUL hs0100311 hx0100311 hy0100311 using 1 <;> norm_num
                  exact Batch0324.cell2597.sound htau (by
                    simp only [Batch0324.cell2597, Batch0324.tau2597, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0100311 | hy0100311
                · have hs01003111 : InSquare (-97/640) (-239/640) (1/640) tau := by
                    convert childLR hs0100311 hx0100311 hy0100311 using 1 <;> norm_num
                  exact (outside_01003111 htau hs01003111).elim
                · have hs01003113 : InSquare (-97/640) (-237/640) (1/640) tau := by
                    convert childUR hs0100311 hx0100311 hy0100311 using 1 <;> norm_num
                  exact Batch0324.cell2598.sound htau (by
                    simp only [Batch0324.cell2598, Batch0324.tau2598, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003113 (by positivity) using 1 <;> norm_num)
            · have hs0100313 : InSquare (-49/320) (-117/320) (1/320) tau := by
                convert childUR hs010031 hx010031 hy010031 using 1 <;> norm_num
              rcases le_total tau.re (-49/320 : ℝ) with hx0100313 | hx0100313
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100313 | hy0100313
                · have hs01003130 : InSquare (-99/640) (-47/128) (1/640) tau := by
                    convert childLL hs0100313 hx0100313 hy0100313 using 1 <;> norm_num
                  exact Batch0325.cell2603.sound htau (by
                    simp only [Batch0325.cell2603, Batch0325.tau2603, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003130 (by positivity) using 1 <;> norm_num)
                · have hs01003132 : InSquare (-99/640) (-233/640) (1/640) tau := by
                    convert childUL hs0100313 hx0100313 hy0100313 using 1 <;> norm_num
                  exact Batch0325.cell2605.sound htau (by
                    simp only [Batch0325.cell2605, Batch0325.tau2605, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100313 | hy0100313
                · have hs01003131 : InSquare (-97/640) (-47/128) (1/640) tau := by
                    convert childLR hs0100313 hx0100313 hy0100313 using 1 <;> norm_num
                  exact Batch0325.cell2604.sound htau (by
                    simp only [Batch0325.cell2604, Batch0325.tau2604, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003131 (by positivity) using 1 <;> norm_num)
                · have hs01003133 : InSquare (-97/640) (-233/640) (1/640) tau := by
                    convert childUR hs0100313 hx0100313 hy0100313 using 1 <;> norm_num
                  exact Batch0325.cell2606.sound htau (by
                    simp only [Batch0325.cell2606, Batch0325.tau2606, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003133 (by positivity) using 1 <;> norm_num)
        · have hs010033 : InSquare (-5/32) (-57/160) (1/160) tau := by
            convert childUR hs01003 hx01003 hy01003 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx010033 | hx010033
          · rcases le_total tau.im (-57/160 : ℝ) with hy010033 | hy010033
            · have hs0100330 : InSquare (-51/320) (-23/64) (1/320) tau := by
                convert childLL hs010033 hx010033 hy010033 using 1 <;> norm_num
              rcases le_total tau.re (-51/320 : ℝ) with hx0100330 | hx0100330
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100330 | hy0100330
                · have hs01003300 : InSquare (-103/640) (-231/640) (1/640) tau := by
                    convert childLL hs0100330 hx0100330 hy0100330 using 1 <;> norm_num
                  exact Batch0327.cell2619.sound htau (by
                    simp only [Batch0327.cell2619, Batch0327.tau2619, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003300 (by positivity) using 1 <;> norm_num)
                · have hs01003302 : InSquare (-103/640) (-229/640) (1/640) tau := by
                    convert childUL hs0100330 hx0100330 hy0100330 using 1 <;> norm_num
                  exact Batch0327.cell2621.sound htau (by
                    simp only [Batch0327.cell2621, Batch0327.tau2621, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100330 | hy0100330
                · have hs01003301 : InSquare (-101/640) (-231/640) (1/640) tau := by
                    convert childLR hs0100330 hx0100330 hy0100330 using 1 <;> norm_num
                  exact Batch0327.cell2620.sound htau (by
                    simp only [Batch0327.cell2620, Batch0327.tau2620, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003301 (by positivity) using 1 <;> norm_num)
                · have hs01003303 : InSquare (-101/640) (-229/640) (1/640) tau := by
                    convert childUR hs0100330 hx0100330 hy0100330 using 1 <;> norm_num
                  exact Batch0327.cell2622.sound htau (by
                    simp only [Batch0327.cell2622, Batch0327.tau2622, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003303 (by positivity) using 1 <;> norm_num)
            · have hs0100332 : InSquare (-51/320) (-113/320) (1/320) tau := by
                convert childUL hs010033 hx010033 hy010033 using 1 <;> norm_num
              exact Batch0168.cell1345.sound htau (by
                simp only [Batch0168.cell1345, Batch0168.tau1345, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0100332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy010033 | hy010033
            · have hs0100331 : InSquare (-49/320) (-23/64) (1/320) tau := by
                convert childLR hs010033 hx010033 hy010033 using 1 <;> norm_num
              rcases le_total tau.re (-49/320 : ℝ) with hx0100331 | hx0100331
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100331 | hy0100331
                · have hs01003310 : InSquare (-99/640) (-231/640) (1/640) tau := by
                    convert childLL hs0100331 hx0100331 hy0100331 using 1 <;> norm_num
                  exact Batch0327.cell2623.sound htau (by
                    simp only [Batch0327.cell2623, Batch0327.tau2623, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003310 (by positivity) using 1 <;> norm_num)
                · have hs01003312 : InSquare (-99/640) (-229/640) (1/640) tau := by
                    convert childUL hs0100331 hx0100331 hy0100331 using 1 <;> norm_num
                  exact Batch0328.cell2625.sound htau (by
                    simp only [Batch0328.cell2625, Batch0328.tau2625, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100331 | hy0100331
                · have hs01003311 : InSquare (-97/640) (-231/640) (1/640) tau := by
                    convert childLR hs0100331 hx0100331 hy0100331 using 1 <;> norm_num
                  exact Batch0328.cell2624.sound htau (by
                    simp only [Batch0328.cell2624, Batch0328.tau2624, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003311 (by positivity) using 1 <;> norm_num)
                · have hs01003313 : InSquare (-97/640) (-229/640) (1/640) tau := by
                    convert childUR hs0100331 hx0100331 hy0100331 using 1 <;> norm_num
                  exact Batch0328.cell2626.sound htau (by
                    simp only [Batch0328.cell2626, Batch0328.tau2626, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003313 (by positivity) using 1 <;> norm_num)
            · have hs0100333 : InSquare (-49/320) (-113/320) (1/320) tau := by
                convert childUR hs010033 hx010033 hy010033 using 1 <;> norm_num
              exact Batch0168.cell1346.sound htau (by
                simp only [Batch0168.cell1346, Batch0168.tau1346, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0100333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0100

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0101 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0101

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_010100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_010101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-21/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/8)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_010110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-19/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_010111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-17/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/10)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0101020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/320) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0101021 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/64) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/80)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0101022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/320) (-121/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/160)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0101030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-43/320) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0101031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-41/320) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/8)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01010230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/640) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/64)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01010231 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-89/640) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/80)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01010232 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/640) (-241/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/64)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01010320 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-87/640) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+43/320)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01010321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-17/128) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/160)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01011200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-79/640) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+39/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01011201 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-77/640) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/160)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01011202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-79/640) (-49/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+39/320)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01011210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-15/128) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+37/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01011211 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-73/640) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/80)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (-3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx0101 | hx0101
  · rcases le_total tau.im (-3/8 : ℝ) with hy0101 | hy0101
    · have hs01010 : InSquare (-11/80) (-31/80) (1/80) tau := by
        convert childLL hs hx0101 hy0101 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx01010 | hx01010
      · rcases le_total tau.im (-31/80 : ℝ) with hy01010 | hy01010
        · have hs010100 : InSquare (-23/160) (-63/160) (1/160) tau := by
            convert childLL hs01010 hx01010 hy01010 using 1 <;> norm_num
          exact (outside_010100 htau hs010100).elim
        · have hs010102 : InSquare (-23/160) (-61/160) (1/160) tau := by
            convert childUL hs01010 hx01010 hy01010 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx010102 | hx010102
          · rcases le_total tau.im (-61/160 : ℝ) with hy010102 | hy010102
            · have hs0101020 : InSquare (-47/320) (-123/320) (1/320) tau := by
                convert childLL hs010102 hx010102 hy010102 using 1 <;> norm_num
              exact (outside_0101020 htau hs0101020).elim
            · have hs0101022 : InSquare (-47/320) (-121/320) (1/320) tau := by
                convert childUL hs010102 hx010102 hy010102 using 1 <;> norm_num
              exact (outside_0101022 htau hs0101022).elim
          · rcases le_total tau.im (-61/160 : ℝ) with hy010102 | hy010102
            · have hs0101021 : InSquare (-9/64) (-123/320) (1/320) tau := by
                convert childLR hs010102 hx010102 hy010102 using 1 <;> norm_num
              exact (outside_0101021 htau hs0101021).elim
            · have hs0101023 : InSquare (-9/64) (-121/320) (1/320) tau := by
                convert childUR hs010102 hx010102 hy010102 using 1 <;> norm_num
              rcases le_total tau.re (-9/64 : ℝ) with hx0101023 | hx0101023
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101023 | hy0101023
                · have hs01010230 : InSquare (-91/640) (-243/640) (1/640) tau := by
                    convert childLL hs0101023 hx0101023 hy0101023 using 1 <;> norm_num
                  exact (outside_01010230 htau hs01010230).elim
                · have hs01010232 : InSquare (-91/640) (-241/640) (1/640) tau := by
                    convert childUL hs0101023 hx0101023 hy0101023 using 1 <;> norm_num
                  exact (outside_01010232 htau hs01010232).elim
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101023 | hy0101023
                · have hs01010231 : InSquare (-89/640) (-243/640) (1/640) tau := by
                    convert childLR hs0101023 hx0101023 hy0101023 using 1 <;> norm_num
                  exact (outside_01010231 htau hs01010231).elim
                · have hs01010233 : InSquare (-89/640) (-241/640) (1/640) tau := by
                    convert childUR hs0101023 hx0101023 hy0101023 using 1 <;> norm_num
                  exact Batch0328.cell2627.sound htau (by
                    simp only [Batch0328.cell2627, Batch0328.tau2627, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01010233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy01010 | hy01010
        · have hs010101 : InSquare (-21/160) (-63/160) (1/160) tau := by
            convert childLR hs01010 hx01010 hy01010 using 1 <;> norm_num
          exact (outside_010101 htau hs010101).elim
        · have hs010103 : InSquare (-21/160) (-61/160) (1/160) tau := by
            convert childUR hs01010 hx01010 hy01010 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx010103 | hx010103
          · rcases le_total tau.im (-61/160 : ℝ) with hy010103 | hy010103
            · have hs0101030 : InSquare (-43/320) (-123/320) (1/320) tau := by
                convert childLL hs010103 hx010103 hy010103 using 1 <;> norm_num
              exact (outside_0101030 htau hs0101030).elim
            · have hs0101032 : InSquare (-43/320) (-121/320) (1/320) tau := by
                convert childUL hs010103 hx010103 hy010103 using 1 <;> norm_num
              rcases le_total tau.re (-43/320 : ℝ) with hx0101032 | hx0101032
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101032 | hy0101032
                · have hs01010320 : InSquare (-87/640) (-243/640) (1/640) tau := by
                    convert childLL hs0101032 hx0101032 hy0101032 using 1 <;> norm_num
                  exact (outside_01010320 htau hs01010320).elim
                · have hs01010322 : InSquare (-87/640) (-241/640) (1/640) tau := by
                    convert childUL hs0101032 hx0101032 hy0101032 using 1 <;> norm_num
                  exact Batch0328.cell2628.sound htau (by
                    simp only [Batch0328.cell2628, Batch0328.tau2628, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01010322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101032 | hy0101032
                · have hs01010321 : InSquare (-17/128) (-243/640) (1/640) tau := by
                    convert childLR hs0101032 hx0101032 hy0101032 using 1 <;> norm_num
                  exact (outside_01010321 htau hs01010321).elim
                · have hs01010323 : InSquare (-17/128) (-241/640) (1/640) tau := by
                    convert childUR hs0101032 hx0101032 hy0101032 using 1 <;> norm_num
                  exact Batch0328.cell2629.sound htau (by
                    simp only [Batch0328.cell2629, Batch0328.tau2629, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01010323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy010103 | hy010103
            · have hs0101031 : InSquare (-41/320) (-123/320) (1/320) tau := by
                convert childLR hs010103 hx010103 hy010103 using 1 <;> norm_num
              exact (outside_0101031 htau hs0101031).elim
            · have hs0101033 : InSquare (-41/320) (-121/320) (1/320) tau := by
                convert childUR hs010103 hx010103 hy010103 using 1 <;> norm_num
              rcases le_total tau.re (-41/320 : ℝ) with hx0101033 | hx0101033
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101033 | hy0101033
                · have hs01010330 : InSquare (-83/640) (-243/640) (1/640) tau := by
                    convert childLL hs0101033 hx0101033 hy0101033 using 1 <;> norm_num
                  exact Batch0328.cell2630.sound htau (by
                    simp only [Batch0328.cell2630, Batch0328.tau2630, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01010330 (by positivity) using 1 <;> norm_num)
                · have hs01010332 : InSquare (-83/640) (-241/640) (1/640) tau := by
                    convert childUL hs0101033 hx0101033 hy0101033 using 1 <;> norm_num
                  exact Batch0329.cell2632.sound htau (by
                    simp only [Batch0329.cell2632, Batch0329.tau2632, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01010332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101033 | hy0101033
                · have hs01010331 : InSquare (-81/640) (-243/640) (1/640) tau := by
                    convert childLR hs0101033 hx0101033 hy0101033 using 1 <;> norm_num
                  exact Batch0328.cell2631.sound htau (by
                    simp only [Batch0328.cell2631, Batch0328.tau2631, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01010331 (by positivity) using 1 <;> norm_num)
                · have hs01010333 : InSquare (-81/640) (-241/640) (1/640) tau := by
                    convert childUR hs0101033 hx0101033 hy0101033 using 1 <;> norm_num
                  exact Batch0329.cell2633.sound htau (by
                    simp only [Batch0329.cell2633, Batch0329.tau2633, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01010333 (by positivity) using 1 <;> norm_num)
    · have hs01012 : InSquare (-11/80) (-29/80) (1/80) tau := by
        convert childUL hs hx0101 hy0101 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx01012 | hx01012
      · rcases le_total tau.im (-29/80 : ℝ) with hy01012 | hy01012
        · have hs010120 : InSquare (-23/160) (-59/160) (1/160) tau := by
            convert childLL hs01012 hx01012 hy01012 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx010120 | hx010120
          · rcases le_total tau.im (-59/160 : ℝ) with hy010120 | hy010120
            · have hs0101200 : InSquare (-47/320) (-119/320) (1/320) tau := by
                convert childLL hs010120 hx010120 hy010120 using 1 <;> norm_num
              rcases le_total tau.re (-47/320 : ℝ) with hx0101200 | hx0101200
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101200 | hy0101200
                · have hs01012000 : InSquare (-19/128) (-239/640) (1/640) tau := by
                    convert childLL hs0101200 hx0101200 hy0101200 using 1 <;> norm_num
                  exact Batch0332.cell2661.sound htau (by
                    simp only [Batch0332.cell2661, Batch0332.tau2661, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012000 (by positivity) using 1 <;> norm_num)
                · have hs01012002 : InSquare (-19/128) (-237/640) (1/640) tau := by
                    convert childUL hs0101200 hx0101200 hy0101200 using 1 <;> norm_num
                  exact Batch0332.cell2663.sound htau (by
                    simp only [Batch0332.cell2663, Batch0332.tau2663, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101200 | hy0101200
                · have hs01012001 : InSquare (-93/640) (-239/640) (1/640) tau := by
                    convert childLR hs0101200 hx0101200 hy0101200 using 1 <;> norm_num
                  exact Batch0332.cell2662.sound htau (by
                    simp only [Batch0332.cell2662, Batch0332.tau2662, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012001 (by positivity) using 1 <;> norm_num)
                · have hs01012003 : InSquare (-93/640) (-237/640) (1/640) tau := by
                    convert childUR hs0101200 hx0101200 hy0101200 using 1 <;> norm_num
                  exact Batch0333.cell2664.sound htau (by
                    simp only [Batch0333.cell2664, Batch0333.tau2664, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012003 (by positivity) using 1 <;> norm_num)
            · have hs0101202 : InSquare (-47/320) (-117/320) (1/320) tau := by
                convert childUL hs010120 hx010120 hy010120 using 1 <;> norm_num
              rcases le_total tau.re (-47/320 : ℝ) with hx0101202 | hx0101202
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101202 | hy0101202
                · have hs01012020 : InSquare (-19/128) (-47/128) (1/640) tau := by
                    convert childLL hs0101202 hx0101202 hy0101202 using 1 <;> norm_num
                  exact Batch0333.cell2669.sound htau (by
                    simp only [Batch0333.cell2669, Batch0333.tau2669, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012020 (by positivity) using 1 <;> norm_num)
                · have hs01012022 : InSquare (-19/128) (-233/640) (1/640) tau := by
                    convert childUL hs0101202 hx0101202 hy0101202 using 1 <;> norm_num
                  exact Batch0333.cell2671.sound htau (by
                    simp only [Batch0333.cell2671, Batch0333.tau2671, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101202 | hy0101202
                · have hs01012021 : InSquare (-93/640) (-47/128) (1/640) tau := by
                    convert childLR hs0101202 hx0101202 hy0101202 using 1 <;> norm_num
                  exact Batch0333.cell2670.sound htau (by
                    simp only [Batch0333.cell2670, Batch0333.tau2670, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012021 (by positivity) using 1 <;> norm_num)
                · have hs01012023 : InSquare (-93/640) (-233/640) (1/640) tau := by
                    convert childUR hs0101202 hx0101202 hy0101202 using 1 <;> norm_num
                  exact Batch0334.cell2672.sound htau (by
                    simp only [Batch0334.cell2672, Batch0334.tau2672, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy010120 | hy010120
            · have hs0101201 : InSquare (-9/64) (-119/320) (1/320) tau := by
                convert childLR hs010120 hx010120 hy010120 using 1 <;> norm_num
              rcases le_total tau.re (-9/64 : ℝ) with hx0101201 | hx0101201
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101201 | hy0101201
                · have hs01012010 : InSquare (-91/640) (-239/640) (1/640) tau := by
                    convert childLL hs0101201 hx0101201 hy0101201 using 1 <;> norm_num
                  exact Batch0333.cell2665.sound htau (by
                    simp only [Batch0333.cell2665, Batch0333.tau2665, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012010 (by positivity) using 1 <;> norm_num)
                · have hs01012012 : InSquare (-91/640) (-237/640) (1/640) tau := by
                    convert childUL hs0101201 hx0101201 hy0101201 using 1 <;> norm_num
                  exact Batch0333.cell2667.sound htau (by
                    simp only [Batch0333.cell2667, Batch0333.tau2667, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101201 | hy0101201
                · have hs01012011 : InSquare (-89/640) (-239/640) (1/640) tau := by
                    convert childLR hs0101201 hx0101201 hy0101201 using 1 <;> norm_num
                  exact Batch0333.cell2666.sound htau (by
                    simp only [Batch0333.cell2666, Batch0333.tau2666, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012011 (by positivity) using 1 <;> norm_num)
                · have hs01012013 : InSquare (-89/640) (-237/640) (1/640) tau := by
                    convert childUR hs0101201 hx0101201 hy0101201 using 1 <;> norm_num
                  exact Batch0333.cell2668.sound htau (by
                    simp only [Batch0333.cell2668, Batch0333.tau2668, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012013 (by positivity) using 1 <;> norm_num)
            · have hs0101203 : InSquare (-9/64) (-117/320) (1/320) tau := by
                convert childUR hs010120 hx010120 hy010120 using 1 <;> norm_num
              rcases le_total tau.re (-9/64 : ℝ) with hx0101203 | hx0101203
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101203 | hy0101203
                · have hs01012030 : InSquare (-91/640) (-47/128) (1/640) tau := by
                    convert childLL hs0101203 hx0101203 hy0101203 using 1 <;> norm_num
                  exact Batch0334.cell2673.sound htau (by
                    simp only [Batch0334.cell2673, Batch0334.tau2673, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012030 (by positivity) using 1 <;> norm_num)
                · have hs01012032 : InSquare (-91/640) (-233/640) (1/640) tau := by
                    convert childUL hs0101203 hx0101203 hy0101203 using 1 <;> norm_num
                  exact Batch0334.cell2675.sound htau (by
                    simp only [Batch0334.cell2675, Batch0334.tau2675, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101203 | hy0101203
                · have hs01012031 : InSquare (-89/640) (-47/128) (1/640) tau := by
                    convert childLR hs0101203 hx0101203 hy0101203 using 1 <;> norm_num
                  exact Batch0334.cell2674.sound htau (by
                    simp only [Batch0334.cell2674, Batch0334.tau2674, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012031 (by positivity) using 1 <;> norm_num)
                · have hs01012033 : InSquare (-89/640) (-233/640) (1/640) tau := by
                    convert childUR hs0101203 hx0101203 hy0101203 using 1 <;> norm_num
                  exact Batch0334.cell2676.sound htau (by
                    simp only [Batch0334.cell2676, Batch0334.tau2676, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012033 (by positivity) using 1 <;> norm_num)
        · have hs010122 : InSquare (-23/160) (-57/160) (1/160) tau := by
            convert childUL hs01012 hx01012 hy01012 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx010122 | hx010122
          · rcases le_total tau.im (-57/160 : ℝ) with hy010122 | hy010122
            · have hs0101220 : InSquare (-47/320) (-23/64) (1/320) tau := by
                convert childLL hs010122 hx010122 hy010122 using 1 <;> norm_num
              rcases le_total tau.re (-47/320 : ℝ) with hx0101220 | hx0101220
              · rcases le_total tau.im (-23/64 : ℝ) with hy0101220 | hy0101220
                · have hs01012200 : InSquare (-19/128) (-231/640) (1/640) tau := by
                    convert childLL hs0101220 hx0101220 hy0101220 using 1 <;> norm_num
                  exact Batch0336.cell2693.sound htau (by
                    simp only [Batch0336.cell2693, Batch0336.tau2693, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012200 (by positivity) using 1 <;> norm_num)
                · have hs01012202 : InSquare (-19/128) (-229/640) (1/640) tau := by
                    convert childUL hs0101220 hx0101220 hy0101220 using 1 <;> norm_num
                  exact Batch0336.cell2695.sound htau (by
                    simp only [Batch0336.cell2695, Batch0336.tau2695, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy0101220 | hy0101220
                · have hs01012201 : InSquare (-93/640) (-231/640) (1/640) tau := by
                    convert childLR hs0101220 hx0101220 hy0101220 using 1 <;> norm_num
                  exact Batch0336.cell2694.sound htau (by
                    simp only [Batch0336.cell2694, Batch0336.tau2694, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012201 (by positivity) using 1 <;> norm_num)
                · have hs01012203 : InSquare (-93/640) (-229/640) (1/640) tau := by
                    convert childUR hs0101220 hx0101220 hy0101220 using 1 <;> norm_num
                  exact Batch0337.cell2696.sound htau (by
                    simp only [Batch0337.cell2696, Batch0337.tau2696, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012203 (by positivity) using 1 <;> norm_num)
            · have hs0101222 : InSquare (-47/320) (-113/320) (1/320) tau := by
                convert childUL hs010122 hx010122 hy010122 using 1 <;> norm_num
              exact Batch0168.cell1348.sound htau (by
                simp only [Batch0168.cell1348, Batch0168.tau1348, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy010122 | hy010122
            · have hs0101221 : InSquare (-9/64) (-23/64) (1/320) tau := by
                convert childLR hs010122 hx010122 hy010122 using 1 <;> norm_num
              exact Batch0168.cell1347.sound htau (by
                simp only [Batch0168.cell1347, Batch0168.tau1347, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101221 (by positivity) using 1 <;> norm_num)
            · have hs0101223 : InSquare (-9/64) (-113/320) (1/320) tau := by
                convert childUR hs010122 hx010122 hy010122 using 1 <;> norm_num
              exact Batch0168.cell1349.sound htau (by
                simp only [Batch0168.cell1349, Batch0168.tau1349, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01012 | hy01012
        · have hs010121 : InSquare (-21/160) (-59/160) (1/160) tau := by
            convert childLR hs01012 hx01012 hy01012 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx010121 | hx010121
          · rcases le_total tau.im (-59/160 : ℝ) with hy010121 | hy010121
            · have hs0101210 : InSquare (-43/320) (-119/320) (1/320) tau := by
                convert childLL hs010121 hx010121 hy010121 using 1 <;> norm_num
              rcases le_total tau.re (-43/320 : ℝ) with hx0101210 | hx0101210
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101210 | hy0101210
                · have hs01012100 : InSquare (-87/640) (-239/640) (1/640) tau := by
                    convert childLL hs0101210 hx0101210 hy0101210 using 1 <;> norm_num
                  exact Batch0334.cell2677.sound htau (by
                    simp only [Batch0334.cell2677, Batch0334.tau2677, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012100 (by positivity) using 1 <;> norm_num)
                · have hs01012102 : InSquare (-87/640) (-237/640) (1/640) tau := by
                    convert childUL hs0101210 hx0101210 hy0101210 using 1 <;> norm_num
                  exact Batch0334.cell2679.sound htau (by
                    simp only [Batch0334.cell2679, Batch0334.tau2679, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101210 | hy0101210
                · have hs01012101 : InSquare (-17/128) (-239/640) (1/640) tau := by
                    convert childLR hs0101210 hx0101210 hy0101210 using 1 <;> norm_num
                  exact Batch0334.cell2678.sound htau (by
                    simp only [Batch0334.cell2678, Batch0334.tau2678, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012101 (by positivity) using 1 <;> norm_num)
                · have hs01012103 : InSquare (-17/128) (-237/640) (1/640) tau := by
                    convert childUR hs0101210 hx0101210 hy0101210 using 1 <;> norm_num
                  exact Batch0335.cell2680.sound htau (by
                    simp only [Batch0335.cell2680, Batch0335.tau2680, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012103 (by positivity) using 1 <;> norm_num)
            · have hs0101212 : InSquare (-43/320) (-117/320) (1/320) tau := by
                convert childUL hs010121 hx010121 hy010121 using 1 <;> norm_num
              rcases le_total tau.re (-43/320 : ℝ) with hx0101212 | hx0101212
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101212 | hy0101212
                · have hs01012120 : InSquare (-87/640) (-47/128) (1/640) tau := by
                    convert childLL hs0101212 hx0101212 hy0101212 using 1 <;> norm_num
                  exact Batch0335.cell2685.sound htau (by
                    simp only [Batch0335.cell2685, Batch0335.tau2685, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012120 (by positivity) using 1 <;> norm_num)
                · have hs01012122 : InSquare (-87/640) (-233/640) (1/640) tau := by
                    convert childUL hs0101212 hx0101212 hy0101212 using 1 <;> norm_num
                  exact Batch0335.cell2687.sound htau (by
                    simp only [Batch0335.cell2687, Batch0335.tau2687, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101212 | hy0101212
                · have hs01012121 : InSquare (-17/128) (-47/128) (1/640) tau := by
                    convert childLR hs0101212 hx0101212 hy0101212 using 1 <;> norm_num
                  exact Batch0335.cell2686.sound htau (by
                    simp only [Batch0335.cell2686, Batch0335.tau2686, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012121 (by positivity) using 1 <;> norm_num)
                · have hs01012123 : InSquare (-17/128) (-233/640) (1/640) tau := by
                    convert childUR hs0101212 hx0101212 hy0101212 using 1 <;> norm_num
                  exact Batch0336.cell2688.sound htau (by
                    simp only [Batch0336.cell2688, Batch0336.tau2688, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy010121 | hy010121
            · have hs0101211 : InSquare (-41/320) (-119/320) (1/320) tau := by
                convert childLR hs010121 hx010121 hy010121 using 1 <;> norm_num
              rcases le_total tau.re (-41/320 : ℝ) with hx0101211 | hx0101211
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101211 | hy0101211
                · have hs01012110 : InSquare (-83/640) (-239/640) (1/640) tau := by
                    convert childLL hs0101211 hx0101211 hy0101211 using 1 <;> norm_num
                  exact Batch0335.cell2681.sound htau (by
                    simp only [Batch0335.cell2681, Batch0335.tau2681, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012110 (by positivity) using 1 <;> norm_num)
                · have hs01012112 : InSquare (-83/640) (-237/640) (1/640) tau := by
                    convert childUL hs0101211 hx0101211 hy0101211 using 1 <;> norm_num
                  exact Batch0335.cell2683.sound htau (by
                    simp only [Batch0335.cell2683, Batch0335.tau2683, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101211 | hy0101211
                · have hs01012111 : InSquare (-81/640) (-239/640) (1/640) tau := by
                    convert childLR hs0101211 hx0101211 hy0101211 using 1 <;> norm_num
                  exact Batch0335.cell2682.sound htau (by
                    simp only [Batch0335.cell2682, Batch0335.tau2682, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012111 (by positivity) using 1 <;> norm_num)
                · have hs01012113 : InSquare (-81/640) (-237/640) (1/640) tau := by
                    convert childUR hs0101211 hx0101211 hy0101211 using 1 <;> norm_num
                  exact Batch0335.cell2684.sound htau (by
                    simp only [Batch0335.cell2684, Batch0335.tau2684, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012113 (by positivity) using 1 <;> norm_num)
            · have hs0101213 : InSquare (-41/320) (-117/320) (1/320) tau := by
                convert childUR hs010121 hx010121 hy010121 using 1 <;> norm_num
              rcases le_total tau.re (-41/320 : ℝ) with hx0101213 | hx0101213
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101213 | hy0101213
                · have hs01012130 : InSquare (-83/640) (-47/128) (1/640) tau := by
                    convert childLL hs0101213 hx0101213 hy0101213 using 1 <;> norm_num
                  exact Batch0336.cell2689.sound htau (by
                    simp only [Batch0336.cell2689, Batch0336.tau2689, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012130 (by positivity) using 1 <;> norm_num)
                · have hs01012132 : InSquare (-83/640) (-233/640) (1/640) tau := by
                    convert childUL hs0101213 hx0101213 hy0101213 using 1 <;> norm_num
                  exact Batch0336.cell2691.sound htau (by
                    simp only [Batch0336.cell2691, Batch0336.tau2691, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101213 | hy0101213
                · have hs01012131 : InSquare (-81/640) (-47/128) (1/640) tau := by
                    convert childLR hs0101213 hx0101213 hy0101213 using 1 <;> norm_num
                  exact Batch0336.cell2690.sound htau (by
                    simp only [Batch0336.cell2690, Batch0336.tau2690, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012131 (by positivity) using 1 <;> norm_num)
                · have hs01012133 : InSquare (-81/640) (-233/640) (1/640) tau := by
                    convert childUR hs0101213 hx0101213 hy0101213 using 1 <;> norm_num
                  exact Batch0336.cell2692.sound htau (by
                    simp only [Batch0336.cell2692, Batch0336.tau2692, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012133 (by positivity) using 1 <;> norm_num)
        · have hs010123 : InSquare (-21/160) (-57/160) (1/160) tau := by
            convert childUR hs01012 hx01012 hy01012 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx010123 | hx010123
          · rcases le_total tau.im (-57/160 : ℝ) with hy010123 | hy010123
            · have hs0101230 : InSquare (-43/320) (-23/64) (1/320) tau := by
                convert childLL hs010123 hx010123 hy010123 using 1 <;> norm_num
              exact Batch0168.cell1350.sound htau (by
                simp only [Batch0168.cell1350, Batch0168.tau1350, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101230 (by positivity) using 1 <;> norm_num)
            · have hs0101232 : InSquare (-43/320) (-113/320) (1/320) tau := by
                convert childUL hs010123 hx010123 hy010123 using 1 <;> norm_num
              exact Batch0169.cell1352.sound htau (by
                simp only [Batch0169.cell1352, Batch0169.tau1352, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy010123 | hy010123
            · have hs0101231 : InSquare (-41/320) (-23/64) (1/320) tau := by
                convert childLR hs010123 hx010123 hy010123 using 1 <;> norm_num
              exact Batch0168.cell1351.sound htau (by
                simp only [Batch0168.cell1351, Batch0168.tau1351, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101231 (by positivity) using 1 <;> norm_num)
            · have hs0101233 : InSquare (-41/320) (-113/320) (1/320) tau := by
                convert childUR hs010123 hx010123 hy010123 using 1 <;> norm_num
              exact Batch0169.cell1353.sound htau (by
                simp only [Batch0169.cell1353, Batch0169.tau1353, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/8 : ℝ) with hy0101 | hy0101
    · have hs01011 : InSquare (-9/80) (-31/80) (1/80) tau := by
        convert childLR hs hx0101 hy0101 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx01011 | hx01011
      · rcases le_total tau.im (-31/80 : ℝ) with hy01011 | hy01011
        · have hs010110 : InSquare (-19/160) (-63/160) (1/160) tau := by
            convert childLL hs01011 hx01011 hy01011 using 1 <;> norm_num
          exact (outside_010110 htau hs010110).elim
        · have hs010112 : InSquare (-19/160) (-61/160) (1/160) tau := by
            convert childUL hs01011 hx01011 hy01011 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx010112 | hx010112
          · rcases le_total tau.im (-61/160 : ℝ) with hy010112 | hy010112
            · have hs0101120 : InSquare (-39/320) (-123/320) (1/320) tau := by
                convert childLL hs010112 hx010112 hy010112 using 1 <;> norm_num
              rcases le_total tau.re (-39/320 : ℝ) with hx0101120 | hx0101120
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101120 | hy0101120
                · have hs01011200 : InSquare (-79/640) (-247/640) (1/640) tau := by
                    convert childLL hs0101120 hx0101120 hy0101120 using 1 <;> norm_num
                  exact (outside_01011200 htau hs01011200).elim
                · have hs01011202 : InSquare (-79/640) (-49/128) (1/640) tau := by
                    convert childUL hs0101120 hx0101120 hy0101120 using 1 <;> norm_num
                  exact (outside_01011202 htau hs01011202).elim
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101120 | hy0101120
                · have hs01011201 : InSquare (-77/640) (-247/640) (1/640) tau := by
                    convert childLR hs0101120 hx0101120 hy0101120 using 1 <;> norm_num
                  exact (outside_01011201 htau hs01011201).elim
                · have hs01011203 : InSquare (-77/640) (-49/128) (1/640) tau := by
                    convert childUR hs0101120 hx0101120 hy0101120 using 1 <;> norm_num
                  exact Batch0329.cell2634.sound htau (by
                    simp only [Batch0329.cell2634, Batch0329.tau2634, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011203 (by positivity) using 1 <;> norm_num)
            · have hs0101122 : InSquare (-39/320) (-121/320) (1/320) tau := by
                convert childUL hs010112 hx010112 hy010112 using 1 <;> norm_num
              rcases le_total tau.re (-39/320 : ℝ) with hx0101122 | hx0101122
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101122 | hy0101122
                · have hs01011220 : InSquare (-79/640) (-243/640) (1/640) tau := by
                    convert childLL hs0101122 hx0101122 hy0101122 using 1 <;> norm_num
                  exact Batch0329.cell2637.sound htau (by
                    simp only [Batch0329.cell2637, Batch0329.tau2637, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011220 (by positivity) using 1 <;> norm_num)
                · have hs01011222 : InSquare (-79/640) (-241/640) (1/640) tau := by
                    convert childUL hs0101122 hx0101122 hy0101122 using 1 <;> norm_num
                  exact Batch0329.cell2639.sound htau (by
                    simp only [Batch0329.cell2639, Batch0329.tau2639, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101122 | hy0101122
                · have hs01011221 : InSquare (-77/640) (-243/640) (1/640) tau := by
                    convert childLR hs0101122 hx0101122 hy0101122 using 1 <;> norm_num
                  exact Batch0329.cell2638.sound htau (by
                    simp only [Batch0329.cell2638, Batch0329.tau2638, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011221 (by positivity) using 1 <;> norm_num)
                · have hs01011223 : InSquare (-77/640) (-241/640) (1/640) tau := by
                    convert childUR hs0101122 hx0101122 hy0101122 using 1 <;> norm_num
                  exact Batch0330.cell2640.sound htau (by
                    simp only [Batch0330.cell2640, Batch0330.tau2640, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy010112 | hy010112
            · have hs0101121 : InSquare (-37/320) (-123/320) (1/320) tau := by
                convert childLR hs010112 hx010112 hy010112 using 1 <;> norm_num
              rcases le_total tau.re (-37/320 : ℝ) with hx0101121 | hx0101121
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101121 | hy0101121
                · have hs01011210 : InSquare (-15/128) (-247/640) (1/640) tau := by
                    convert childLL hs0101121 hx0101121 hy0101121 using 1 <;> norm_num
                  exact (outside_01011210 htau hs01011210).elim
                · have hs01011212 : InSquare (-15/128) (-49/128) (1/640) tau := by
                    convert childUL hs0101121 hx0101121 hy0101121 using 1 <;> norm_num
                  exact Batch0329.cell2635.sound htau (by
                    simp only [Batch0329.cell2635, Batch0329.tau2635, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101121 | hy0101121
                · have hs01011211 : InSquare (-73/640) (-247/640) (1/640) tau := by
                    convert childLR hs0101121 hx0101121 hy0101121 using 1 <;> norm_num
                  exact (outside_01011211 htau hs01011211).elim
                · have hs01011213 : InSquare (-73/640) (-49/128) (1/640) tau := by
                    convert childUR hs0101121 hx0101121 hy0101121 using 1 <;> norm_num
                  exact Batch0329.cell2636.sound htau (by
                    simp only [Batch0329.cell2636, Batch0329.tau2636, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011213 (by positivity) using 1 <;> norm_num)
            · have hs0101123 : InSquare (-37/320) (-121/320) (1/320) tau := by
                convert childUR hs010112 hx010112 hy010112 using 1 <;> norm_num
              rcases le_total tau.re (-37/320 : ℝ) with hx0101123 | hx0101123
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101123 | hy0101123
                · have hs01011230 : InSquare (-15/128) (-243/640) (1/640) tau := by
                    convert childLL hs0101123 hx0101123 hy0101123 using 1 <;> norm_num
                  exact Batch0330.cell2641.sound htau (by
                    simp only [Batch0330.cell2641, Batch0330.tau2641, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011230 (by positivity) using 1 <;> norm_num)
                · have hs01011232 : InSquare (-15/128) (-241/640) (1/640) tau := by
                    convert childUL hs0101123 hx0101123 hy0101123 using 1 <;> norm_num
                  exact Batch0330.cell2643.sound htau (by
                    simp only [Batch0330.cell2643, Batch0330.tau2643, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101123 | hy0101123
                · have hs01011231 : InSquare (-73/640) (-243/640) (1/640) tau := by
                    convert childLR hs0101123 hx0101123 hy0101123 using 1 <;> norm_num
                  exact Batch0330.cell2642.sound htau (by
                    simp only [Batch0330.cell2642, Batch0330.tau2642, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011231 (by positivity) using 1 <;> norm_num)
                · have hs01011233 : InSquare (-73/640) (-241/640) (1/640) tau := by
                    convert childUR hs0101123 hx0101123 hy0101123 using 1 <;> norm_num
                  exact Batch0330.cell2644.sound htau (by
                    simp only [Batch0330.cell2644, Batch0330.tau2644, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy01011 | hy01011
        · have hs010111 : InSquare (-17/160) (-63/160) (1/160) tau := by
            convert childLR hs01011 hx01011 hy01011 using 1 <;> norm_num
          exact (outside_010111 htau hs010111).elim
        · have hs010113 : InSquare (-17/160) (-61/160) (1/160) tau := by
            convert childUR hs01011 hx01011 hy01011 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx010113 | hx010113
          · rcases le_total tau.im (-61/160 : ℝ) with hy010113 | hy010113
            · have hs0101130 : InSquare (-7/64) (-123/320) (1/320) tau := by
                convert childLL hs010113 hx010113 hy010113 using 1 <;> norm_num
              rcases le_total tau.re (-7/64 : ℝ) with hx0101130 | hx0101130
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101130 | hy0101130
                · have hs01011300 : InSquare (-71/640) (-247/640) (1/640) tau := by
                    convert childLL hs0101130 hx0101130 hy0101130 using 1 <;> norm_num
                  exact Batch0330.cell2645.sound htau (by
                    simp only [Batch0330.cell2645, Batch0330.tau2645, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011300 (by positivity) using 1 <;> norm_num)
                · have hs01011302 : InSquare (-71/640) (-49/128) (1/640) tau := by
                    convert childUL hs0101130 hx0101130 hy0101130 using 1 <;> norm_num
                  exact Batch0330.cell2647.sound htau (by
                    simp only [Batch0330.cell2647, Batch0330.tau2647, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101130 | hy0101130
                · have hs01011301 : InSquare (-69/640) (-247/640) (1/640) tau := by
                    convert childLR hs0101130 hx0101130 hy0101130 using 1 <;> norm_num
                  exact Batch0330.cell2646.sound htau (by
                    simp only [Batch0330.cell2646, Batch0330.tau2646, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011301 (by positivity) using 1 <;> norm_num)
                · have hs01011303 : InSquare (-69/640) (-49/128) (1/640) tau := by
                    convert childUR hs0101130 hx0101130 hy0101130 using 1 <;> norm_num
                  exact Batch0331.cell2648.sound htau (by
                    simp only [Batch0331.cell2648, Batch0331.tau2648, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011303 (by positivity) using 1 <;> norm_num)
            · have hs0101132 : InSquare (-7/64) (-121/320) (1/320) tau := by
                convert childUL hs010113 hx010113 hy010113 using 1 <;> norm_num
              rcases le_total tau.re (-7/64 : ℝ) with hx0101132 | hx0101132
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101132 | hy0101132
                · have hs01011320 : InSquare (-71/640) (-243/640) (1/640) tau := by
                    convert childLL hs0101132 hx0101132 hy0101132 using 1 <;> norm_num
                  exact Batch0331.cell2653.sound htau (by
                    simp only [Batch0331.cell2653, Batch0331.tau2653, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011320 (by positivity) using 1 <;> norm_num)
                · have hs01011322 : InSquare (-71/640) (-241/640) (1/640) tau := by
                    convert childUL hs0101132 hx0101132 hy0101132 using 1 <;> norm_num
                  exact Batch0331.cell2655.sound htau (by
                    simp only [Batch0331.cell2655, Batch0331.tau2655, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101132 | hy0101132
                · have hs01011321 : InSquare (-69/640) (-243/640) (1/640) tau := by
                    convert childLR hs0101132 hx0101132 hy0101132 using 1 <;> norm_num
                  exact Batch0331.cell2654.sound htau (by
                    simp only [Batch0331.cell2654, Batch0331.tau2654, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011321 (by positivity) using 1 <;> norm_num)
                · have hs01011323 : InSquare (-69/640) (-241/640) (1/640) tau := by
                    convert childUR hs0101132 hx0101132 hy0101132 using 1 <;> norm_num
                  exact Batch0332.cell2656.sound htau (by
                    simp only [Batch0332.cell2656, Batch0332.tau2656, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy010113 | hy010113
            · have hs0101131 : InSquare (-33/320) (-123/320) (1/320) tau := by
                convert childLR hs010113 hx010113 hy010113 using 1 <;> norm_num
              rcases le_total tau.re (-33/320 : ℝ) with hx0101131 | hx0101131
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101131 | hy0101131
                · have hs01011310 : InSquare (-67/640) (-247/640) (1/640) tau := by
                    convert childLL hs0101131 hx0101131 hy0101131 using 1 <;> norm_num
                  exact Batch0331.cell2649.sound htau (by
                    simp only [Batch0331.cell2649, Batch0331.tau2649, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011310 (by positivity) using 1 <;> norm_num)
                · have hs01011312 : InSquare (-67/640) (-49/128) (1/640) tau := by
                    convert childUL hs0101131 hx0101131 hy0101131 using 1 <;> norm_num
                  exact Batch0331.cell2651.sound htau (by
                    simp only [Batch0331.cell2651, Batch0331.tau2651, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101131 | hy0101131
                · have hs01011311 : InSquare (-13/128) (-247/640) (1/640) tau := by
                    convert childLR hs0101131 hx0101131 hy0101131 using 1 <;> norm_num
                  exact Batch0331.cell2650.sound htau (by
                    simp only [Batch0331.cell2650, Batch0331.tau2650, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011311 (by positivity) using 1 <;> norm_num)
                · have hs01011313 : InSquare (-13/128) (-49/128) (1/640) tau := by
                    convert childUR hs0101131 hx0101131 hy0101131 using 1 <;> norm_num
                  exact Batch0331.cell2652.sound htau (by
                    simp only [Batch0331.cell2652, Batch0331.tau2652, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011313 (by positivity) using 1 <;> norm_num)
            · have hs0101133 : InSquare (-33/320) (-121/320) (1/320) tau := by
                convert childUR hs010113 hx010113 hy010113 using 1 <;> norm_num
              rcases le_total tau.re (-33/320 : ℝ) with hx0101133 | hx0101133
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101133 | hy0101133
                · have hs01011330 : InSquare (-67/640) (-243/640) (1/640) tau := by
                    convert childLL hs0101133 hx0101133 hy0101133 using 1 <;> norm_num
                  exact Batch0332.cell2657.sound htau (by
                    simp only [Batch0332.cell2657, Batch0332.tau2657, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011330 (by positivity) using 1 <;> norm_num)
                · have hs01011332 : InSquare (-67/640) (-241/640) (1/640) tau := by
                    convert childUL hs0101133 hx0101133 hy0101133 using 1 <;> norm_num
                  exact Batch0332.cell2659.sound htau (by
                    simp only [Batch0332.cell2659, Batch0332.tau2659, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101133 | hy0101133
                · have hs01011331 : InSquare (-13/128) (-243/640) (1/640) tau := by
                    convert childLR hs0101133 hx0101133 hy0101133 using 1 <;> norm_num
                  exact Batch0332.cell2658.sound htau (by
                    simp only [Batch0332.cell2658, Batch0332.tau2658, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011331 (by positivity) using 1 <;> norm_num)
                · have hs01011333 : InSquare (-13/128) (-241/640) (1/640) tau := by
                    convert childUR hs0101133 hx0101133 hy0101133 using 1 <;> norm_num
                  exact Batch0332.cell2660.sound htau (by
                    simp only [Batch0332.cell2660, Batch0332.tau2660, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011333 (by positivity) using 1 <;> norm_num)
    · have hs01013 : InSquare (-9/80) (-29/80) (1/80) tau := by
        convert childUR hs hx0101 hy0101 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx01013 | hx01013
      · rcases le_total tau.im (-29/80 : ℝ) with hy01013 | hy01013
        · have hs010130 : InSquare (-19/160) (-59/160) (1/160) tau := by
            convert childLL hs01013 hx01013 hy01013 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx010130 | hx010130
          · rcases le_total tau.im (-59/160 : ℝ) with hy010130 | hy010130
            · have hs0101300 : InSquare (-39/320) (-119/320) (1/320) tau := by
                convert childLL hs010130 hx010130 hy010130 using 1 <;> norm_num
              rcases le_total tau.re (-39/320 : ℝ) with hx0101300 | hx0101300
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101300 | hy0101300
                · have hs01013000 : InSquare (-79/640) (-239/640) (1/640) tau := by
                    convert childLL hs0101300 hx0101300 hy0101300 using 1 <;> norm_num
                  exact Batch0337.cell2697.sound htau (by
                    simp only [Batch0337.cell2697, Batch0337.tau2697, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013000 (by positivity) using 1 <;> norm_num)
                · have hs01013002 : InSquare (-79/640) (-237/640) (1/640) tau := by
                    convert childUL hs0101300 hx0101300 hy0101300 using 1 <;> norm_num
                  exact Batch0337.cell2699.sound htau (by
                    simp only [Batch0337.cell2699, Batch0337.tau2699, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101300 | hy0101300
                · have hs01013001 : InSquare (-77/640) (-239/640) (1/640) tau := by
                    convert childLR hs0101300 hx0101300 hy0101300 using 1 <;> norm_num
                  exact Batch0337.cell2698.sound htau (by
                    simp only [Batch0337.cell2698, Batch0337.tau2698, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013001 (by positivity) using 1 <;> norm_num)
                · have hs01013003 : InSquare (-77/640) (-237/640) (1/640) tau := by
                    convert childUR hs0101300 hx0101300 hy0101300 using 1 <;> norm_num
                  exact Batch0337.cell2700.sound htau (by
                    simp only [Batch0337.cell2700, Batch0337.tau2700, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013003 (by positivity) using 1 <;> norm_num)
            · have hs0101302 : InSquare (-39/320) (-117/320) (1/320) tau := by
                convert childUL hs010130 hx010130 hy010130 using 1 <;> norm_num
              exact Batch0169.cell1354.sound htau (by
                simp only [Batch0169.cell1354, Batch0169.tau1354, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy010130 | hy010130
            · have hs0101301 : InSquare (-37/320) (-119/320) (1/320) tau := by
                convert childLR hs010130 hx010130 hy010130 using 1 <;> norm_num
              rcases le_total tau.re (-37/320 : ℝ) with hx0101301 | hx0101301
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101301 | hy0101301
                · have hs01013010 : InSquare (-15/128) (-239/640) (1/640) tau := by
                    convert childLL hs0101301 hx0101301 hy0101301 using 1 <;> norm_num
                  exact Batch0337.cell2701.sound htau (by
                    simp only [Batch0337.cell2701, Batch0337.tau2701, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013010 (by positivity) using 1 <;> norm_num)
                · have hs01013012 : InSquare (-15/128) (-237/640) (1/640) tau := by
                    convert childUL hs0101301 hx0101301 hy0101301 using 1 <;> norm_num
                  exact Batch0337.cell2703.sound htau (by
                    simp only [Batch0337.cell2703, Batch0337.tau2703, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101301 | hy0101301
                · have hs01013011 : InSquare (-73/640) (-239/640) (1/640) tau := by
                    convert childLR hs0101301 hx0101301 hy0101301 using 1 <;> norm_num
                  exact Batch0337.cell2702.sound htau (by
                    simp only [Batch0337.cell2702, Batch0337.tau2702, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013011 (by positivity) using 1 <;> norm_num)
                · have hs01013013 : InSquare (-73/640) (-237/640) (1/640) tau := by
                    convert childUR hs0101301 hx0101301 hy0101301 using 1 <;> norm_num
                  exact Batch0338.cell2704.sound htau (by
                    simp only [Batch0338.cell2704, Batch0338.tau2704, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013013 (by positivity) using 1 <;> norm_num)
            · have hs0101303 : InSquare (-37/320) (-117/320) (1/320) tau := by
                convert childUR hs010130 hx010130 hy010130 using 1 <;> norm_num
              exact Batch0169.cell1355.sound htau (by
                simp only [Batch0169.cell1355, Batch0169.tau1355, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101303 (by positivity) using 1 <;> norm_num)
        · have hs010132 : InSquare (-19/160) (-57/160) (1/160) tau := by
            convert childUL hs01013 hx01013 hy01013 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx010132 | hx010132
          · rcases le_total tau.im (-57/160 : ℝ) with hy010132 | hy010132
            · have hs0101320 : InSquare (-39/320) (-23/64) (1/320) tau := by
                convert childLL hs010132 hx010132 hy010132 using 1 <;> norm_num
              exact Batch0169.cell1358.sound htau (by
                simp only [Batch0169.cell1358, Batch0169.tau1358, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101320 (by positivity) using 1 <;> norm_num)
            · have hs0101322 : InSquare (-39/320) (-113/320) (1/320) tau := by
                convert childUL hs010132 hx010132 hy010132 using 1 <;> norm_num
              exact Batch0170.cell1360.sound htau (by
                simp only [Batch0170.cell1360, Batch0170.tau1360, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy010132 | hy010132
            · have hs0101321 : InSquare (-37/320) (-23/64) (1/320) tau := by
                convert childLR hs010132 hx010132 hy010132 using 1 <;> norm_num
              exact Batch0169.cell1359.sound htau (by
                simp only [Batch0169.cell1359, Batch0169.tau1359, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101321 (by positivity) using 1 <;> norm_num)
            · have hs0101323 : InSquare (-37/320) (-113/320) (1/320) tau := by
                convert childUR hs010132 hx010132 hy010132 using 1 <;> norm_num
              exact Batch0170.cell1361.sound htau (by
                simp only [Batch0170.cell1361, Batch0170.tau1361, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01013 | hy01013
        · have hs010131 : InSquare (-17/160) (-59/160) (1/160) tau := by
            convert childLR hs01013 hx01013 hy01013 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx010131 | hx010131
          · rcases le_total tau.im (-59/160 : ℝ) with hy010131 | hy010131
            · have hs0101310 : InSquare (-7/64) (-119/320) (1/320) tau := by
                convert childLL hs010131 hx010131 hy010131 using 1 <;> norm_num
              rcases le_total tau.re (-7/64 : ℝ) with hx0101310 | hx0101310
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101310 | hy0101310
                · have hs01013100 : InSquare (-71/640) (-239/640) (1/640) tau := by
                    convert childLL hs0101310 hx0101310 hy0101310 using 1 <;> norm_num
                  exact Batch0338.cell2705.sound htau (by
                    simp only [Batch0338.cell2705, Batch0338.tau2705, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013100 (by positivity) using 1 <;> norm_num)
                · have hs01013102 : InSquare (-71/640) (-237/640) (1/640) tau := by
                    convert childUL hs0101310 hx0101310 hy0101310 using 1 <;> norm_num
                  exact Batch0338.cell2707.sound htau (by
                    simp only [Batch0338.cell2707, Batch0338.tau2707, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101310 | hy0101310
                · have hs01013101 : InSquare (-69/640) (-239/640) (1/640) tau := by
                    convert childLR hs0101310 hx0101310 hy0101310 using 1 <;> norm_num
                  exact Batch0338.cell2706.sound htau (by
                    simp only [Batch0338.cell2706, Batch0338.tau2706, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013101 (by positivity) using 1 <;> norm_num)
                · have hs01013103 : InSquare (-69/640) (-237/640) (1/640) tau := by
                    convert childUR hs0101310 hx0101310 hy0101310 using 1 <;> norm_num
                  exact Batch0338.cell2708.sound htau (by
                    simp only [Batch0338.cell2708, Batch0338.tau2708, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013103 (by positivity) using 1 <;> norm_num)
            · have hs0101312 : InSquare (-7/64) (-117/320) (1/320) tau := by
                convert childUL hs010131 hx010131 hy010131 using 1 <;> norm_num
              exact Batch0169.cell1356.sound htau (by
                simp only [Batch0169.cell1356, Batch0169.tau1356, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy010131 | hy010131
            · have hs0101311 : InSquare (-33/320) (-119/320) (1/320) tau := by
                convert childLR hs010131 hx010131 hy010131 using 1 <;> norm_num
              rcases le_total tau.re (-33/320 : ℝ) with hx0101311 | hx0101311
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101311 | hy0101311
                · have hs01013110 : InSquare (-67/640) (-239/640) (1/640) tau := by
                    convert childLL hs0101311 hx0101311 hy0101311 using 1 <;> norm_num
                  exact Batch0338.cell2709.sound htau (by
                    simp only [Batch0338.cell2709, Batch0338.tau2709, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013110 (by positivity) using 1 <;> norm_num)
                · have hs01013112 : InSquare (-67/640) (-237/640) (1/640) tau := by
                    convert childUL hs0101311 hx0101311 hy0101311 using 1 <;> norm_num
                  exact Batch0338.cell2711.sound htau (by
                    simp only [Batch0338.cell2711, Batch0338.tau2711, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101311 | hy0101311
                · have hs01013111 : InSquare (-13/128) (-239/640) (1/640) tau := by
                    convert childLR hs0101311 hx0101311 hy0101311 using 1 <;> norm_num
                  exact Batch0338.cell2710.sound htau (by
                    simp only [Batch0338.cell2710, Batch0338.tau2710, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013111 (by positivity) using 1 <;> norm_num)
                · have hs01013113 : InSquare (-13/128) (-237/640) (1/640) tau := by
                    convert childUR hs0101311 hx0101311 hy0101311 using 1 <;> norm_num
                  exact Batch0339.cell2712.sound htau (by
                    simp only [Batch0339.cell2712, Batch0339.tau2712, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013113 (by positivity) using 1 <;> norm_num)
            · have hs0101313 : InSquare (-33/320) (-117/320) (1/320) tau := by
                convert childUR hs010131 hx010131 hy010131 using 1 <;> norm_num
              exact Batch0169.cell1357.sound htau (by
                simp only [Batch0169.cell1357, Batch0169.tau1357, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101313 (by positivity) using 1 <;> norm_num)
        · have hs010133 : InSquare (-17/160) (-57/160) (1/160) tau := by
            convert childUR hs01013 hx01013 hy01013 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx010133 | hx010133
          · rcases le_total tau.im (-57/160 : ℝ) with hy010133 | hy010133
            · have hs0101330 : InSquare (-7/64) (-23/64) (1/320) tau := by
                convert childLL hs010133 hx010133 hy010133 using 1 <;> norm_num
              exact Batch0170.cell1362.sound htau (by
                simp only [Batch0170.cell1362, Batch0170.tau1362, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101330 (by positivity) using 1 <;> norm_num)
            · have hs0101332 : InSquare (-7/64) (-113/320) (1/320) tau := by
                convert childUL hs010133 hx010133 hy010133 using 1 <;> norm_num
              exact Batch0170.cell1364.sound htau (by
                simp only [Batch0170.cell1364, Batch0170.tau1364, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy010133 | hy010133
            · have hs0101331 : InSquare (-33/320) (-23/64) (1/320) tau := by
                convert childLR hs010133 hx010133 hy010133 using 1 <;> norm_num
              exact Batch0170.cell1363.sound htau (by
                simp only [Batch0170.cell1363, Batch0170.tau1363, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101331 (by positivity) using 1 <;> norm_num)
            · have hs0101333 : InSquare (-33/320) (-113/320) (1/320) tau := by
                convert childUR hs010133 hx010133 hy010133 using 1 <;> norm_num
              exact Batch0170.cell1365.sound htau (by
                simp only [Batch0170.cell1365, Batch0170.tau1365, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0101

end


