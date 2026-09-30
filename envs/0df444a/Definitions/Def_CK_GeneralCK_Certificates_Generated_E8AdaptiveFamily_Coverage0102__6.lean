-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage0102__6
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage0102__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:24:51.398628+00:00
-- url     : https://prove2.me/theorems/e68d4155-611d-4b14-be80-7487f41339ba
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0102 (+5 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0103, GeneralCK.Certific…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0102 (+5 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0103, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0110, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0111, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0112, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0113)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0102 (+5 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0103, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0110, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0111, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0112, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0113)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0102 (+5 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0103, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0110, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0111, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0112, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0113) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0102 (+5 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0103, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0110, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0111, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0112, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0113).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0049
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0170
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0171
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0172
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0173
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0174
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0175
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0176
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0177
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0339
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0340
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0050
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0178
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0179
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0180
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0181
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0182
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0183
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0184
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0185
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0341
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0342
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0343
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0344
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0345
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0346
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0347
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0348
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0349
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0350
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0186
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0187
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0188
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0189
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0190
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0351
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0352
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0353
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0354
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0355
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0356
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0357
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0358
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0359
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0360
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0051
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0052
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0191
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0192
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0053
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0054

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0102 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0102

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx0102 | hx0102
  · rcases le_total tau.im (-13/40 : ℝ) with hy0102 | hy0102
    · have hs01020 : InSquare (-3/16) (-27/80) (1/80) tau := by
        convert childLL hs hx0102 hy0102 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx01020 | hx01020
      · rcases le_total tau.im (-27/80 : ℝ) with hy01020 | hy01020
        · have hs010200 : InSquare (-31/160) (-11/32) (1/160) tau := by
            convert childLL hs01020 hx01020 hy01020 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx010200 | hx010200
          · rcases le_total tau.im (-11/32 : ℝ) with hy010200 | hy010200
            · have hs0102000 : InSquare (-63/320) (-111/320) (1/320) tau := by
                convert childLL hs010200 hx010200 hy010200 using 1 <;> norm_num
              rcases le_total tau.re (-63/320 : ℝ) with hx0102000 | hx0102000
              · rcases le_total tau.im (-111/320 : ℝ) with hy0102000 | hy0102000
                · have hs01020000 : InSquare (-127/640) (-223/640) (1/640) tau := by
                    convert childLL hs0102000 hx0102000 hy0102000 using 1 <;> norm_num
                  exact Batch0339.cell2713.sound htau (by
                    simp only [Batch0339.cell2713, Batch0339.tau2713, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020000 (by positivity) using 1 <;> norm_num)
                · have hs01020002 : InSquare (-127/640) (-221/640) (1/640) tau := by
                    convert childUL hs0102000 hx0102000 hy0102000 using 1 <;> norm_num
                  exact Batch0339.cell2715.sound htau (by
                    simp only [Batch0339.cell2715, Batch0339.tau2715, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-111/320 : ℝ) with hy0102000 | hy0102000
                · have hs01020001 : InSquare (-25/128) (-223/640) (1/640) tau := by
                    convert childLR hs0102000 hx0102000 hy0102000 using 1 <;> norm_num
                  exact Batch0339.cell2714.sound htau (by
                    simp only [Batch0339.cell2714, Batch0339.tau2714, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020001 (by positivity) using 1 <;> norm_num)
                · have hs01020003 : InSquare (-25/128) (-221/640) (1/640) tau := by
                    convert childUR hs0102000 hx0102000 hy0102000 using 1 <;> norm_num
                  exact Batch0339.cell2716.sound htau (by
                    simp only [Batch0339.cell2716, Batch0339.tau2716, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020003 (by positivity) using 1 <;> norm_num)
            · have hs0102002 : InSquare (-63/320) (-109/320) (1/320) tau := by
                convert childUL hs010200 hx010200 hy010200 using 1 <;> norm_num
              exact Batch0170.cell1366.sound htau (by
                simp only [Batch0170.cell1366, Batch0170.tau1366, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010200 | hy010200
            · have hs0102001 : InSquare (-61/320) (-111/320) (1/320) tau := by
                convert childLR hs010200 hx010200 hy010200 using 1 <;> norm_num
              rcases le_total tau.re (-61/320 : ℝ) with hx0102001 | hx0102001
              · rcases le_total tau.im (-111/320 : ℝ) with hy0102001 | hy0102001
                · have hs01020010 : InSquare (-123/640) (-223/640) (1/640) tau := by
                    convert childLL hs0102001 hx0102001 hy0102001 using 1 <;> norm_num
                  exact Batch0339.cell2717.sound htau (by
                    simp only [Batch0339.cell2717, Batch0339.tau2717, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020010 (by positivity) using 1 <;> norm_num)
                · have hs01020012 : InSquare (-123/640) (-221/640) (1/640) tau := by
                    convert childUL hs0102001 hx0102001 hy0102001 using 1 <;> norm_num
                  exact Batch0339.cell2719.sound htau (by
                    simp only [Batch0339.cell2719, Batch0339.tau2719, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-111/320 : ℝ) with hy0102001 | hy0102001
                · have hs01020011 : InSquare (-121/640) (-223/640) (1/640) tau := by
                    convert childLR hs0102001 hx0102001 hy0102001 using 1 <;> norm_num
                  exact Batch0339.cell2718.sound htau (by
                    simp only [Batch0339.cell2718, Batch0339.tau2718, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020011 (by positivity) using 1 <;> norm_num)
                · have hs01020013 : InSquare (-121/640) (-221/640) (1/640) tau := by
                    convert childUR hs0102001 hx0102001 hy0102001 using 1 <;> norm_num
                  exact Batch0340.cell2720.sound htau (by
                    simp only [Batch0340.cell2720, Batch0340.tau2720, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020013 (by positivity) using 1 <;> norm_num)
            · have hs0102003 : InSquare (-61/320) (-109/320) (1/320) tau := by
                convert childUR hs010200 hx010200 hy010200 using 1 <;> norm_num
              exact Batch0170.cell1367.sound htau (by
                simp only [Batch0170.cell1367, Batch0170.tau1367, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102003 (by positivity) using 1 <;> norm_num)
        · have hs010202 : InSquare (-31/160) (-53/160) (1/160) tau := by
            convert childUL hs01020 hx01020 hy01020 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx010202 | hx010202
          · rcases le_total tau.im (-53/160 : ℝ) with hy010202 | hy010202
            · have hs0102020 : InSquare (-63/320) (-107/320) (1/320) tau := by
                convert childLL hs010202 hx010202 hy010202 using 1 <;> norm_num
              exact Batch0171.cell1372.sound htau (by
                simp only [Batch0171.cell1372, Batch0171.tau1372, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102020 (by positivity) using 1 <;> norm_num)
            · have hs0102022 : InSquare (-63/320) (-21/64) (1/320) tau := by
                convert childUL hs010202 hx010202 hy010202 using 1 <;> norm_num
              exact Batch0171.cell1374.sound htau (by
                simp only [Batch0171.cell1374, Batch0171.tau1374, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy010202 | hy010202
            · have hs0102021 : InSquare (-61/320) (-107/320) (1/320) tau := by
                convert childLR hs010202 hx010202 hy010202 using 1 <;> norm_num
              exact Batch0171.cell1373.sound htau (by
                simp only [Batch0171.cell1373, Batch0171.tau1373, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102021 (by positivity) using 1 <;> norm_num)
            · have hs0102023 : InSquare (-61/320) (-21/64) (1/320) tau := by
                convert childUR hs010202 hx010202 hy010202 using 1 <;> norm_num
              exact Batch0171.cell1375.sound htau (by
                simp only [Batch0171.cell1375, Batch0171.tau1375, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01020 | hy01020
        · have hs010201 : InSquare (-29/160) (-11/32) (1/160) tau := by
            convert childLR hs01020 hx01020 hy01020 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx010201 | hx010201
          · rcases le_total tau.im (-11/32 : ℝ) with hy010201 | hy010201
            · have hs0102010 : InSquare (-59/320) (-111/320) (1/320) tau := by
                convert childLL hs010201 hx010201 hy010201 using 1 <;> norm_num
              exact Batch0171.cell1368.sound htau (by
                simp only [Batch0171.cell1368, Batch0171.tau1368, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102010 (by positivity) using 1 <;> norm_num)
            · have hs0102012 : InSquare (-59/320) (-109/320) (1/320) tau := by
                convert childUL hs010201 hx010201 hy010201 using 1 <;> norm_num
              exact Batch0171.cell1370.sound htau (by
                simp only [Batch0171.cell1370, Batch0171.tau1370, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010201 | hy010201
            · have hs0102011 : InSquare (-57/320) (-111/320) (1/320) tau := by
                convert childLR hs010201 hx010201 hy010201 using 1 <;> norm_num
              exact Batch0171.cell1369.sound htau (by
                simp only [Batch0171.cell1369, Batch0171.tau1369, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102011 (by positivity) using 1 <;> norm_num)
            · have hs0102013 : InSquare (-57/320) (-109/320) (1/320) tau := by
                convert childUR hs010201 hx010201 hy010201 using 1 <;> norm_num
              exact Batch0171.cell1371.sound htau (by
                simp only [Batch0171.cell1371, Batch0171.tau1371, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102013 (by positivity) using 1 <;> norm_num)
        · have hs010203 : InSquare (-29/160) (-53/160) (1/160) tau := by
            convert childUR hs01020 hx01020 hy01020 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx010203 | hx010203
          · rcases le_total tau.im (-53/160 : ℝ) with hy010203 | hy010203
            · have hs0102030 : InSquare (-59/320) (-107/320) (1/320) tau := by
                convert childLL hs010203 hx010203 hy010203 using 1 <;> norm_num
              exact Batch0172.cell1376.sound htau (by
                simp only [Batch0172.cell1376, Batch0172.tau1376, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102030 (by positivity) using 1 <;> norm_num)
            · have hs0102032 : InSquare (-59/320) (-21/64) (1/320) tau := by
                convert childUL hs010203 hx010203 hy010203 using 1 <;> norm_num
              exact Batch0172.cell1378.sound htau (by
                simp only [Batch0172.cell1378, Batch0172.tau1378, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy010203 | hy010203
            · have hs0102031 : InSquare (-57/320) (-107/320) (1/320) tau := by
                convert childLR hs010203 hx010203 hy010203 using 1 <;> norm_num
              exact Batch0172.cell1377.sound htau (by
                simp only [Batch0172.cell1377, Batch0172.tau1377, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102031 (by positivity) using 1 <;> norm_num)
            · have hs0102033 : InSquare (-57/320) (-21/64) (1/320) tau := by
                convert childUR hs010203 hx010203 hy010203 using 1 <;> norm_num
              exact Batch0172.cell1379.sound htau (by
                simp only [Batch0172.cell1379, Batch0172.tau1379, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102033 (by positivity) using 1 <;> norm_num)
    · have hs01022 : InSquare (-3/16) (-5/16) (1/80) tau := by
        convert childUL hs hx0102 hy0102 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx01022 | hx01022
      · rcases le_total tau.im (-5/16 : ℝ) with hy01022 | hy01022
        · have hs010220 : InSquare (-31/160) (-51/160) (1/160) tau := by
            convert childLL hs01022 hx01022 hy01022 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx010220 | hx010220
          · rcases le_total tau.im (-51/160 : ℝ) with hy010220 | hy010220
            · have hs0102200 : InSquare (-63/320) (-103/320) (1/320) tau := by
                convert childLL hs010220 hx010220 hy010220 using 1 <;> norm_num
              exact Batch0174.cell1396.sound htau (by
                simp only [Batch0174.cell1396, Batch0174.tau1396, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102200 (by positivity) using 1 <;> norm_num)
            · have hs0102202 : InSquare (-63/320) (-101/320) (1/320) tau := by
                convert childUL hs010220 hx010220 hy010220 using 1 <;> norm_num
              exact Batch0174.cell1398.sound htau (by
                simp only [Batch0174.cell1398, Batch0174.tau1398, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy010220 | hy010220
            · have hs0102201 : InSquare (-61/320) (-103/320) (1/320) tau := by
                convert childLR hs010220 hx010220 hy010220 using 1 <;> norm_num
              exact Batch0174.cell1397.sound htau (by
                simp only [Batch0174.cell1397, Batch0174.tau1397, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102201 (by positivity) using 1 <;> norm_num)
            · have hs0102203 : InSquare (-61/320) (-101/320) (1/320) tau := by
                convert childUR hs010220 hx010220 hy010220 using 1 <;> norm_num
              exact Batch0174.cell1399.sound htau (by
                simp only [Batch0174.cell1399, Batch0174.tau1399, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102203 (by positivity) using 1 <;> norm_num)
        · have hs010222 : InSquare (-31/160) (-49/160) (1/160) tau := by
            convert childUL hs01022 hx01022 hy01022 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx010222 | hx010222
          · rcases le_total tau.im (-49/160 : ℝ) with hy010222 | hy010222
            · have hs0102220 : InSquare (-63/320) (-99/320) (1/320) tau := by
                convert childLL hs010222 hx010222 hy010222 using 1 <;> norm_num
              exact Batch0175.cell1404.sound htau (by
                simp only [Batch0175.cell1404, Batch0175.tau1404, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102220 (by positivity) using 1 <;> norm_num)
            · have hs0102222 : InSquare (-63/320) (-97/320) (1/320) tau := by
                convert childUL hs010222 hx010222 hy010222 using 1 <;> norm_num
              exact Batch0175.cell1406.sound htau (by
                simp only [Batch0175.cell1406, Batch0175.tau1406, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy010222 | hy010222
            · have hs0102221 : InSquare (-61/320) (-99/320) (1/320) tau := by
                convert childLR hs010222 hx010222 hy010222 using 1 <;> norm_num
              exact Batch0175.cell1405.sound htau (by
                simp only [Batch0175.cell1405, Batch0175.tau1405, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102221 (by positivity) using 1 <;> norm_num)
            · have hs0102223 : InSquare (-61/320) (-97/320) (1/320) tau := by
                convert childUR hs010222 hx010222 hy010222 using 1 <;> norm_num
              exact Batch0175.cell1407.sound htau (by
                simp only [Batch0175.cell1407, Batch0175.tau1407, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01022 | hy01022
        · have hs010221 : InSquare (-29/160) (-51/160) (1/160) tau := by
            convert childLR hs01022 hx01022 hy01022 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx010221 | hx010221
          · rcases le_total tau.im (-51/160 : ℝ) with hy010221 | hy010221
            · have hs0102210 : InSquare (-59/320) (-103/320) (1/320) tau := by
                convert childLL hs010221 hx010221 hy010221 using 1 <;> norm_num
              exact Batch0175.cell1400.sound htau (by
                simp only [Batch0175.cell1400, Batch0175.tau1400, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102210 (by positivity) using 1 <;> norm_num)
            · have hs0102212 : InSquare (-59/320) (-101/320) (1/320) tau := by
                convert childUL hs010221 hx010221 hy010221 using 1 <;> norm_num
              exact Batch0175.cell1402.sound htau (by
                simp only [Batch0175.cell1402, Batch0175.tau1402, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy010221 | hy010221
            · have hs0102211 : InSquare (-57/320) (-103/320) (1/320) tau := by
                convert childLR hs010221 hx010221 hy010221 using 1 <;> norm_num
              exact Batch0175.cell1401.sound htau (by
                simp only [Batch0175.cell1401, Batch0175.tau1401, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102211 (by positivity) using 1 <;> norm_num)
            · have hs0102213 : InSquare (-57/320) (-101/320) (1/320) tau := by
                convert childUR hs010221 hx010221 hy010221 using 1 <;> norm_num
              exact Batch0175.cell1403.sound htau (by
                simp only [Batch0175.cell1403, Batch0175.tau1403, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102213 (by positivity) using 1 <;> norm_num)
        · have hs010223 : InSquare (-29/160) (-49/160) (1/160) tau := by
            convert childUR hs01022 hx01022 hy01022 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx010223 | hx010223
          · rcases le_total tau.im (-49/160 : ℝ) with hy010223 | hy010223
            · have hs0102230 : InSquare (-59/320) (-99/320) (1/320) tau := by
                convert childLL hs010223 hx010223 hy010223 using 1 <;> norm_num
              exact Batch0176.cell1408.sound htau (by
                simp only [Batch0176.cell1408, Batch0176.tau1408, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102230 (by positivity) using 1 <;> norm_num)
            · have hs0102232 : InSquare (-59/320) (-97/320) (1/320) tau := by
                convert childUL hs010223 hx010223 hy010223 using 1 <;> norm_num
              exact Batch0176.cell1410.sound htau (by
                simp only [Batch0176.cell1410, Batch0176.tau1410, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy010223 | hy010223
            · have hs0102231 : InSquare (-57/320) (-99/320) (1/320) tau := by
                convert childLR hs010223 hx010223 hy010223 using 1 <;> norm_num
              exact Batch0176.cell1409.sound htau (by
                simp only [Batch0176.cell1409, Batch0176.tau1409, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102231 (by positivity) using 1 <;> norm_num)
            · have hs0102233 : InSquare (-57/320) (-97/320) (1/320) tau := by
                convert childUR hs010223 hx010223 hy010223 using 1 <;> norm_num
              exact Batch0176.cell1411.sound htau (by
                simp only [Batch0176.cell1411, Batch0176.tau1411, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy0102 | hy0102
    · have hs01021 : InSquare (-13/80) (-27/80) (1/80) tau := by
        convert childLR hs hx0102 hy0102 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx01021 | hx01021
      · rcases le_total tau.im (-27/80 : ℝ) with hy01021 | hy01021
        · have hs010210 : InSquare (-27/160) (-11/32) (1/160) tau := by
            convert childLL hs01021 hx01021 hy01021 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx010210 | hx010210
          · rcases le_total tau.im (-11/32 : ℝ) with hy010210 | hy010210
            · have hs0102100 : InSquare (-11/64) (-111/320) (1/320) tau := by
                convert childLL hs010210 hx010210 hy010210 using 1 <;> norm_num
              exact Batch0172.cell1380.sound htau (by
                simp only [Batch0172.cell1380, Batch0172.tau1380, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102100 (by positivity) using 1 <;> norm_num)
            · have hs0102102 : InSquare (-11/64) (-109/320) (1/320) tau := by
                convert childUL hs010210 hx010210 hy010210 using 1 <;> norm_num
              exact Batch0172.cell1382.sound htau (by
                simp only [Batch0172.cell1382, Batch0172.tau1382, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010210 | hy010210
            · have hs0102101 : InSquare (-53/320) (-111/320) (1/320) tau := by
                convert childLR hs010210 hx010210 hy010210 using 1 <;> norm_num
              exact Batch0172.cell1381.sound htau (by
                simp only [Batch0172.cell1381, Batch0172.tau1381, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102101 (by positivity) using 1 <;> norm_num)
            · have hs0102103 : InSquare (-53/320) (-109/320) (1/320) tau := by
                convert childUR hs010210 hx010210 hy010210 using 1 <;> norm_num
              exact Batch0172.cell1383.sound htau (by
                simp only [Batch0172.cell1383, Batch0172.tau1383, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102103 (by positivity) using 1 <;> norm_num)
        · have hs010212 : InSquare (-27/160) (-53/160) (1/160) tau := by
            convert childUL hs01021 hx01021 hy01021 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx010212 | hx010212
          · rcases le_total tau.im (-53/160 : ℝ) with hy010212 | hy010212
            · have hs0102120 : InSquare (-11/64) (-107/320) (1/320) tau := by
                convert childLL hs010212 hx010212 hy010212 using 1 <;> norm_num
              exact Batch0173.cell1388.sound htau (by
                simp only [Batch0173.cell1388, Batch0173.tau1388, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102120 (by positivity) using 1 <;> norm_num)
            · have hs0102122 : InSquare (-11/64) (-21/64) (1/320) tau := by
                convert childUL hs010212 hx010212 hy010212 using 1 <;> norm_num
              exact Batch0173.cell1390.sound htau (by
                simp only [Batch0173.cell1390, Batch0173.tau1390, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy010212 | hy010212
            · have hs0102121 : InSquare (-53/320) (-107/320) (1/320) tau := by
                convert childLR hs010212 hx010212 hy010212 using 1 <;> norm_num
              exact Batch0173.cell1389.sound htau (by
                simp only [Batch0173.cell1389, Batch0173.tau1389, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102121 (by positivity) using 1 <;> norm_num)
            · have hs0102123 : InSquare (-53/320) (-21/64) (1/320) tau := by
                convert childUR hs010212 hx010212 hy010212 using 1 <;> norm_num
              exact Batch0173.cell1391.sound htau (by
                simp only [Batch0173.cell1391, Batch0173.tau1391, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01021 | hy01021
        · have hs010211 : InSquare (-5/32) (-11/32) (1/160) tau := by
            convert childLR hs01021 hx01021 hy01021 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx010211 | hx010211
          · rcases le_total tau.im (-11/32 : ℝ) with hy010211 | hy010211
            · have hs0102110 : InSquare (-51/320) (-111/320) (1/320) tau := by
                convert childLL hs010211 hx010211 hy010211 using 1 <;> norm_num
              exact Batch0173.cell1384.sound htau (by
                simp only [Batch0173.cell1384, Batch0173.tau1384, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102110 (by positivity) using 1 <;> norm_num)
            · have hs0102112 : InSquare (-51/320) (-109/320) (1/320) tau := by
                convert childUL hs010211 hx010211 hy010211 using 1 <;> norm_num
              exact Batch0173.cell1386.sound htau (by
                simp only [Batch0173.cell1386, Batch0173.tau1386, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010211 | hy010211
            · have hs0102111 : InSquare (-49/320) (-111/320) (1/320) tau := by
                convert childLR hs010211 hx010211 hy010211 using 1 <;> norm_num
              exact Batch0173.cell1385.sound htau (by
                simp only [Batch0173.cell1385, Batch0173.tau1385, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102111 (by positivity) using 1 <;> norm_num)
            · have hs0102113 : InSquare (-49/320) (-109/320) (1/320) tau := by
                convert childUR hs010211 hx010211 hy010211 using 1 <;> norm_num
              exact Batch0173.cell1387.sound htau (by
                simp only [Batch0173.cell1387, Batch0173.tau1387, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102113 (by positivity) using 1 <;> norm_num)
        · have hs010213 : InSquare (-5/32) (-53/160) (1/160) tau := by
            convert childUR hs01021 hx01021 hy01021 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx010213 | hx010213
          · rcases le_total tau.im (-53/160 : ℝ) with hy010213 | hy010213
            · have hs0102130 : InSquare (-51/320) (-107/320) (1/320) tau := by
                convert childLL hs010213 hx010213 hy010213 using 1 <;> norm_num
              exact Batch0174.cell1392.sound htau (by
                simp only [Batch0174.cell1392, Batch0174.tau1392, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102130 (by positivity) using 1 <;> norm_num)
            · have hs0102132 : InSquare (-51/320) (-21/64) (1/320) tau := by
                convert childUL hs010213 hx010213 hy010213 using 1 <;> norm_num
              exact Batch0174.cell1394.sound htau (by
                simp only [Batch0174.cell1394, Batch0174.tau1394, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy010213 | hy010213
            · have hs0102131 : InSquare (-49/320) (-107/320) (1/320) tau := by
                convert childLR hs010213 hx010213 hy010213 using 1 <;> norm_num
              exact Batch0174.cell1393.sound htau (by
                simp only [Batch0174.cell1393, Batch0174.tau1393, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102131 (by positivity) using 1 <;> norm_num)
            · have hs0102133 : InSquare (-49/320) (-21/64) (1/320) tau := by
                convert childUR hs010213 hx010213 hy010213 using 1 <;> norm_num
              exact Batch0174.cell1395.sound htau (by
                simp only [Batch0174.cell1395, Batch0174.tau1395, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102133 (by positivity) using 1 <;> norm_num)
    · have hs01023 : InSquare (-13/80) (-5/16) (1/80) tau := by
        convert childUR hs hx0102 hy0102 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx01023 | hx01023
      · rcases le_total tau.im (-5/16 : ℝ) with hy01023 | hy01023
        · have hs010230 : InSquare (-27/160) (-51/160) (1/160) tau := by
            convert childLL hs01023 hx01023 hy01023 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx010230 | hx010230
          · rcases le_total tau.im (-51/160 : ℝ) with hy010230 | hy010230
            · have hs0102300 : InSquare (-11/64) (-103/320) (1/320) tau := by
                convert childLL hs010230 hx010230 hy010230 using 1 <;> norm_num
              exact Batch0176.cell1412.sound htau (by
                simp only [Batch0176.cell1412, Batch0176.tau1412, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102300 (by positivity) using 1 <;> norm_num)
            · have hs0102302 : InSquare (-11/64) (-101/320) (1/320) tau := by
                convert childUL hs010230 hx010230 hy010230 using 1 <;> norm_num
              exact Batch0176.cell1414.sound htau (by
                simp only [Batch0176.cell1414, Batch0176.tau1414, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy010230 | hy010230
            · have hs0102301 : InSquare (-53/320) (-103/320) (1/320) tau := by
                convert childLR hs010230 hx010230 hy010230 using 1 <;> norm_num
              exact Batch0176.cell1413.sound htau (by
                simp only [Batch0176.cell1413, Batch0176.tau1413, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102301 (by positivity) using 1 <;> norm_num)
            · have hs0102303 : InSquare (-53/320) (-101/320) (1/320) tau := by
                convert childUR hs010230 hx010230 hy010230 using 1 <;> norm_num
              exact Batch0176.cell1415.sound htau (by
                simp only [Batch0176.cell1415, Batch0176.tau1415, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102303 (by positivity) using 1 <;> norm_num)
        · have hs010232 : InSquare (-27/160) (-49/160) (1/160) tau := by
            convert childUL hs01023 hx01023 hy01023 using 1 <;> norm_num
          exact Batch0049.cell0393.sound htau (by
            simp only [Batch0049.cell0393, Batch0049.tau0393, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01023 | hy01023
        · have hs010231 : InSquare (-5/32) (-51/160) (1/160) tau := by
            convert childLR hs01023 hx01023 hy01023 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx010231 | hx010231
          · rcases le_total tau.im (-51/160 : ℝ) with hy010231 | hy010231
            · have hs0102310 : InSquare (-51/320) (-103/320) (1/320) tau := by
                convert childLL hs010231 hx010231 hy010231 using 1 <;> norm_num
              exact Batch0177.cell1416.sound htau (by
                simp only [Batch0177.cell1416, Batch0177.tau1416, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102310 (by positivity) using 1 <;> norm_num)
            · have hs0102312 : InSquare (-51/320) (-101/320) (1/320) tau := by
                convert childUL hs010231 hx010231 hy010231 using 1 <;> norm_num
              exact Batch0177.cell1418.sound htau (by
                simp only [Batch0177.cell1418, Batch0177.tau1418, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy010231 | hy010231
            · have hs0102311 : InSquare (-49/320) (-103/320) (1/320) tau := by
                convert childLR hs010231 hx010231 hy010231 using 1 <;> norm_num
              exact Batch0177.cell1417.sound htau (by
                simp only [Batch0177.cell1417, Batch0177.tau1417, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102311 (by positivity) using 1 <;> norm_num)
            · have hs0102313 : InSquare (-49/320) (-101/320) (1/320) tau := by
                convert childUR hs010231 hx010231 hy010231 using 1 <;> norm_num
              exact Batch0177.cell1419.sound htau (by
                simp only [Batch0177.cell1419, Batch0177.tau1419, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102313 (by positivity) using 1 <;> norm_num)
        · have hs010233 : InSquare (-5/32) (-49/160) (1/160) tau := by
            convert childUR hs01023 hx01023 hy01023 using 1 <;> norm_num
          exact Batch0049.cell0394.sound htau (by
            simp only [Batch0049.cell0394, Batch0049.tau0394, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0102

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0103 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0103

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx0103 | hx0103
  · rcases le_total tau.im (-13/40 : ℝ) with hy0103 | hy0103
    · have hs01030 : InSquare (-11/80) (-27/80) (1/80) tau := by
        convert childLL hs hx0103 hy0103 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx01030 | hx01030
      · rcases le_total tau.im (-27/80 : ℝ) with hy01030 | hy01030
        · have hs010300 : InSquare (-23/160) (-11/32) (1/160) tau := by
            convert childLL hs01030 hx01030 hy01030 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx010300 | hx010300
          · rcases le_total tau.im (-11/32 : ℝ) with hy010300 | hy010300
            · have hs0103000 : InSquare (-47/320) (-111/320) (1/320) tau := by
                convert childLL hs010300 hx010300 hy010300 using 1 <;> norm_num
              exact Batch0177.cell1420.sound htau (by
                simp only [Batch0177.cell1420, Batch0177.tau1420, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103000 (by positivity) using 1 <;> norm_num)
            · have hs0103002 : InSquare (-47/320) (-109/320) (1/320) tau := by
                convert childUL hs010300 hx010300 hy010300 using 1 <;> norm_num
              exact Batch0177.cell1422.sound htau (by
                simp only [Batch0177.cell1422, Batch0177.tau1422, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010300 | hy010300
            · have hs0103001 : InSquare (-9/64) (-111/320) (1/320) tau := by
                convert childLR hs010300 hx010300 hy010300 using 1 <;> norm_num
              exact Batch0177.cell1421.sound htau (by
                simp only [Batch0177.cell1421, Batch0177.tau1421, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103001 (by positivity) using 1 <;> norm_num)
            · have hs0103003 : InSquare (-9/64) (-109/320) (1/320) tau := by
                convert childUR hs010300 hx010300 hy010300 using 1 <;> norm_num
              exact Batch0177.cell1423.sound htau (by
                simp only [Batch0177.cell1423, Batch0177.tau1423, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103003 (by positivity) using 1 <;> norm_num)
        · have hs010302 : InSquare (-23/160) (-53/160) (1/160) tau := by
            convert childUL hs01030 hx01030 hy01030 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx010302 | hx010302
          · rcases le_total tau.im (-53/160 : ℝ) with hy010302 | hy010302
            · have hs0103020 : InSquare (-47/320) (-107/320) (1/320) tau := by
                convert childLL hs010302 hx010302 hy010302 using 1 <;> norm_num
              exact Batch0178.cell1428.sound htau (by
                simp only [Batch0178.cell1428, Batch0178.tau1428, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103020 (by positivity) using 1 <;> norm_num)
            · have hs0103022 : InSquare (-47/320) (-21/64) (1/320) tau := by
                convert childUL hs010302 hx010302 hy010302 using 1 <;> norm_num
              exact Batch0178.cell1430.sound htau (by
                simp only [Batch0178.cell1430, Batch0178.tau1430, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy010302 | hy010302
            · have hs0103021 : InSquare (-9/64) (-107/320) (1/320) tau := by
                convert childLR hs010302 hx010302 hy010302 using 1 <;> norm_num
              exact Batch0178.cell1429.sound htau (by
                simp only [Batch0178.cell1429, Batch0178.tau1429, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103021 (by positivity) using 1 <;> norm_num)
            · have hs0103023 : InSquare (-9/64) (-21/64) (1/320) tau := by
                convert childUR hs010302 hx010302 hy010302 using 1 <;> norm_num
              exact Batch0178.cell1431.sound htau (by
                simp only [Batch0178.cell1431, Batch0178.tau1431, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01030 | hy01030
        · have hs010301 : InSquare (-21/160) (-11/32) (1/160) tau := by
            convert childLR hs01030 hx01030 hy01030 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx010301 | hx010301
          · rcases le_total tau.im (-11/32 : ℝ) with hy010301 | hy010301
            · have hs0103010 : InSquare (-43/320) (-111/320) (1/320) tau := by
                convert childLL hs010301 hx010301 hy010301 using 1 <;> norm_num
              exact Batch0178.cell1424.sound htau (by
                simp only [Batch0178.cell1424, Batch0178.tau1424, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103010 (by positivity) using 1 <;> norm_num)
            · have hs0103012 : InSquare (-43/320) (-109/320) (1/320) tau := by
                convert childUL hs010301 hx010301 hy010301 using 1 <;> norm_num
              exact Batch0178.cell1426.sound htau (by
                simp only [Batch0178.cell1426, Batch0178.tau1426, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010301 | hy010301
            · have hs0103011 : InSquare (-41/320) (-111/320) (1/320) tau := by
                convert childLR hs010301 hx010301 hy010301 using 1 <;> norm_num
              exact Batch0178.cell1425.sound htau (by
                simp only [Batch0178.cell1425, Batch0178.tau1425, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103011 (by positivity) using 1 <;> norm_num)
            · have hs0103013 : InSquare (-41/320) (-109/320) (1/320) tau := by
                convert childUR hs010301 hx010301 hy010301 using 1 <;> norm_num
              exact Batch0178.cell1427.sound htau (by
                simp only [Batch0178.cell1427, Batch0178.tau1427, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103013 (by positivity) using 1 <;> norm_num)
        · have hs010303 : InSquare (-21/160) (-53/160) (1/160) tau := by
            convert childUR hs01030 hx01030 hy01030 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx010303 | hx010303
          · rcases le_total tau.im (-53/160 : ℝ) with hy010303 | hy010303
            · have hs0103030 : InSquare (-43/320) (-107/320) (1/320) tau := by
                convert childLL hs010303 hx010303 hy010303 using 1 <;> norm_num
              exact Batch0179.cell1432.sound htau (by
                simp only [Batch0179.cell1432, Batch0179.tau1432, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103030 (by positivity) using 1 <;> norm_num)
            · have hs0103032 : InSquare (-43/320) (-21/64) (1/320) tau := by
                convert childUL hs010303 hx010303 hy010303 using 1 <;> norm_num
              exact Batch0179.cell1434.sound htau (by
                simp only [Batch0179.cell1434, Batch0179.tau1434, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy010303 | hy010303
            · have hs0103031 : InSquare (-41/320) (-107/320) (1/320) tau := by
                convert childLR hs010303 hx010303 hy010303 using 1 <;> norm_num
              exact Batch0179.cell1433.sound htau (by
                simp only [Batch0179.cell1433, Batch0179.tau1433, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103031 (by positivity) using 1 <;> norm_num)
            · have hs0103033 : InSquare (-41/320) (-21/64) (1/320) tau := by
                convert childUR hs010303 hx010303 hy010303 using 1 <;> norm_num
              exact Batch0179.cell1435.sound htau (by
                simp only [Batch0179.cell1435, Batch0179.tau1435, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103033 (by positivity) using 1 <;> norm_num)
    · have hs01032 : InSquare (-11/80) (-5/16) (1/80) tau := by
        convert childUL hs hx0103 hy0103 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx01032 | hx01032
      · rcases le_total tau.im (-5/16 : ℝ) with hy01032 | hy01032
        · have hs010320 : InSquare (-23/160) (-51/160) (1/160) tau := by
            convert childLL hs01032 hx01032 hy01032 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx010320 | hx010320
          · rcases le_total tau.im (-51/160 : ℝ) with hy010320 | hy010320
            · have hs0103200 : InSquare (-47/320) (-103/320) (1/320) tau := by
                convert childLL hs010320 hx010320 hy010320 using 1 <;> norm_num
              exact Batch0181.cell1448.sound htau (by
                simp only [Batch0181.cell1448, Batch0181.tau1448, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103200 (by positivity) using 1 <;> norm_num)
            · have hs0103202 : InSquare (-47/320) (-101/320) (1/320) tau := by
                convert childUL hs010320 hx010320 hy010320 using 1 <;> norm_num
              exact Batch0181.cell1450.sound htau (by
                simp only [Batch0181.cell1450, Batch0181.tau1450, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy010320 | hy010320
            · have hs0103201 : InSquare (-9/64) (-103/320) (1/320) tau := by
                convert childLR hs010320 hx010320 hy010320 using 1 <;> norm_num
              exact Batch0181.cell1449.sound htau (by
                simp only [Batch0181.cell1449, Batch0181.tau1449, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103201 (by positivity) using 1 <;> norm_num)
            · have hs0103203 : InSquare (-9/64) (-101/320) (1/320) tau := by
                convert childUR hs010320 hx010320 hy010320 using 1 <;> norm_num
              exact Batch0181.cell1451.sound htau (by
                simp only [Batch0181.cell1451, Batch0181.tau1451, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103203 (by positivity) using 1 <;> norm_num)
        · have hs010322 : InSquare (-23/160) (-49/160) (1/160) tau := by
            convert childUL hs01032 hx01032 hy01032 using 1 <;> norm_num
          exact Batch0049.cell0397.sound htau (by
            simp only [Batch0049.cell0397, Batch0049.tau0397, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01032 | hy01032
        · have hs010321 : InSquare (-21/160) (-51/160) (1/160) tau := by
            convert childLR hs01032 hx01032 hy01032 using 1 <;> norm_num
          exact Batch0049.cell0396.sound htau (by
            simp only [Batch0049.cell0396, Batch0049.tau0396, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010321 (by positivity) using 1 <;> norm_num)
        · have hs010323 : InSquare (-21/160) (-49/160) (1/160) tau := by
            convert childUR hs01032 hx01032 hy01032 using 1 <;> norm_num
          exact Batch0049.cell0398.sound htau (by
            simp only [Batch0049.cell0398, Batch0049.tau0398, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy0103 | hy0103
    · have hs01031 : InSquare (-9/80) (-27/80) (1/80) tau := by
        convert childLR hs hx0103 hy0103 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx01031 | hx01031
      · rcases le_total tau.im (-27/80 : ℝ) with hy01031 | hy01031
        · have hs010310 : InSquare (-19/160) (-11/32) (1/160) tau := by
            convert childLL hs01031 hx01031 hy01031 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx010310 | hx010310
          · rcases le_total tau.im (-11/32 : ℝ) with hy010310 | hy010310
            · have hs0103100 : InSquare (-39/320) (-111/320) (1/320) tau := by
                convert childLL hs010310 hx010310 hy010310 using 1 <;> norm_num
              exact Batch0179.cell1436.sound htau (by
                simp only [Batch0179.cell1436, Batch0179.tau1436, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103100 (by positivity) using 1 <;> norm_num)
            · have hs0103102 : InSquare (-39/320) (-109/320) (1/320) tau := by
                convert childUL hs010310 hx010310 hy010310 using 1 <;> norm_num
              exact Batch0179.cell1438.sound htau (by
                simp only [Batch0179.cell1438, Batch0179.tau1438, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010310 | hy010310
            · have hs0103101 : InSquare (-37/320) (-111/320) (1/320) tau := by
                convert childLR hs010310 hx010310 hy010310 using 1 <;> norm_num
              exact Batch0179.cell1437.sound htau (by
                simp only [Batch0179.cell1437, Batch0179.tau1437, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103101 (by positivity) using 1 <;> norm_num)
            · have hs0103103 : InSquare (-37/320) (-109/320) (1/320) tau := by
                convert childUR hs010310 hx010310 hy010310 using 1 <;> norm_num
              exact Batch0179.cell1439.sound htau (by
                simp only [Batch0179.cell1439, Batch0179.tau1439, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103103 (by positivity) using 1 <;> norm_num)
        · have hs010312 : InSquare (-19/160) (-53/160) (1/160) tau := by
            convert childUL hs01031 hx01031 hy01031 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx010312 | hx010312
          · rcases le_total tau.im (-53/160 : ℝ) with hy010312 | hy010312
            · have hs0103120 : InSquare (-39/320) (-107/320) (1/320) tau := by
                convert childLL hs010312 hx010312 hy010312 using 1 <;> norm_num
              exact Batch0180.cell1444.sound htau (by
                simp only [Batch0180.cell1444, Batch0180.tau1444, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103120 (by positivity) using 1 <;> norm_num)
            · have hs0103122 : InSquare (-39/320) (-21/64) (1/320) tau := by
                convert childUL hs010312 hx010312 hy010312 using 1 <;> norm_num
              exact Batch0180.cell1446.sound htau (by
                simp only [Batch0180.cell1446, Batch0180.tau1446, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy010312 | hy010312
            · have hs0103121 : InSquare (-37/320) (-107/320) (1/320) tau := by
                convert childLR hs010312 hx010312 hy010312 using 1 <;> norm_num
              exact Batch0180.cell1445.sound htau (by
                simp only [Batch0180.cell1445, Batch0180.tau1445, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103121 (by positivity) using 1 <;> norm_num)
            · have hs0103123 : InSquare (-37/320) (-21/64) (1/320) tau := by
                convert childUR hs010312 hx010312 hy010312 using 1 <;> norm_num
              exact Batch0180.cell1447.sound htau (by
                simp only [Batch0180.cell1447, Batch0180.tau1447, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01031 | hy01031
        · have hs010311 : InSquare (-17/160) (-11/32) (1/160) tau := by
            convert childLR hs01031 hx01031 hy01031 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx010311 | hx010311
          · rcases le_total tau.im (-11/32 : ℝ) with hy010311 | hy010311
            · have hs0103110 : InSquare (-7/64) (-111/320) (1/320) tau := by
                convert childLL hs010311 hx010311 hy010311 using 1 <;> norm_num
              exact Batch0180.cell1440.sound htau (by
                simp only [Batch0180.cell1440, Batch0180.tau1440, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103110 (by positivity) using 1 <;> norm_num)
            · have hs0103112 : InSquare (-7/64) (-109/320) (1/320) tau := by
                convert childUL hs010311 hx010311 hy010311 using 1 <;> norm_num
              exact Batch0180.cell1442.sound htau (by
                simp only [Batch0180.cell1442, Batch0180.tau1442, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010311 | hy010311
            · have hs0103111 : InSquare (-33/320) (-111/320) (1/320) tau := by
                convert childLR hs010311 hx010311 hy010311 using 1 <;> norm_num
              exact Batch0180.cell1441.sound htau (by
                simp only [Batch0180.cell1441, Batch0180.tau1441, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103111 (by positivity) using 1 <;> norm_num)
            · have hs0103113 : InSquare (-33/320) (-109/320) (1/320) tau := by
                convert childUR hs010311 hx010311 hy010311 using 1 <;> norm_num
              exact Batch0180.cell1443.sound htau (by
                simp only [Batch0180.cell1443, Batch0180.tau1443, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103113 (by positivity) using 1 <;> norm_num)
        · have hs010313 : InSquare (-17/160) (-53/160) (1/160) tau := by
            convert childUR hs01031 hx01031 hy01031 using 1 <;> norm_num
          exact Batch0049.cell0395.sound htau (by
            simp only [Batch0049.cell0395, Batch0049.tau0395, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010313 (by positivity) using 1 <;> norm_num)
    · have hs01033 : InSquare (-9/80) (-5/16) (1/80) tau := by
        convert childUR hs hx0103 hy0103 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx01033 | hx01033
      · rcases le_total tau.im (-5/16 : ℝ) with hy01033 | hy01033
        · have hs010330 : InSquare (-19/160) (-51/160) (1/160) tau := by
            convert childLL hs01033 hx01033 hy01033 using 1 <;> norm_num
          exact Batch0049.cell0399.sound htau (by
            simp only [Batch0049.cell0399, Batch0049.tau0399, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010330 (by positivity) using 1 <;> norm_num)
        · have hs010332 : InSquare (-19/160) (-49/160) (1/160) tau := by
            convert childUL hs01033 hx01033 hy01033 using 1 <;> norm_num
          exact Batch0050.cell0401.sound htau (by
            simp only [Batch0050.cell0401, Batch0050.tau0401, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01033 | hy01033
        · have hs010331 : InSquare (-17/160) (-51/160) (1/160) tau := by
            convert childLR hs01033 hx01033 hy01033 using 1 <;> norm_num
          exact Batch0050.cell0400.sound htau (by
            simp only [Batch0050.cell0400, Batch0050.tau0400, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010331 (by positivity) using 1 <;> norm_num)
        · have hs010333 : InSquare (-17/160) (-49/160) (1/160) tau := by
            convert childUR hs01033 hx01033 hy01033 using 1 <;> norm_num
          exact Batch0050.cell0402.sound htau (by
            simp only [Batch0050.cell0402, Batch0050.tau0402, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0103

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0110 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0110

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_0110000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/320) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/32)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0110001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-29/320) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/80)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0110010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-27/320) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/160)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0110011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-5/64) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/40)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01100020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01100021 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-61/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/32)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01100030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-59/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01100031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-57/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/80)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/128) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101002 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/640) (-253/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/320)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-43/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-41/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/16)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-39/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-37/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/128) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+17/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-33/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/20)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (-3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx0110 | hx0110
  · rcases le_total tau.im (-3/8 : ℝ) with hy0110 | hy0110
    · have hs01100 : InSquare (-7/80) (-31/80) (1/80) tau := by
        convert childLL hs hx0110 hy0110 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx01100 | hx01100
      · rcases le_total tau.im (-31/80 : ℝ) with hy01100 | hy01100
        · have hs011000 : InSquare (-3/32) (-63/160) (1/160) tau := by
            convert childLL hs01100 hx01100 hy01100 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx011000 | hx011000
          · rcases le_total tau.im (-63/160 : ℝ) with hy011000 | hy011000
            · have hs0110000 : InSquare (-31/320) (-127/320) (1/320) tau := by
                convert childLL hs011000 hx011000 hy011000 using 1 <;> norm_num
              exact (outside_0110000 htau hs0110000).elim
            · have hs0110002 : InSquare (-31/320) (-25/64) (1/320) tau := by
                convert childUL hs011000 hx011000 hy011000 using 1 <;> norm_num
              rcases le_total tau.re (-31/320 : ℝ) with hx0110002 | hx0110002
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110002 | hy0110002
                · have hs01100020 : InSquare (-63/640) (-251/640) (1/640) tau := by
                    convert childLL hs0110002 hx0110002 hy0110002 using 1 <;> norm_num
                  exact (outside_01100020 htau hs01100020).elim
                · have hs01100022 : InSquare (-63/640) (-249/640) (1/640) tau := by
                    convert childUL hs0110002 hx0110002 hy0110002 using 1 <;> norm_num
                  exact Batch0340.cell2721.sound htau (by
                    simp only [Batch0340.cell2721, Batch0340.tau2721, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110002 | hy0110002
                · have hs01100021 : InSquare (-61/640) (-251/640) (1/640) tau := by
                    convert childLR hs0110002 hx0110002 hy0110002 using 1 <;> norm_num
                  exact (outside_01100021 htau hs01100021).elim
                · have hs01100023 : InSquare (-61/640) (-249/640) (1/640) tau := by
                    convert childUR hs0110002 hx0110002 hy0110002 using 1 <;> norm_num
                  exact Batch0340.cell2722.sound htau (by
                    simp only [Batch0340.cell2722, Batch0340.tau2722, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011000 | hy011000
            · have hs0110001 : InSquare (-29/320) (-127/320) (1/320) tau := by
                convert childLR hs011000 hx011000 hy011000 using 1 <;> norm_num
              exact (outside_0110001 htau hs0110001).elim
            · have hs0110003 : InSquare (-29/320) (-25/64) (1/320) tau := by
                convert childUR hs011000 hx011000 hy011000 using 1 <;> norm_num
              rcases le_total tau.re (-29/320 : ℝ) with hx0110003 | hx0110003
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110003 | hy0110003
                · have hs01100030 : InSquare (-59/640) (-251/640) (1/640) tau := by
                    convert childLL hs0110003 hx0110003 hy0110003 using 1 <;> norm_num
                  exact (outside_01100030 htau hs01100030).elim
                · have hs01100032 : InSquare (-59/640) (-249/640) (1/640) tau := by
                    convert childUL hs0110003 hx0110003 hy0110003 using 1 <;> norm_num
                  exact Batch0340.cell2723.sound htau (by
                    simp only [Batch0340.cell2723, Batch0340.tau2723, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110003 | hy0110003
                · have hs01100031 : InSquare (-57/640) (-251/640) (1/640) tau := by
                    convert childLR hs0110003 hx0110003 hy0110003 using 1 <;> norm_num
                  exact (outside_01100031 htau hs01100031).elim
                · have hs01100033 : InSquare (-57/640) (-249/640) (1/640) tau := by
                    convert childUR hs0110003 hx0110003 hy0110003 using 1 <;> norm_num
                  exact Batch0340.cell2724.sound htau (by
                    simp only [Batch0340.cell2724, Batch0340.tau2724, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100033 (by positivity) using 1 <;> norm_num)
        · have hs011002 : InSquare (-3/32) (-61/160) (1/160) tau := by
            convert childUL hs01100 hx01100 hy01100 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx011002 | hx011002
          · rcases le_total tau.im (-61/160 : ℝ) with hy011002 | hy011002
            · have hs0110020 : InSquare (-31/320) (-123/320) (1/320) tau := by
                convert childLL hs011002 hx011002 hy011002 using 1 <;> norm_num
              rcases le_total tau.re (-31/320 : ℝ) with hx0110020 | hx0110020
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110020 | hy0110020
                · have hs01100200 : InSquare (-63/640) (-247/640) (1/640) tau := by
                    convert childLL hs0110020 hx0110020 hy0110020 using 1 <;> norm_num
                  exact Batch0341.cell2733.sound htau (by
                    simp only [Batch0341.cell2733, Batch0341.tau2733, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100200 (by positivity) using 1 <;> norm_num)
                · have hs01100202 : InSquare (-63/640) (-49/128) (1/640) tau := by
                    convert childUL hs0110020 hx0110020 hy0110020 using 1 <;> norm_num
                  exact Batch0341.cell2735.sound htau (by
                    simp only [Batch0341.cell2735, Batch0341.tau2735, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110020 | hy0110020
                · have hs01100201 : InSquare (-61/640) (-247/640) (1/640) tau := by
                    convert childLR hs0110020 hx0110020 hy0110020 using 1 <;> norm_num
                  exact Batch0341.cell2734.sound htau (by
                    simp only [Batch0341.cell2734, Batch0341.tau2734, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100201 (by positivity) using 1 <;> norm_num)
                · have hs01100203 : InSquare (-61/640) (-49/128) (1/640) tau := by
                    convert childUR hs0110020 hx0110020 hy0110020 using 1 <;> norm_num
                  exact Batch0342.cell2736.sound htau (by
                    simp only [Batch0342.cell2736, Batch0342.tau2736, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100203 (by positivity) using 1 <;> norm_num)
            · have hs0110022 : InSquare (-31/320) (-121/320) (1/320) tau := by
                convert childUL hs011002 hx011002 hy011002 using 1 <;> norm_num
              rcases le_total tau.re (-31/320 : ℝ) with hx0110022 | hx0110022
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110022 | hy0110022
                · have hs01100220 : InSquare (-63/640) (-243/640) (1/640) tau := by
                    convert childLL hs0110022 hx0110022 hy0110022 using 1 <;> norm_num
                  exact Batch0342.cell2741.sound htau (by
                    simp only [Batch0342.cell2741, Batch0342.tau2741, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100220 (by positivity) using 1 <;> norm_num)
                · have hs01100222 : InSquare (-63/640) (-241/640) (1/640) tau := by
                    convert childUL hs0110022 hx0110022 hy0110022 using 1 <;> norm_num
                  exact Batch0342.cell2743.sound htau (by
                    simp only [Batch0342.cell2743, Batch0342.tau2743, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110022 | hy0110022
                · have hs01100221 : InSquare (-61/640) (-243/640) (1/640) tau := by
                    convert childLR hs0110022 hx0110022 hy0110022 using 1 <;> norm_num
                  exact Batch0342.cell2742.sound htau (by
                    simp only [Batch0342.cell2742, Batch0342.tau2742, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100221 (by positivity) using 1 <;> norm_num)
                · have hs01100223 : InSquare (-61/640) (-241/640) (1/640) tau := by
                    convert childUR hs0110022 hx0110022 hy0110022 using 1 <;> norm_num
                  exact Batch0343.cell2744.sound htau (by
                    simp only [Batch0343.cell2744, Batch0343.tau2744, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011002 | hy011002
            · have hs0110021 : InSquare (-29/320) (-123/320) (1/320) tau := by
                convert childLR hs011002 hx011002 hy011002 using 1 <;> norm_num
              rcases le_total tau.re (-29/320 : ℝ) with hx0110021 | hx0110021
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110021 | hy0110021
                · have hs01100210 : InSquare (-59/640) (-247/640) (1/640) tau := by
                    convert childLL hs0110021 hx0110021 hy0110021 using 1 <;> norm_num
                  exact Batch0342.cell2737.sound htau (by
                    simp only [Batch0342.cell2737, Batch0342.tau2737, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100210 (by positivity) using 1 <;> norm_num)
                · have hs01100212 : InSquare (-59/640) (-49/128) (1/640) tau := by
                    convert childUL hs0110021 hx0110021 hy0110021 using 1 <;> norm_num
                  exact Batch0342.cell2739.sound htau (by
                    simp only [Batch0342.cell2739, Batch0342.tau2739, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110021 | hy0110021
                · have hs01100211 : InSquare (-57/640) (-247/640) (1/640) tau := by
                    convert childLR hs0110021 hx0110021 hy0110021 using 1 <;> norm_num
                  exact Batch0342.cell2738.sound htau (by
                    simp only [Batch0342.cell2738, Batch0342.tau2738, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100211 (by positivity) using 1 <;> norm_num)
                · have hs01100213 : InSquare (-57/640) (-49/128) (1/640) tau := by
                    convert childUR hs0110021 hx0110021 hy0110021 using 1 <;> norm_num
                  exact Batch0342.cell2740.sound htau (by
                    simp only [Batch0342.cell2740, Batch0342.tau2740, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100213 (by positivity) using 1 <;> norm_num)
            · have hs0110023 : InSquare (-29/320) (-121/320) (1/320) tau := by
                convert childUR hs011002 hx011002 hy011002 using 1 <;> norm_num
              rcases le_total tau.re (-29/320 : ℝ) with hx0110023 | hx0110023
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110023 | hy0110023
                · have hs01100230 : InSquare (-59/640) (-243/640) (1/640) tau := by
                    convert childLL hs0110023 hx0110023 hy0110023 using 1 <;> norm_num
                  exact Batch0343.cell2745.sound htau (by
                    simp only [Batch0343.cell2745, Batch0343.tau2745, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100230 (by positivity) using 1 <;> norm_num)
                · have hs01100232 : InSquare (-59/640) (-241/640) (1/640) tau := by
                    convert childUL hs0110023 hx0110023 hy0110023 using 1 <;> norm_num
                  exact Batch0343.cell2747.sound htau (by
                    simp only [Batch0343.cell2747, Batch0343.tau2747, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110023 | hy0110023
                · have hs01100231 : InSquare (-57/640) (-243/640) (1/640) tau := by
                    convert childLR hs0110023 hx0110023 hy0110023 using 1 <;> norm_num
                  exact Batch0343.cell2746.sound htau (by
                    simp only [Batch0343.cell2746, Batch0343.tau2746, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100231 (by positivity) using 1 <;> norm_num)
                · have hs01100233 : InSquare (-57/640) (-241/640) (1/640) tau := by
                    convert childUR hs0110023 hx0110023 hy0110023 using 1 <;> norm_num
                  exact Batch0343.cell2748.sound htau (by
                    simp only [Batch0343.cell2748, Batch0343.tau2748, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy01100 | hy01100
        · have hs011001 : InSquare (-13/160) (-63/160) (1/160) tau := by
            convert childLR hs01100 hx01100 hy01100 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx011001 | hx011001
          · rcases le_total tau.im (-63/160 : ℝ) with hy011001 | hy011001
            · have hs0110010 : InSquare (-27/320) (-127/320) (1/320) tau := by
                convert childLL hs011001 hx011001 hy011001 using 1 <;> norm_num
              exact (outside_0110010 htau hs0110010).elim
            · have hs0110012 : InSquare (-27/320) (-25/64) (1/320) tau := by
                convert childUL hs011001 hx011001 hy011001 using 1 <;> norm_num
              rcases le_total tau.re (-27/320 : ℝ) with hx0110012 | hx0110012
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110012 | hy0110012
                · have hs01100120 : InSquare (-11/128) (-251/640) (1/640) tau := by
                    convert childLL hs0110012 hx0110012 hy0110012 using 1 <;> norm_num
                  exact Batch0340.cell2725.sound htau (by
                    simp only [Batch0340.cell2725, Batch0340.tau2725, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100120 (by positivity) using 1 <;> norm_num)
                · have hs01100122 : InSquare (-11/128) (-249/640) (1/640) tau := by
                    convert childUL hs0110012 hx0110012 hy0110012 using 1 <;> norm_num
                  exact Batch0340.cell2727.sound htau (by
                    simp only [Batch0340.cell2727, Batch0340.tau2727, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110012 | hy0110012
                · have hs01100121 : InSquare (-53/640) (-251/640) (1/640) tau := by
                    convert childLR hs0110012 hx0110012 hy0110012 using 1 <;> norm_num
                  exact Batch0340.cell2726.sound htau (by
                    simp only [Batch0340.cell2726, Batch0340.tau2726, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100121 (by positivity) using 1 <;> norm_num)
                · have hs01100123 : InSquare (-53/640) (-249/640) (1/640) tau := by
                    convert childUR hs0110012 hx0110012 hy0110012 using 1 <;> norm_num
                  exact Batch0341.cell2728.sound htau (by
                    simp only [Batch0341.cell2728, Batch0341.tau2728, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011001 | hy011001
            · have hs0110011 : InSquare (-5/64) (-127/320) (1/320) tau := by
                convert childLR hs011001 hx011001 hy011001 using 1 <;> norm_num
              exact (outside_0110011 htau hs0110011).elim
            · have hs0110013 : InSquare (-5/64) (-25/64) (1/320) tau := by
                convert childUR hs011001 hx011001 hy011001 using 1 <;> norm_num
              rcases le_total tau.re (-5/64 : ℝ) with hx0110013 | hx0110013
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110013 | hy0110013
                · have hs01100130 : InSquare (-51/640) (-251/640) (1/640) tau := by
                    convert childLL hs0110013 hx0110013 hy0110013 using 1 <;> norm_num
                  exact Batch0341.cell2729.sound htau (by
                    simp only [Batch0341.cell2729, Batch0341.tau2729, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100130 (by positivity) using 1 <;> norm_num)
                · have hs01100132 : InSquare (-51/640) (-249/640) (1/640) tau := by
                    convert childUL hs0110013 hx0110013 hy0110013 using 1 <;> norm_num
                  exact Batch0341.cell2731.sound htau (by
                    simp only [Batch0341.cell2731, Batch0341.tau2731, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110013 | hy0110013
                · have hs01100131 : InSquare (-49/640) (-251/640) (1/640) tau := by
                    convert childLR hs0110013 hx0110013 hy0110013 using 1 <;> norm_num
                  exact Batch0341.cell2730.sound htau (by
                    simp only [Batch0341.cell2730, Batch0341.tau2730, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100131 (by positivity) using 1 <;> norm_num)
                · have hs01100133 : InSquare (-49/640) (-249/640) (1/640) tau := by
                    convert childUR hs0110013 hx0110013 hy0110013 using 1 <;> norm_num
                  exact Batch0341.cell2732.sound htau (by
                    simp only [Batch0341.cell2732, Batch0341.tau2732, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100133 (by positivity) using 1 <;> norm_num)
        · have hs011003 : InSquare (-13/160) (-61/160) (1/160) tau := by
            convert childUR hs01100 hx01100 hy01100 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx011003 | hx011003
          · rcases le_total tau.im (-61/160 : ℝ) with hy011003 | hy011003
            · have hs0110030 : InSquare (-27/320) (-123/320) (1/320) tau := by
                convert childLL hs011003 hx011003 hy011003 using 1 <;> norm_num
              rcases le_total tau.re (-27/320 : ℝ) with hx0110030 | hx0110030
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110030 | hy0110030
                · have hs01100300 : InSquare (-11/128) (-247/640) (1/640) tau := by
                    convert childLL hs0110030 hx0110030 hy0110030 using 1 <;> norm_num
                  exact Batch0343.cell2749.sound htau (by
                    simp only [Batch0343.cell2749, Batch0343.tau2749, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100300 (by positivity) using 1 <;> norm_num)
                · have hs01100302 : InSquare (-11/128) (-49/128) (1/640) tau := by
                    convert childUL hs0110030 hx0110030 hy0110030 using 1 <;> norm_num
                  exact Batch0343.cell2751.sound htau (by
                    simp only [Batch0343.cell2751, Batch0343.tau2751, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110030 | hy0110030
                · have hs01100301 : InSquare (-53/640) (-247/640) (1/640) tau := by
                    convert childLR hs0110030 hx0110030 hy0110030 using 1 <;> norm_num
                  exact Batch0343.cell2750.sound htau (by
                    simp only [Batch0343.cell2750, Batch0343.tau2750, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100301 (by positivity) using 1 <;> norm_num)
                · have hs01100303 : InSquare (-53/640) (-49/128) (1/640) tau := by
                    convert childUR hs0110030 hx0110030 hy0110030 using 1 <;> norm_num
                  exact Batch0344.cell2752.sound htau (by
                    simp only [Batch0344.cell2752, Batch0344.tau2752, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100303 (by positivity) using 1 <;> norm_num)
            · have hs0110032 : InSquare (-27/320) (-121/320) (1/320) tau := by
                convert childUL hs011003 hx011003 hy011003 using 1 <;> norm_num
              rcases le_total tau.re (-27/320 : ℝ) with hx0110032 | hx0110032
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110032 | hy0110032
                · have hs01100320 : InSquare (-11/128) (-243/640) (1/640) tau := by
                    convert childLL hs0110032 hx0110032 hy0110032 using 1 <;> norm_num
                  exact Batch0344.cell2757.sound htau (by
                    simp only [Batch0344.cell2757, Batch0344.tau2757, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100320 (by positivity) using 1 <;> norm_num)
                · have hs01100322 : InSquare (-11/128) (-241/640) (1/640) tau := by
                    convert childUL hs0110032 hx0110032 hy0110032 using 1 <;> norm_num
                  exact Batch0344.cell2759.sound htau (by
                    simp only [Batch0344.cell2759, Batch0344.tau2759, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110032 | hy0110032
                · have hs01100321 : InSquare (-53/640) (-243/640) (1/640) tau := by
                    convert childLR hs0110032 hx0110032 hy0110032 using 1 <;> norm_num
                  exact Batch0344.cell2758.sound htau (by
                    simp only [Batch0344.cell2758, Batch0344.tau2758, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100321 (by positivity) using 1 <;> norm_num)
                · have hs01100323 : InSquare (-53/640) (-241/640) (1/640) tau := by
                    convert childUR hs0110032 hx0110032 hy0110032 using 1 <;> norm_num
                  exact Batch0345.cell2760.sound htau (by
                    simp only [Batch0345.cell2760, Batch0345.tau2760, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011003 | hy011003
            · have hs0110031 : InSquare (-5/64) (-123/320) (1/320) tau := by
                convert childLR hs011003 hx011003 hy011003 using 1 <;> norm_num
              rcases le_total tau.re (-5/64 : ℝ) with hx0110031 | hx0110031
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110031 | hy0110031
                · have hs01100310 : InSquare (-51/640) (-247/640) (1/640) tau := by
                    convert childLL hs0110031 hx0110031 hy0110031 using 1 <;> norm_num
                  exact Batch0344.cell2753.sound htau (by
                    simp only [Batch0344.cell2753, Batch0344.tau2753, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100310 (by positivity) using 1 <;> norm_num)
                · have hs01100312 : InSquare (-51/640) (-49/128) (1/640) tau := by
                    convert childUL hs0110031 hx0110031 hy0110031 using 1 <;> norm_num
                  exact Batch0344.cell2755.sound htau (by
                    simp only [Batch0344.cell2755, Batch0344.tau2755, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110031 | hy0110031
                · have hs01100311 : InSquare (-49/640) (-247/640) (1/640) tau := by
                    convert childLR hs0110031 hx0110031 hy0110031 using 1 <;> norm_num
                  exact Batch0344.cell2754.sound htau (by
                    simp only [Batch0344.cell2754, Batch0344.tau2754, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100311 (by positivity) using 1 <;> norm_num)
                · have hs01100313 : InSquare (-49/640) (-49/128) (1/640) tau := by
                    convert childUR hs0110031 hx0110031 hy0110031 using 1 <;> norm_num
                  exact Batch0344.cell2756.sound htau (by
                    simp only [Batch0344.cell2756, Batch0344.tau2756, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100313 (by positivity) using 1 <;> norm_num)
            · have hs0110033 : InSquare (-5/64) (-121/320) (1/320) tau := by
                convert childUR hs011003 hx011003 hy011003 using 1 <;> norm_num
              rcases le_total tau.re (-5/64 : ℝ) with hx0110033 | hx0110033
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110033 | hy0110033
                · have hs01100330 : InSquare (-51/640) (-243/640) (1/640) tau := by
                    convert childLL hs0110033 hx0110033 hy0110033 using 1 <;> norm_num
                  exact Batch0345.cell2761.sound htau (by
                    simp only [Batch0345.cell2761, Batch0345.tau2761, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100330 (by positivity) using 1 <;> norm_num)
                · have hs01100332 : InSquare (-51/640) (-241/640) (1/640) tau := by
                    convert childUL hs0110033 hx0110033 hy0110033 using 1 <;> norm_num
                  exact Batch0345.cell2763.sound htau (by
                    simp only [Batch0345.cell2763, Batch0345.tau2763, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110033 | hy0110033
                · have hs01100331 : InSquare (-49/640) (-243/640) (1/640) tau := by
                    convert childLR hs0110033 hx0110033 hy0110033 using 1 <;> norm_num
                  exact Batch0345.cell2762.sound htau (by
                    simp only [Batch0345.cell2762, Batch0345.tau2762, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100331 (by positivity) using 1 <;> norm_num)
                · have hs01100333 : InSquare (-49/640) (-241/640) (1/640) tau := by
                    convert childUR hs0110033 hx0110033 hy0110033 using 1 <;> norm_num
                  exact Batch0345.cell2764.sound htau (by
                    simp only [Batch0345.cell2764, Batch0345.tau2764, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100333 (by positivity) using 1 <;> norm_num)
    · have hs01102 : InSquare (-7/80) (-29/80) (1/80) tau := by
        convert childUL hs hx0110 hy0110 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx01102 | hx01102
      · rcases le_total tau.im (-29/80 : ℝ) with hy01102 | hy01102
        · have hs011020 : InSquare (-3/32) (-59/160) (1/160) tau := by
            convert childLL hs01102 hx01102 hy01102 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx011020 | hx011020
          · rcases le_total tau.im (-59/160 : ℝ) with hy011020 | hy011020
            · have hs0110200 : InSquare (-31/320) (-119/320) (1/320) tau := by
                convert childLL hs011020 hx011020 hy011020 using 1 <;> norm_num
              exact Batch0181.cell1455.sound htau (by
                simp only [Batch0181.cell1455, Batch0181.tau1455, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110200 (by positivity) using 1 <;> norm_num)
            · have hs0110202 : InSquare (-31/320) (-117/320) (1/320) tau := by
                convert childUL hs011020 hx011020 hy011020 using 1 <;> norm_num
              exact Batch0182.cell1457.sound htau (by
                simp only [Batch0182.cell1457, Batch0182.tau1457, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011020 | hy011020
            · have hs0110201 : InSquare (-29/320) (-119/320) (1/320) tau := by
                convert childLR hs011020 hx011020 hy011020 using 1 <;> norm_num
              exact Batch0182.cell1456.sound htau (by
                simp only [Batch0182.cell1456, Batch0182.tau1456, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110201 (by positivity) using 1 <;> norm_num)
            · have hs0110203 : InSquare (-29/320) (-117/320) (1/320) tau := by
                convert childUR hs011020 hx011020 hy011020 using 1 <;> norm_num
              exact Batch0182.cell1458.sound htau (by
                simp only [Batch0182.cell1458, Batch0182.tau1458, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110203 (by positivity) using 1 <;> norm_num)
        · have hs011022 : InSquare (-3/32) (-57/160) (1/160) tau := by
            convert childUL hs01102 hx01102 hy01102 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx011022 | hx011022
          · rcases le_total tau.im (-57/160 : ℝ) with hy011022 | hy011022
            · have hs0110220 : InSquare (-31/320) (-23/64) (1/320) tau := by
                convert childLL hs011022 hx011022 hy011022 using 1 <;> norm_num
              exact Batch0182.cell1463.sound htau (by
                simp only [Batch0182.cell1463, Batch0182.tau1463, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110220 (by positivity) using 1 <;> norm_num)
            · have hs0110222 : InSquare (-31/320) (-113/320) (1/320) tau := by
                convert childUL hs011022 hx011022 hy011022 using 1 <;> norm_num
              exact Batch0183.cell1465.sound htau (by
                simp only [Batch0183.cell1465, Batch0183.tau1465, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy011022 | hy011022
            · have hs0110221 : InSquare (-29/320) (-23/64) (1/320) tau := by
                convert childLR hs011022 hx011022 hy011022 using 1 <;> norm_num
              exact Batch0183.cell1464.sound htau (by
                simp only [Batch0183.cell1464, Batch0183.tau1464, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110221 (by positivity) using 1 <;> norm_num)
            · have hs0110223 : InSquare (-29/320) (-113/320) (1/320) tau := by
                convert childUR hs011022 hx011022 hy011022 using 1 <;> norm_num
              exact Batch0183.cell1466.sound htau (by
                simp only [Batch0183.cell1466, Batch0183.tau1466, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01102 | hy01102
        · have hs011021 : InSquare (-13/160) (-59/160) (1/160) tau := by
            convert childLR hs01102 hx01102 hy01102 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx011021 | hx011021
          · rcases le_total tau.im (-59/160 : ℝ) with hy011021 | hy011021
            · have hs0110210 : InSquare (-27/320) (-119/320) (1/320) tau := by
                convert childLL hs011021 hx011021 hy011021 using 1 <;> norm_num
              exact Batch0182.cell1459.sound htau (by
                simp only [Batch0182.cell1459, Batch0182.tau1459, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110210 (by positivity) using 1 <;> norm_num)
            · have hs0110212 : InSquare (-27/320) (-117/320) (1/320) tau := by
                convert childUL hs011021 hx011021 hy011021 using 1 <;> norm_num
              exact Batch0182.cell1461.sound htau (by
                simp only [Batch0182.cell1461, Batch0182.tau1461, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011021 | hy011021
            · have hs0110211 : InSquare (-5/64) (-119/320) (1/320) tau := by
                convert childLR hs011021 hx011021 hy011021 using 1 <;> norm_num
              exact Batch0182.cell1460.sound htau (by
                simp only [Batch0182.cell1460, Batch0182.tau1460, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110211 (by positivity) using 1 <;> norm_num)
            · have hs0110213 : InSquare (-5/64) (-117/320) (1/320) tau := by
                convert childUR hs011021 hx011021 hy011021 using 1 <;> norm_num
              exact Batch0182.cell1462.sound htau (by
                simp only [Batch0182.cell1462, Batch0182.tau1462, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110213 (by positivity) using 1 <;> norm_num)
        · have hs011023 : InSquare (-13/160) (-57/160) (1/160) tau := by
            convert childUR hs01102 hx01102 hy01102 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx011023 | hx011023
          · rcases le_total tau.im (-57/160 : ℝ) with hy011023 | hy011023
            · have hs0110230 : InSquare (-27/320) (-23/64) (1/320) tau := by
                convert childLL hs011023 hx011023 hy011023 using 1 <;> norm_num
              exact Batch0183.cell1467.sound htau (by
                simp only [Batch0183.cell1467, Batch0183.tau1467, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110230 (by positivity) using 1 <;> norm_num)
            · have hs0110232 : InSquare (-27/320) (-113/320) (1/320) tau := by
                convert childUL hs011023 hx011023 hy011023 using 1 <;> norm_num
              exact Batch0183.cell1469.sound htau (by
                simp only [Batch0183.cell1469, Batch0183.tau1469, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy011023 | hy011023
            · have hs0110231 : InSquare (-5/64) (-23/64) (1/320) tau := by
                convert childLR hs011023 hx011023 hy011023 using 1 <;> norm_num
              exact Batch0183.cell1468.sound htau (by
                simp only [Batch0183.cell1468, Batch0183.tau1468, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110231 (by positivity) using 1 <;> norm_num)
            · have hs0110233 : InSquare (-5/64) (-113/320) (1/320) tau := by
                convert childUR hs011023 hx011023 hy011023 using 1 <;> norm_num
              exact Batch0183.cell1470.sound htau (by
                simp only [Batch0183.cell1470, Batch0183.tau1470, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/8 : ℝ) with hy0110 | hy0110
    · have hs01101 : InSquare (-1/16) (-31/80) (1/80) tau := by
        convert childLR hs hx0110 hy0110 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx01101 | hx01101
      · rcases le_total tau.im (-31/80 : ℝ) with hy01101 | hy01101
        · have hs011010 : InSquare (-11/160) (-63/160) (1/160) tau := by
            convert childLL hs01101 hx01101 hy01101 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx011010 | hx011010
          · rcases le_total tau.im (-63/160 : ℝ) with hy011010 | hy011010
            · have hs0110100 : InSquare (-23/320) (-127/320) (1/320) tau := by
                convert childLL hs011010 hx011010 hy011010 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx0110100 | hx0110100
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110100 | hy0110100
                · have hs01101000 : InSquare (-47/640) (-51/128) (1/640) tau := by
                    convert childLL hs0110100 hx0110100 hy0110100 using 1 <;> norm_num
                  exact (outside_01101000 htau hs01101000).elim
                · have hs01101002 : InSquare (-47/640) (-253/640) (1/640) tau := by
                    convert childUL hs0110100 hx0110100 hy0110100 using 1 <;> norm_num
                  exact (outside_01101002 htau hs01101002).elim
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110100 | hy0110100
                · have hs01101001 : InSquare (-9/128) (-51/128) (1/640) tau := by
                    convert childLR hs0110100 hx0110100 hy0110100 using 1 <;> norm_num
                  exact (outside_01101001 htau hs01101001).elim
                · have hs01101003 : InSquare (-9/128) (-253/640) (1/640) tau := by
                    convert childUR hs0110100 hx0110100 hy0110100 using 1 <;> norm_num
                  exact Batch0345.cell2765.sound htau (by
                    simp only [Batch0345.cell2765, Batch0345.tau2765, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101003 (by positivity) using 1 <;> norm_num)
            · have hs0110102 : InSquare (-23/320) (-25/64) (1/320) tau := by
                convert childUL hs011010 hx011010 hy011010 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx0110102 | hx0110102
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110102 | hy0110102
                · have hs01101020 : InSquare (-47/640) (-251/640) (1/640) tau := by
                    convert childLL hs0110102 hx0110102 hy0110102 using 1 <;> norm_num
                  exact Batch0346.cell2768.sound htau (by
                    simp only [Batch0346.cell2768, Batch0346.tau2768, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101020 (by positivity) using 1 <;> norm_num)
                · have hs01101022 : InSquare (-47/640) (-249/640) (1/640) tau := by
                    convert childUL hs0110102 hx0110102 hy0110102 using 1 <;> norm_num
                  exact Batch0346.cell2770.sound htau (by
                    simp only [Batch0346.cell2770, Batch0346.tau2770, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110102 | hy0110102
                · have hs01101021 : InSquare (-9/128) (-251/640) (1/640) tau := by
                    convert childLR hs0110102 hx0110102 hy0110102 using 1 <;> norm_num
                  exact Batch0346.cell2769.sound htau (by
                    simp only [Batch0346.cell2769, Batch0346.tau2769, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101021 (by positivity) using 1 <;> norm_num)
                · have hs01101023 : InSquare (-9/128) (-249/640) (1/640) tau := by
                    convert childUR hs0110102 hx0110102 hy0110102 using 1 <;> norm_num
                  exact Batch0346.cell2771.sound htau (by
                    simp only [Batch0346.cell2771, Batch0346.tau2771, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011010 | hy011010
            · have hs0110101 : InSquare (-21/320) (-127/320) (1/320) tau := by
                convert childLR hs011010 hx011010 hy011010 using 1 <;> norm_num
              rcases le_total tau.re (-21/320 : ℝ) with hx0110101 | hx0110101
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110101 | hy0110101
                · have hs01101010 : InSquare (-43/640) (-51/128) (1/640) tau := by
                    convert childLL hs0110101 hx0110101 hy0110101 using 1 <;> norm_num
                  exact (outside_01101010 htau hs01101010).elim
                · have hs01101012 : InSquare (-43/640) (-253/640) (1/640) tau := by
                    convert childUL hs0110101 hx0110101 hy0110101 using 1 <;> norm_num
                  exact Batch0345.cell2766.sound htau (by
                    simp only [Batch0345.cell2766, Batch0345.tau2766, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110101 | hy0110101
                · have hs01101011 : InSquare (-41/640) (-51/128) (1/640) tau := by
                    convert childLR hs0110101 hx0110101 hy0110101 using 1 <;> norm_num
                  exact (outside_01101011 htau hs01101011).elim
                · have hs01101013 : InSquare (-41/640) (-253/640) (1/640) tau := by
                    convert childUR hs0110101 hx0110101 hy0110101 using 1 <;> norm_num
                  exact Batch0345.cell2767.sound htau (by
                    simp only [Batch0345.cell2767, Batch0345.tau2767, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101013 (by positivity) using 1 <;> norm_num)
            · have hs0110103 : InSquare (-21/320) (-25/64) (1/320) tau := by
                convert childUR hs011010 hx011010 hy011010 using 1 <;> norm_num
              rcases le_total tau.re (-21/320 : ℝ) with hx0110103 | hx0110103
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110103 | hy0110103
                · have hs01101030 : InSquare (-43/640) (-251/640) (1/640) tau := by
                    convert childLL hs0110103 hx0110103 hy0110103 using 1 <;> norm_num
                  exact Batch0346.cell2772.sound htau (by
                    simp only [Batch0346.cell2772, Batch0346.tau2772, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101030 (by positivity) using 1 <;> norm_num)
                · have hs01101032 : InSquare (-43/640) (-249/640) (1/640) tau := by
                    convert childUL hs0110103 hx0110103 hy0110103 using 1 <;> norm_num
                  exact Batch0346.cell2774.sound htau (by
                    simp only [Batch0346.cell2774, Batch0346.tau2774, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110103 | hy0110103
                · have hs01101031 : InSquare (-41/640) (-251/640) (1/640) tau := by
                    convert childLR hs0110103 hx0110103 hy0110103 using 1 <;> norm_num
                  exact Batch0346.cell2773.sound htau (by
                    simp only [Batch0346.cell2773, Batch0346.tau2773, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101031 (by positivity) using 1 <;> norm_num)
                · have hs01101033 : InSquare (-41/640) (-249/640) (1/640) tau := by
                    convert childUR hs0110103 hx0110103 hy0110103 using 1 <;> norm_num
                  exact Batch0346.cell2775.sound htau (by
                    simp only [Batch0346.cell2775, Batch0346.tau2775, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101033 (by positivity) using 1 <;> norm_num)
        · have hs011012 : InSquare (-11/160) (-61/160) (1/160) tau := by
            convert childUL hs01101 hx01101 hy01101 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx011012 | hx011012
          · rcases le_total tau.im (-61/160 : ℝ) with hy011012 | hy011012
            · have hs0110120 : InSquare (-23/320) (-123/320) (1/320) tau := by
                convert childLL hs011012 hx011012 hy011012 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx0110120 | hx0110120
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110120 | hy0110120
                · have hs01101200 : InSquare (-47/640) (-247/640) (1/640) tau := by
                    convert childLL hs0110120 hx0110120 hy0110120 using 1 <;> norm_num
                  exact Batch0348.cell2788.sound htau (by
                    simp only [Batch0348.cell2788, Batch0348.tau2788, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101200 (by positivity) using 1 <;> norm_num)
                · have hs01101202 : InSquare (-47/640) (-49/128) (1/640) tau := by
                    convert childUL hs0110120 hx0110120 hy0110120 using 1 <;> norm_num
                  exact Batch0348.cell2790.sound htau (by
                    simp only [Batch0348.cell2790, Batch0348.tau2790, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110120 | hy0110120
                · have hs01101201 : InSquare (-9/128) (-247/640) (1/640) tau := by
                    convert childLR hs0110120 hx0110120 hy0110120 using 1 <;> norm_num
                  exact Batch0348.cell2789.sound htau (by
                    simp only [Batch0348.cell2789, Batch0348.tau2789, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101201 (by positivity) using 1 <;> norm_num)
                · have hs01101203 : InSquare (-9/128) (-49/128) (1/640) tau := by
                    convert childUR hs0110120 hx0110120 hy0110120 using 1 <;> norm_num
                  exact Batch0348.cell2791.sound htau (by
                    simp only [Batch0348.cell2791, Batch0348.tau2791, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101203 (by positivity) using 1 <;> norm_num)
            · have hs0110122 : InSquare (-23/320) (-121/320) (1/320) tau := by
                convert childUL hs011012 hx011012 hy011012 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx0110122 | hx0110122
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110122 | hy0110122
                · have hs01101220 : InSquare (-47/640) (-243/640) (1/640) tau := by
                    convert childLL hs0110122 hx0110122 hy0110122 using 1 <;> norm_num
                  exact Batch0349.cell2796.sound htau (by
                    simp only [Batch0349.cell2796, Batch0349.tau2796, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101220 (by positivity) using 1 <;> norm_num)
                · have hs01101222 : InSquare (-47/640) (-241/640) (1/640) tau := by
                    convert childUL hs0110122 hx0110122 hy0110122 using 1 <;> norm_num
                  exact Batch0349.cell2798.sound htau (by
                    simp only [Batch0349.cell2798, Batch0349.tau2798, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110122 | hy0110122
                · have hs01101221 : InSquare (-9/128) (-243/640) (1/640) tau := by
                    convert childLR hs0110122 hx0110122 hy0110122 using 1 <;> norm_num
                  exact Batch0349.cell2797.sound htau (by
                    simp only [Batch0349.cell2797, Batch0349.tau2797, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101221 (by positivity) using 1 <;> norm_num)
                · have hs01101223 : InSquare (-9/128) (-241/640) (1/640) tau := by
                    convert childUR hs0110122 hx0110122 hy0110122 using 1 <;> norm_num
                  exact Batch0349.cell2799.sound htau (by
                    simp only [Batch0349.cell2799, Batch0349.tau2799, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011012 | hy011012
            · have hs0110121 : InSquare (-21/320) (-123/320) (1/320) tau := by
                convert childLR hs011012 hx011012 hy011012 using 1 <;> norm_num
              rcases le_total tau.re (-21/320 : ℝ) with hx0110121 | hx0110121
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110121 | hy0110121
                · have hs01101210 : InSquare (-43/640) (-247/640) (1/640) tau := by
                    convert childLL hs0110121 hx0110121 hy0110121 using 1 <;> norm_num
                  exact Batch0349.cell2792.sound htau (by
                    simp only [Batch0349.cell2792, Batch0349.tau2792, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101210 (by positivity) using 1 <;> norm_num)
                · have hs01101212 : InSquare (-43/640) (-49/128) (1/640) tau := by
                    convert childUL hs0110121 hx0110121 hy0110121 using 1 <;> norm_num
                  exact Batch0349.cell2794.sound htau (by
                    simp only [Batch0349.cell2794, Batch0349.tau2794, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110121 | hy0110121
                · have hs01101211 : InSquare (-41/640) (-247/640) (1/640) tau := by
                    convert childLR hs0110121 hx0110121 hy0110121 using 1 <;> norm_num
                  exact Batch0349.cell2793.sound htau (by
                    simp only [Batch0349.cell2793, Batch0349.tau2793, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101211 (by positivity) using 1 <;> norm_num)
                · have hs01101213 : InSquare (-41/640) (-49/128) (1/640) tau := by
                    convert childUR hs0110121 hx0110121 hy0110121 using 1 <;> norm_num
                  exact Batch0349.cell2795.sound htau (by
                    simp only [Batch0349.cell2795, Batch0349.tau2795, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101213 (by positivity) using 1 <;> norm_num)
            · have hs0110123 : InSquare (-21/320) (-121/320) (1/320) tau := by
                convert childUR hs011012 hx011012 hy011012 using 1 <;> norm_num
              exact Batch0181.cell1452.sound htau (by
                simp only [Batch0181.cell1452, Batch0181.tau1452, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy01101 | hy01101
        · have hs011011 : InSquare (-9/160) (-63/160) (1/160) tau := by
            convert childLR hs01101 hx01101 hy01101 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx011011 | hx011011
          · rcases le_total tau.im (-63/160 : ℝ) with hy011011 | hy011011
            · have hs0110110 : InSquare (-19/320) (-127/320) (1/320) tau := by
                convert childLL hs011011 hx011011 hy011011 using 1 <;> norm_num
              rcases le_total tau.re (-19/320 : ℝ) with hx0110110 | hx0110110
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110110 | hy0110110
                · have hs01101100 : InSquare (-39/640) (-51/128) (1/640) tau := by
                    convert childLL hs0110110 hx0110110 hy0110110 using 1 <;> norm_num
                  exact (outside_01101100 htau hs01101100).elim
                · have hs01101102 : InSquare (-39/640) (-253/640) (1/640) tau := by
                    convert childUL hs0110110 hx0110110 hy0110110 using 1 <;> norm_num
                  exact Batch0347.cell2776.sound htau (by
                    simp only [Batch0347.cell2776, Batch0347.tau2776, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110110 | hy0110110
                · have hs01101101 : InSquare (-37/640) (-51/128) (1/640) tau := by
                    convert childLR hs0110110 hx0110110 hy0110110 using 1 <;> norm_num
                  exact (outside_01101101 htau hs01101101).elim
                · have hs01101103 : InSquare (-37/640) (-253/640) (1/640) tau := by
                    convert childUR hs0110110 hx0110110 hy0110110 using 1 <;> norm_num
                  exact Batch0347.cell2777.sound htau (by
                    simp only [Batch0347.cell2777, Batch0347.tau2777, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101103 (by positivity) using 1 <;> norm_num)
            · have hs0110112 : InSquare (-19/320) (-25/64) (1/320) tau := by
                convert childUL hs011011 hx011011 hy011011 using 1 <;> norm_num
              rcases le_total tau.re (-19/320 : ℝ) with hx0110112 | hx0110112
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110112 | hy0110112
                · have hs01101120 : InSquare (-39/640) (-251/640) (1/640) tau := by
                    convert childLL hs0110112 hx0110112 hy0110112 using 1 <;> norm_num
                  exact Batch0347.cell2780.sound htau (by
                    simp only [Batch0347.cell2780, Batch0347.tau2780, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101120 (by positivity) using 1 <;> norm_num)
                · have hs01101122 : InSquare (-39/640) (-249/640) (1/640) tau := by
                    convert childUL hs0110112 hx0110112 hy0110112 using 1 <;> norm_num
                  exact Batch0347.cell2782.sound htau (by
                    simp only [Batch0347.cell2782, Batch0347.tau2782, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110112 | hy0110112
                · have hs01101121 : InSquare (-37/640) (-251/640) (1/640) tau := by
                    convert childLR hs0110112 hx0110112 hy0110112 using 1 <;> norm_num
                  exact Batch0347.cell2781.sound htau (by
                    simp only [Batch0347.cell2781, Batch0347.tau2781, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101121 (by positivity) using 1 <;> norm_num)
                · have hs01101123 : InSquare (-37/640) (-249/640) (1/640) tau := by
                    convert childUR hs0110112 hx0110112 hy0110112 using 1 <;> norm_num
                  exact Batch0347.cell2783.sound htau (by
                    simp only [Batch0347.cell2783, Batch0347.tau2783, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011011 | hy011011
            · have hs0110111 : InSquare (-17/320) (-127/320) (1/320) tau := by
                convert childLR hs011011 hx011011 hy011011 using 1 <;> norm_num
              rcases le_total tau.re (-17/320 : ℝ) with hx0110111 | hx0110111
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110111 | hy0110111
                · have hs01101110 : InSquare (-7/128) (-51/128) (1/640) tau := by
                    convert childLL hs0110111 hx0110111 hy0110111 using 1 <;> norm_num
                  exact (outside_01101110 htau hs01101110).elim
                · have hs01101112 : InSquare (-7/128) (-253/640) (1/640) tau := by
                    convert childUL hs0110111 hx0110111 hy0110111 using 1 <;> norm_num
                  exact Batch0347.cell2778.sound htau (by
                    simp only [Batch0347.cell2778, Batch0347.tau2778, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110111 | hy0110111
                · have hs01101111 : InSquare (-33/640) (-51/128) (1/640) tau := by
                    convert childLR hs0110111 hx0110111 hy0110111 using 1 <;> norm_num
                  exact (outside_01101111 htau hs01101111).elim
                · have hs01101113 : InSquare (-33/640) (-253/640) (1/640) tau := by
                    convert childUR hs0110111 hx0110111 hy0110111 using 1 <;> norm_num
                  exact Batch0347.cell2779.sound htau (by
                    simp only [Batch0347.cell2779, Batch0347.tau2779, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101113 (by positivity) using 1 <;> norm_num)
            · have hs0110113 : InSquare (-17/320) (-25/64) (1/320) tau := by
                convert childUR hs011011 hx011011 hy011011 using 1 <;> norm_num
              rcases le_total tau.re (-17/320 : ℝ) with hx0110113 | hx0110113
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110113 | hy0110113
                · have hs01101130 : InSquare (-7/128) (-251/640) (1/640) tau := by
                    convert childLL hs0110113 hx0110113 hy0110113 using 1 <;> norm_num
                  exact Batch0348.cell2784.sound htau (by
                    simp only [Batch0348.cell2784, Batch0348.tau2784, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101130 (by positivity) using 1 <;> norm_num)
                · have hs01101132 : InSquare (-7/128) (-249/640) (1/640) tau := by
                    convert childUL hs0110113 hx0110113 hy0110113 using 1 <;> norm_num
                  exact Batch0348.cell2786.sound htau (by
                    simp only [Batch0348.cell2786, Batch0348.tau2786, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110113 | hy0110113
                · have hs01101131 : InSquare (-33/640) (-251/640) (1/640) tau := by
                    convert childLR hs0110113 hx0110113 hy0110113 using 1 <;> norm_num
                  exact Batch0348.cell2785.sound htau (by
                    simp only [Batch0348.cell2785, Batch0348.tau2785, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101131 (by positivity) using 1 <;> norm_num)
                · have hs01101133 : InSquare (-33/640) (-249/640) (1/640) tau := by
                    convert childUR hs0110113 hx0110113 hy0110113 using 1 <;> norm_num
                  exact Batch0348.cell2787.sound htau (by
                    simp only [Batch0348.cell2787, Batch0348.tau2787, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101133 (by positivity) using 1 <;> norm_num)
        · have hs011013 : InSquare (-9/160) (-61/160) (1/160) tau := by
            convert childUR hs01101 hx01101 hy01101 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx011013 | hx011013
          · rcases le_total tau.im (-61/160 : ℝ) with hy011013 | hy011013
            · have hs0110130 : InSquare (-19/320) (-123/320) (1/320) tau := by
                convert childLL hs011013 hx011013 hy011013 using 1 <;> norm_num
              rcases le_total tau.re (-19/320 : ℝ) with hx0110130 | hx0110130
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110130 | hy0110130
                · have hs01101300 : InSquare (-39/640) (-247/640) (1/640) tau := by
                    convert childLL hs0110130 hx0110130 hy0110130 using 1 <;> norm_num
                  exact Batch0350.cell2800.sound htau (by
                    simp only [Batch0350.cell2800, Batch0350.tau2800, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101300 (by positivity) using 1 <;> norm_num)
                · have hs01101302 : InSquare (-39/640) (-49/128) (1/640) tau := by
                    convert childUL hs0110130 hx0110130 hy0110130 using 1 <;> norm_num
                  exact Batch0350.cell2802.sound htau (by
                    simp only [Batch0350.cell2802, Batch0350.tau2802, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110130 | hy0110130
                · have hs01101301 : InSquare (-37/640) (-247/640) (1/640) tau := by
                    convert childLR hs0110130 hx0110130 hy0110130 using 1 <;> norm_num
                  exact Batch0350.cell2801.sound htau (by
                    simp only [Batch0350.cell2801, Batch0350.tau2801, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101301 (by positivity) using 1 <;> norm_num)
                · have hs01101303 : InSquare (-37/640) (-49/128) (1/640) tau := by
                    convert childUR hs0110130 hx0110130 hy0110130 using 1 <;> norm_num
                  exact Batch0350.cell2803.sound htau (by
                    simp only [Batch0350.cell2803, Batch0350.tau2803, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101303 (by positivity) using 1 <;> norm_num)
            · have hs0110132 : InSquare (-19/320) (-121/320) (1/320) tau := by
                convert childUL hs011013 hx011013 hy011013 using 1 <;> norm_num
              exact Batch0181.cell1453.sound htau (by
                simp only [Batch0181.cell1453, Batch0181.tau1453, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011013 | hy011013
            · have hs0110131 : InSquare (-17/320) (-123/320) (1/320) tau := by
                convert childLR hs011013 hx011013 hy011013 using 1 <;> norm_num
              rcases le_total tau.re (-17/320 : ℝ) with hx0110131 | hx0110131
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110131 | hy0110131
                · have hs01101310 : InSquare (-7/128) (-247/640) (1/640) tau := by
                    convert childLL hs0110131 hx0110131 hy0110131 using 1 <;> norm_num
                  exact Batch0350.cell2804.sound htau (by
                    simp only [Batch0350.cell2804, Batch0350.tau2804, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101310 (by positivity) using 1 <;> norm_num)
                · have hs01101312 : InSquare (-7/128) (-49/128) (1/640) tau := by
                    convert childUL hs0110131 hx0110131 hy0110131 using 1 <;> norm_num
                  exact Batch0350.cell2806.sound htau (by
                    simp only [Batch0350.cell2806, Batch0350.tau2806, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110131 | hy0110131
                · have hs01101311 : InSquare (-33/640) (-247/640) (1/640) tau := by
                    convert childLR hs0110131 hx0110131 hy0110131 using 1 <;> norm_num
                  exact Batch0350.cell2805.sound htau (by
                    simp only [Batch0350.cell2805, Batch0350.tau2805, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101311 (by positivity) using 1 <;> norm_num)
                · have hs01101313 : InSquare (-33/640) (-49/128) (1/640) tau := by
                    convert childUR hs0110131 hx0110131 hy0110131 using 1 <;> norm_num
                  exact Batch0350.cell2807.sound htau (by
                    simp only [Batch0350.cell2807, Batch0350.tau2807, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101313 (by positivity) using 1 <;> norm_num)
            · have hs0110133 : InSquare (-17/320) (-121/320) (1/320) tau := by
                convert childUR hs011013 hx011013 hy011013 using 1 <;> norm_num
              exact Batch0181.cell1454.sound htau (by
                simp only [Batch0181.cell1454, Batch0181.tau1454, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110133 (by positivity) using 1 <;> norm_num)
    · have hs01103 : InSquare (-1/16) (-29/80) (1/80) tau := by
        convert childUR hs hx0110 hy0110 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx01103 | hx01103
      · rcases le_total tau.im (-29/80 : ℝ) with hy01103 | hy01103
        · have hs011030 : InSquare (-11/160) (-59/160) (1/160) tau := by
            convert childLL hs01103 hx01103 hy01103 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx011030 | hx011030
          · rcases le_total tau.im (-59/160 : ℝ) with hy011030 | hy011030
            · have hs0110300 : InSquare (-23/320) (-119/320) (1/320) tau := by
                convert childLL hs011030 hx011030 hy011030 using 1 <;> norm_num
              exact Batch0183.cell1471.sound htau (by
                simp only [Batch0183.cell1471, Batch0183.tau1471, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110300 (by positivity) using 1 <;> norm_num)
            · have hs0110302 : InSquare (-23/320) (-117/320) (1/320) tau := by
                convert childUL hs011030 hx011030 hy011030 using 1 <;> norm_num
              exact Batch0184.cell1473.sound htau (by
                simp only [Batch0184.cell1473, Batch0184.tau1473, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011030 | hy011030
            · have hs0110301 : InSquare (-21/320) (-119/320) (1/320) tau := by
                convert childLR hs011030 hx011030 hy011030 using 1 <;> norm_num
              exact Batch0184.cell1472.sound htau (by
                simp only [Batch0184.cell1472, Batch0184.tau1472, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110301 (by positivity) using 1 <;> norm_num)
            · have hs0110303 : InSquare (-21/320) (-117/320) (1/320) tau := by
                convert childUR hs011030 hx011030 hy011030 using 1 <;> norm_num
              exact Batch0184.cell1474.sound htau (by
                simp only [Batch0184.cell1474, Batch0184.tau1474, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110303 (by positivity) using 1 <;> norm_num)
        · have hs011032 : InSquare (-11/160) (-57/160) (1/160) tau := by
            convert childUL hs01103 hx01103 hy01103 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx011032 | hx011032
          · rcases le_total tau.im (-57/160 : ℝ) with hy011032 | hy011032
            · have hs0110320 : InSquare (-23/320) (-23/64) (1/320) tau := by
                convert childLL hs011032 hx011032 hy011032 using 1 <;> norm_num
              exact Batch0184.cell1479.sound htau (by
                simp only [Batch0184.cell1479, Batch0184.tau1479, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110320 (by positivity) using 1 <;> norm_num)
            · have hs0110322 : InSquare (-23/320) (-113/320) (1/320) tau := by
                convert childUL hs011032 hx011032 hy011032 using 1 <;> norm_num
              exact Batch0185.cell1481.sound htau (by
                simp only [Batch0185.cell1481, Batch0185.tau1481, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy011032 | hy011032
            · have hs0110321 : InSquare (-21/320) (-23/64) (1/320) tau := by
                convert childLR hs011032 hx011032 hy011032 using 1 <;> norm_num
              exact Batch0185.cell1480.sound htau (by
                simp only [Batch0185.cell1480, Batch0185.tau1480, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110321 (by positivity) using 1 <;> norm_num)
            · have hs0110323 : InSquare (-21/320) (-113/320) (1/320) tau := by
                convert childUR hs011032 hx011032 hy011032 using 1 <;> norm_num
              exact Batch0185.cell1482.sound htau (by
                simp only [Batch0185.cell1482, Batch0185.tau1482, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01103 | hy01103
        · have hs011031 : InSquare (-9/160) (-59/160) (1/160) tau := by
            convert childLR hs01103 hx01103 hy01103 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx011031 | hx011031
          · rcases le_total tau.im (-59/160 : ℝ) with hy011031 | hy011031
            · have hs0110310 : InSquare (-19/320) (-119/320) (1/320) tau := by
                convert childLL hs011031 hx011031 hy011031 using 1 <;> norm_num
              exact Batch0184.cell1475.sound htau (by
                simp only [Batch0184.cell1475, Batch0184.tau1475, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110310 (by positivity) using 1 <;> norm_num)
            · have hs0110312 : InSquare (-19/320) (-117/320) (1/320) tau := by
                convert childUL hs011031 hx011031 hy011031 using 1 <;> norm_num
              exact Batch0184.cell1477.sound htau (by
                simp only [Batch0184.cell1477, Batch0184.tau1477, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011031 | hy011031
            · have hs0110311 : InSquare (-17/320) (-119/320) (1/320) tau := by
                convert childLR hs011031 hx011031 hy011031 using 1 <;> norm_num
              exact Batch0184.cell1476.sound htau (by
                simp only [Batch0184.cell1476, Batch0184.tau1476, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110311 (by positivity) using 1 <;> norm_num)
            · have hs0110313 : InSquare (-17/320) (-117/320) (1/320) tau := by
                convert childUR hs011031 hx011031 hy011031 using 1 <;> norm_num
              exact Batch0184.cell1478.sound htau (by
                simp only [Batch0184.cell1478, Batch0184.tau1478, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110313 (by positivity) using 1 <;> norm_num)
        · have hs011033 : InSquare (-9/160) (-57/160) (1/160) tau := by
            convert childUR hs01103 hx01103 hy01103 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx011033 | hx011033
          · rcases le_total tau.im (-57/160 : ℝ) with hy011033 | hy011033
            · have hs0110330 : InSquare (-19/320) (-23/64) (1/320) tau := by
                convert childLL hs011033 hx011033 hy011033 using 1 <;> norm_num
              exact Batch0185.cell1483.sound htau (by
                simp only [Batch0185.cell1483, Batch0185.tau1483, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110330 (by positivity) using 1 <;> norm_num)
            · have hs0110332 : InSquare (-19/320) (-113/320) (1/320) tau := by
                convert childUL hs011033 hx011033 hy011033 using 1 <;> norm_num
              exact Batch0185.cell1485.sound htau (by
                simp only [Batch0185.cell1485, Batch0185.tau1485, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy011033 | hy011033
            · have hs0110331 : InSquare (-17/320) (-23/64) (1/320) tau := by
                convert childLR hs011033 hx011033 hy011033 using 1 <;> norm_num
              exact Batch0185.cell1484.sound htau (by
                simp only [Batch0185.cell1484, Batch0185.tau1484, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110331 (by positivity) using 1 <;> norm_num)
            · have hs0110333 : InSquare (-17/320) (-113/320) (1/320) tau := by
                convert childUR hs011033 hx011033 hy011033 using 1 <;> norm_num
              exact Batch0185.cell1486.sound htau (by
                simp only [Batch0185.cell1486, Batch0185.tau1486, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0110

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0111 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0111

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (-3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx0111 | hx0111
  · rcases le_total tau.im (-3/8 : ℝ) with hy0111 | hy0111
    · have hs01110 : InSquare (-3/80) (-31/80) (1/80) tau := by
        convert childLL hs hx0111 hy0111 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx01110 | hx01110
      · rcases le_total tau.im (-31/80 : ℝ) with hy01110 | hy01110
        · have hs011100 : InSquare (-7/160) (-63/160) (1/160) tau := by
            convert childLL hs01110 hx01110 hy01110 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx011100 | hx011100
          · rcases le_total tau.im (-63/160 : ℝ) with hy011100 | hy011100
            · have hs0111000 : InSquare (-3/64) (-127/320) (1/320) tau := by
                convert childLL hs011100 hx011100 hy011100 using 1 <;> norm_num
              rcases le_total tau.re (-3/64 : ℝ) with hx0111000 | hx0111000
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111000 | hy0111000
                · have hs01110000 : InSquare (-31/640) (-51/128) (1/640) tau := by
                    convert childLL hs0111000 hx0111000 hy0111000 using 1 <;> norm_num
                  exact Batch0351.cell2808.sound htau (by
                    simp only [Batch0351.cell2808, Batch0351.tau2808, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110000 (by positivity) using 1 <;> norm_num)
                · have hs01110002 : InSquare (-31/640) (-253/640) (1/640) tau := by
                    convert childUL hs0111000 hx0111000 hy0111000 using 1 <;> norm_num
                  exact Batch0351.cell2810.sound htau (by
                    simp only [Batch0351.cell2810, Batch0351.tau2810, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111000 | hy0111000
                · have hs01110001 : InSquare (-29/640) (-51/128) (1/640) tau := by
                    convert childLR hs0111000 hx0111000 hy0111000 using 1 <;> norm_num
                  exact Batch0351.cell2809.sound htau (by
                    simp only [Batch0351.cell2809, Batch0351.tau2809, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110001 (by positivity) using 1 <;> norm_num)
                · have hs01110003 : InSquare (-29/640) (-253/640) (1/640) tau := by
                    convert childUR hs0111000 hx0111000 hy0111000 using 1 <;> norm_num
                  exact Batch0351.cell2811.sound htau (by
                    simp only [Batch0351.cell2811, Batch0351.tau2811, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110003 (by positivity) using 1 <;> norm_num)
            · have hs0111002 : InSquare (-3/64) (-25/64) (1/320) tau := by
                convert childUL hs011100 hx011100 hy011100 using 1 <;> norm_num
              rcases le_total tau.re (-3/64 : ℝ) with hx0111002 | hx0111002
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111002 | hy0111002
                · have hs01110020 : InSquare (-31/640) (-251/640) (1/640) tau := by
                    convert childLL hs0111002 hx0111002 hy0111002 using 1 <;> norm_num
                  exact Batch0352.cell2816.sound htau (by
                    simp only [Batch0352.cell2816, Batch0352.tau2816, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110020 (by positivity) using 1 <;> norm_num)
                · have hs01110022 : InSquare (-31/640) (-249/640) (1/640) tau := by
                    convert childUL hs0111002 hx0111002 hy0111002 using 1 <;> norm_num
                  exact Batch0352.cell2818.sound htau (by
                    simp only [Batch0352.cell2818, Batch0352.tau2818, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111002 | hy0111002
                · have hs01110021 : InSquare (-29/640) (-251/640) (1/640) tau := by
                    convert childLR hs0111002 hx0111002 hy0111002 using 1 <;> norm_num
                  exact Batch0352.cell2817.sound htau (by
                    simp only [Batch0352.cell2817, Batch0352.tau2817, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110021 (by positivity) using 1 <;> norm_num)
                · have hs01110023 : InSquare (-29/640) (-249/640) (1/640) tau := by
                    convert childUR hs0111002 hx0111002 hy0111002 using 1 <;> norm_num
                  exact Batch0352.cell2819.sound htau (by
                    simp only [Batch0352.cell2819, Batch0352.tau2819, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011100 | hy011100
            · have hs0111001 : InSquare (-13/320) (-127/320) (1/320) tau := by
                convert childLR hs011100 hx011100 hy011100 using 1 <;> norm_num
              rcases le_total tau.re (-13/320 : ℝ) with hx0111001 | hx0111001
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111001 | hy0111001
                · have hs01110010 : InSquare (-27/640) (-51/128) (1/640) tau := by
                    convert childLL hs0111001 hx0111001 hy0111001 using 1 <;> norm_num
                  exact Batch0351.cell2812.sound htau (by
                    simp only [Batch0351.cell2812, Batch0351.tau2812, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110010 (by positivity) using 1 <;> norm_num)
                · have hs01110012 : InSquare (-27/640) (-253/640) (1/640) tau := by
                    convert childUL hs0111001 hx0111001 hy0111001 using 1 <;> norm_num
                  exact Batch0351.cell2814.sound htau (by
                    simp only [Batch0351.cell2814, Batch0351.tau2814, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111001 | hy0111001
                · have hs01110011 : InSquare (-5/128) (-51/128) (1/640) tau := by
                    convert childLR hs0111001 hx0111001 hy0111001 using 1 <;> norm_num
                  exact Batch0351.cell2813.sound htau (by
                    simp only [Batch0351.cell2813, Batch0351.tau2813, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110011 (by positivity) using 1 <;> norm_num)
                · have hs01110013 : InSquare (-5/128) (-253/640) (1/640) tau := by
                    convert childUR hs0111001 hx0111001 hy0111001 using 1 <;> norm_num
                  exact Batch0351.cell2815.sound htau (by
                    simp only [Batch0351.cell2815, Batch0351.tau2815, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110013 (by positivity) using 1 <;> norm_num)
            · have hs0111003 : InSquare (-13/320) (-25/64) (1/320) tau := by
                convert childUR hs011100 hx011100 hy011100 using 1 <;> norm_num
              rcases le_total tau.re (-13/320 : ℝ) with hx0111003 | hx0111003
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111003 | hy0111003
                · have hs01110030 : InSquare (-27/640) (-251/640) (1/640) tau := by
                    convert childLL hs0111003 hx0111003 hy0111003 using 1 <;> norm_num
                  exact Batch0352.cell2820.sound htau (by
                    simp only [Batch0352.cell2820, Batch0352.tau2820, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110030 (by positivity) using 1 <;> norm_num)
                · have hs01110032 : InSquare (-27/640) (-249/640) (1/640) tau := by
                    convert childUL hs0111003 hx0111003 hy0111003 using 1 <;> norm_num
                  exact Batch0352.cell2822.sound htau (by
                    simp only [Batch0352.cell2822, Batch0352.tau2822, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111003 | hy0111003
                · have hs01110031 : InSquare (-5/128) (-251/640) (1/640) tau := by
                    convert childLR hs0111003 hx0111003 hy0111003 using 1 <;> norm_num
                  exact Batch0352.cell2821.sound htau (by
                    simp only [Batch0352.cell2821, Batch0352.tau2821, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110031 (by positivity) using 1 <;> norm_num)
                · have hs01110033 : InSquare (-5/128) (-249/640) (1/640) tau := by
                    convert childUR hs0111003 hx0111003 hy0111003 using 1 <;> norm_num
                  exact Batch0352.cell2823.sound htau (by
                    simp only [Batch0352.cell2823, Batch0352.tau2823, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110033 (by positivity) using 1 <;> norm_num)
        · have hs011102 : InSquare (-7/160) (-61/160) (1/160) tau := by
            convert childUL hs01110 hx01110 hy01110 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx011102 | hx011102
          · rcases le_total tau.im (-61/160 : ℝ) with hy011102 | hy011102
            · have hs0111020 : InSquare (-3/64) (-123/320) (1/320) tau := by
                convert childLL hs011102 hx011102 hy011102 using 1 <;> norm_num
              rcases le_total tau.re (-3/64 : ℝ) with hx0111020 | hx0111020
              · rcases le_total tau.im (-123/320 : ℝ) with hy0111020 | hy0111020
                · have hs01110200 : InSquare (-31/640) (-247/640) (1/640) tau := by
                    convert childLL hs0111020 hx0111020 hy0111020 using 1 <;> norm_num
                  exact Batch0355.cell2840.sound htau (by
                    simp only [Batch0355.cell2840, Batch0355.tau2840, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110200 (by positivity) using 1 <;> norm_num)
                · have hs01110202 : InSquare (-31/640) (-49/128) (1/640) tau := by
                    convert childUL hs0111020 hx0111020 hy0111020 using 1 <;> norm_num
                  exact Batch0355.cell2842.sound htau (by
                    simp only [Batch0355.cell2842, Batch0355.tau2842, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0111020 | hy0111020
                · have hs01110201 : InSquare (-29/640) (-247/640) (1/640) tau := by
                    convert childLR hs0111020 hx0111020 hy0111020 using 1 <;> norm_num
                  exact Batch0355.cell2841.sound htau (by
                    simp only [Batch0355.cell2841, Batch0355.tau2841, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110201 (by positivity) using 1 <;> norm_num)
                · have hs01110203 : InSquare (-29/640) (-49/128) (1/640) tau := by
                    convert childUR hs0111020 hx0111020 hy0111020 using 1 <;> norm_num
                  exact Batch0355.cell2843.sound htau (by
                    simp only [Batch0355.cell2843, Batch0355.tau2843, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110203 (by positivity) using 1 <;> norm_num)
            · have hs0111022 : InSquare (-3/64) (-121/320) (1/320) tau := by
                convert childUL hs011102 hx011102 hy011102 using 1 <;> norm_num
              exact Batch0185.cell1487.sound htau (by
                simp only [Batch0185.cell1487, Batch0185.tau1487, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011102 | hy011102
            · have hs0111021 : InSquare (-13/320) (-123/320) (1/320) tau := by
                convert childLR hs011102 hx011102 hy011102 using 1 <;> norm_num
              rcases le_total tau.re (-13/320 : ℝ) with hx0111021 | hx0111021
              · rcases le_total tau.im (-123/320 : ℝ) with hy0111021 | hy0111021
                · have hs01110210 : InSquare (-27/640) (-247/640) (1/640) tau := by
                    convert childLL hs0111021 hx0111021 hy0111021 using 1 <;> norm_num
                  exact Batch0355.cell2844.sound htau (by
                    simp only [Batch0355.cell2844, Batch0355.tau2844, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110210 (by positivity) using 1 <;> norm_num)
                · have hs01110212 : InSquare (-27/640) (-49/128) (1/640) tau := by
                    convert childUL hs0111021 hx0111021 hy0111021 using 1 <;> norm_num
                  exact Batch0355.cell2846.sound htau (by
                    simp only [Batch0355.cell2846, Batch0355.tau2846, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0111021 | hy0111021
                · have hs01110211 : InSquare (-5/128) (-247/640) (1/640) tau := by
                    convert childLR hs0111021 hx0111021 hy0111021 using 1 <;> norm_num
                  exact Batch0355.cell2845.sound htau (by
                    simp only [Batch0355.cell2845, Batch0355.tau2845, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110211 (by positivity) using 1 <;> norm_num)
                · have hs01110213 : InSquare (-5/128) (-49/128) (1/640) tau := by
                    convert childUR hs0111021 hx0111021 hy0111021 using 1 <;> norm_num
                  exact Batch0355.cell2847.sound htau (by
                    simp only [Batch0355.cell2847, Batch0355.tau2847, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110213 (by positivity) using 1 <;> norm_num)
            · have hs0111023 : InSquare (-13/320) (-121/320) (1/320) tau := by
                convert childUR hs011102 hx011102 hy011102 using 1 <;> norm_num
              exact Batch0186.cell1488.sound htau (by
                simp only [Batch0186.cell1488, Batch0186.tau1488, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy01110 | hy01110
        · have hs011101 : InSquare (-1/32) (-63/160) (1/160) tau := by
            convert childLR hs01110 hx01110 hy01110 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx011101 | hx011101
          · rcases le_total tau.im (-63/160 : ℝ) with hy011101 | hy011101
            · have hs0111010 : InSquare (-11/320) (-127/320) (1/320) tau := by
                convert childLL hs011101 hx011101 hy011101 using 1 <;> norm_num
              rcases le_total tau.re (-11/320 : ℝ) with hx0111010 | hx0111010
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111010 | hy0111010
                · have hs01110100 : InSquare (-23/640) (-51/128) (1/640) tau := by
                    convert childLL hs0111010 hx0111010 hy0111010 using 1 <;> norm_num
                  exact Batch0353.cell2824.sound htau (by
                    simp only [Batch0353.cell2824, Batch0353.tau2824, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110100 (by positivity) using 1 <;> norm_num)
                · have hs01110102 : InSquare (-23/640) (-253/640) (1/640) tau := by
                    convert childUL hs0111010 hx0111010 hy0111010 using 1 <;> norm_num
                  exact Batch0353.cell2826.sound htau (by
                    simp only [Batch0353.cell2826, Batch0353.tau2826, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111010 | hy0111010
                · have hs01110101 : InSquare (-21/640) (-51/128) (1/640) tau := by
                    convert childLR hs0111010 hx0111010 hy0111010 using 1 <;> norm_num
                  exact Batch0353.cell2825.sound htau (by
                    simp only [Batch0353.cell2825, Batch0353.tau2825, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110101 (by positivity) using 1 <;> norm_num)
                · have hs01110103 : InSquare (-21/640) (-253/640) (1/640) tau := by
                    convert childUR hs0111010 hx0111010 hy0111010 using 1 <;> norm_num
                  exact Batch0353.cell2827.sound htau (by
                    simp only [Batch0353.cell2827, Batch0353.tau2827, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110103 (by positivity) using 1 <;> norm_num)
            · have hs0111012 : InSquare (-11/320) (-25/64) (1/320) tau := by
                convert childUL hs011101 hx011101 hy011101 using 1 <;> norm_num
              rcases le_total tau.re (-11/320 : ℝ) with hx0111012 | hx0111012
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111012 | hy0111012
                · have hs01110120 : InSquare (-23/640) (-251/640) (1/640) tau := by
                    convert childLL hs0111012 hx0111012 hy0111012 using 1 <;> norm_num
                  exact Batch0354.cell2832.sound htau (by
                    simp only [Batch0354.cell2832, Batch0354.tau2832, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110120 (by positivity) using 1 <;> norm_num)
                · have hs01110122 : InSquare (-23/640) (-249/640) (1/640) tau := by
                    convert childUL hs0111012 hx0111012 hy0111012 using 1 <;> norm_num
                  exact Batch0354.cell2834.sound htau (by
                    simp only [Batch0354.cell2834, Batch0354.tau2834, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111012 | hy0111012
                · have hs01110121 : InSquare (-21/640) (-251/640) (1/640) tau := by
                    convert childLR hs0111012 hx0111012 hy0111012 using 1 <;> norm_num
                  exact Batch0354.cell2833.sound htau (by
                    simp only [Batch0354.cell2833, Batch0354.tau2833, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110121 (by positivity) using 1 <;> norm_num)
                · have hs01110123 : InSquare (-21/640) (-249/640) (1/640) tau := by
                    convert childUR hs0111012 hx0111012 hy0111012 using 1 <;> norm_num
                  exact Batch0354.cell2835.sound htau (by
                    simp only [Batch0354.cell2835, Batch0354.tau2835, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011101 | hy011101
            · have hs0111011 : InSquare (-9/320) (-127/320) (1/320) tau := by
                convert childLR hs011101 hx011101 hy011101 using 1 <;> norm_num
              rcases le_total tau.re (-9/320 : ℝ) with hx0111011 | hx0111011
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111011 | hy0111011
                · have hs01110110 : InSquare (-19/640) (-51/128) (1/640) tau := by
                    convert childLL hs0111011 hx0111011 hy0111011 using 1 <;> norm_num
                  exact Batch0353.cell2828.sound htau (by
                    simp only [Batch0353.cell2828, Batch0353.tau2828, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110110 (by positivity) using 1 <;> norm_num)
                · have hs01110112 : InSquare (-19/640) (-253/640) (1/640) tau := by
                    convert childUL hs0111011 hx0111011 hy0111011 using 1 <;> norm_num
                  exact Batch0353.cell2830.sound htau (by
                    simp only [Batch0353.cell2830, Batch0353.tau2830, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111011 | hy0111011
                · have hs01110111 : InSquare (-17/640) (-51/128) (1/640) tau := by
                    convert childLR hs0111011 hx0111011 hy0111011 using 1 <;> norm_num
                  exact Batch0353.cell2829.sound htau (by
                    simp only [Batch0353.cell2829, Batch0353.tau2829, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110111 (by positivity) using 1 <;> norm_num)
                · have hs01110113 : InSquare (-17/640) (-253/640) (1/640) tau := by
                    convert childUR hs0111011 hx0111011 hy0111011 using 1 <;> norm_num
                  exact Batch0353.cell2831.sound htau (by
                    simp only [Batch0353.cell2831, Batch0353.tau2831, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110113 (by positivity) using 1 <;> norm_num)
            · have hs0111013 : InSquare (-9/320) (-25/64) (1/320) tau := by
                convert childUR hs011101 hx011101 hy011101 using 1 <;> norm_num
              rcases le_total tau.re (-9/320 : ℝ) with hx0111013 | hx0111013
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111013 | hy0111013
                · have hs01110130 : InSquare (-19/640) (-251/640) (1/640) tau := by
                    convert childLL hs0111013 hx0111013 hy0111013 using 1 <;> norm_num
                  exact Batch0354.cell2836.sound htau (by
                    simp only [Batch0354.cell2836, Batch0354.tau2836, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110130 (by positivity) using 1 <;> norm_num)
                · have hs01110132 : InSquare (-19/640) (-249/640) (1/640) tau := by
                    convert childUL hs0111013 hx0111013 hy0111013 using 1 <;> norm_num
                  exact Batch0354.cell2838.sound htau (by
                    simp only [Batch0354.cell2838, Batch0354.tau2838, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111013 | hy0111013
                · have hs01110131 : InSquare (-17/640) (-251/640) (1/640) tau := by
                    convert childLR hs0111013 hx0111013 hy0111013 using 1 <;> norm_num
                  exact Batch0354.cell2837.sound htau (by
                    simp only [Batch0354.cell2837, Batch0354.tau2837, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110131 (by positivity) using 1 <;> norm_num)
                · have hs01110133 : InSquare (-17/640) (-249/640) (1/640) tau := by
                    convert childUR hs0111013 hx0111013 hy0111013 using 1 <;> norm_num
                  exact Batch0354.cell2839.sound htau (by
                    simp only [Batch0354.cell2839, Batch0354.tau2839, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110133 (by positivity) using 1 <;> norm_num)
        · have hs011103 : InSquare (-1/32) (-61/160) (1/160) tau := by
            convert childUR hs01110 hx01110 hy01110 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx011103 | hx011103
          · rcases le_total tau.im (-61/160 : ℝ) with hy011103 | hy011103
            · have hs0111030 : InSquare (-11/320) (-123/320) (1/320) tau := by
                convert childLL hs011103 hx011103 hy011103 using 1 <;> norm_num
              rcases le_total tau.re (-11/320 : ℝ) with hx0111030 | hx0111030
              · rcases le_total tau.im (-123/320 : ℝ) with hy0111030 | hy0111030
                · have hs01110300 : InSquare (-23/640) (-247/640) (1/640) tau := by
                    convert childLL hs0111030 hx0111030 hy0111030 using 1 <;> norm_num
                  exact Batch0356.cell2848.sound htau (by
                    simp only [Batch0356.cell2848, Batch0356.tau2848, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110300 (by positivity) using 1 <;> norm_num)
                · have hs01110302 : InSquare (-23/640) (-49/128) (1/640) tau := by
                    convert childUL hs0111030 hx0111030 hy0111030 using 1 <;> norm_num
                  exact Batch0356.cell2850.sound htau (by
                    simp only [Batch0356.cell2850, Batch0356.tau2850, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0111030 | hy0111030
                · have hs01110301 : InSquare (-21/640) (-247/640) (1/640) tau := by
                    convert childLR hs0111030 hx0111030 hy0111030 using 1 <;> norm_num
                  exact Batch0356.cell2849.sound htau (by
                    simp only [Batch0356.cell2849, Batch0356.tau2849, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110301 (by positivity) using 1 <;> norm_num)
                · have hs01110303 : InSquare (-21/640) (-49/128) (1/640) tau := by
                    convert childUR hs0111030 hx0111030 hy0111030 using 1 <;> norm_num
                  exact Batch0356.cell2851.sound htau (by
                    simp only [Batch0356.cell2851, Batch0356.tau2851, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110303 (by positivity) using 1 <;> norm_num)
            · have hs0111032 : InSquare (-11/320) (-121/320) (1/320) tau := by
                convert childUL hs011103 hx011103 hy011103 using 1 <;> norm_num
              exact Batch0186.cell1490.sound htau (by
                simp only [Batch0186.cell1490, Batch0186.tau1490, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011103 | hy011103
            · have hs0111031 : InSquare (-9/320) (-123/320) (1/320) tau := by
                convert childLR hs011103 hx011103 hy011103 using 1 <;> norm_num
              exact Batch0186.cell1489.sound htau (by
                simp only [Batch0186.cell1489, Batch0186.tau1489, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111031 (by positivity) using 1 <;> norm_num)
            · have hs0111033 : InSquare (-9/320) (-121/320) (1/320) tau := by
                convert childUR hs011103 hx011103 hy011103 using 1 <;> norm_num
              exact Batch0186.cell1491.sound htau (by
                simp only [Batch0186.cell1491, Batch0186.tau1491, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111033 (by positivity) using 1 <;> norm_num)
    · have hs01112 : InSquare (-3/80) (-29/80) (1/80) tau := by
        convert childUL hs hx0111 hy0111 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx01112 | hx01112
      · rcases le_total tau.im (-29/80 : ℝ) with hy01112 | hy01112
        · have hs011120 : InSquare (-7/160) (-59/160) (1/160) tau := by
            convert childLL hs01112 hx01112 hy01112 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx011120 | hx011120
          · rcases le_total tau.im (-59/160 : ℝ) with hy011120 | hy011120
            · have hs0111200 : InSquare (-3/64) (-119/320) (1/320) tau := by
                convert childLL hs011120 hx011120 hy011120 using 1 <;> norm_num
              exact Batch0187.cell1500.sound htau (by
                simp only [Batch0187.cell1500, Batch0187.tau1500, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111200 (by positivity) using 1 <;> norm_num)
            · have hs0111202 : InSquare (-3/64) (-117/320) (1/320) tau := by
                convert childUL hs011120 hx011120 hy011120 using 1 <;> norm_num
              exact Batch0187.cell1502.sound htau (by
                simp only [Batch0187.cell1502, Batch0187.tau1502, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011120 | hy011120
            · have hs0111201 : InSquare (-13/320) (-119/320) (1/320) tau := by
                convert childLR hs011120 hx011120 hy011120 using 1 <;> norm_num
              exact Batch0187.cell1501.sound htau (by
                simp only [Batch0187.cell1501, Batch0187.tau1501, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111201 (by positivity) using 1 <;> norm_num)
            · have hs0111203 : InSquare (-13/320) (-117/320) (1/320) tau := by
                convert childUR hs011120 hx011120 hy011120 using 1 <;> norm_num
              exact Batch0187.cell1503.sound htau (by
                simp only [Batch0187.cell1503, Batch0187.tau1503, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111203 (by positivity) using 1 <;> norm_num)
        · have hs011122 : InSquare (-7/160) (-57/160) (1/160) tau := by
            convert childUL hs01112 hx01112 hy01112 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx011122 | hx011122
          · rcases le_total tau.im (-57/160 : ℝ) with hy011122 | hy011122
            · have hs0111220 : InSquare (-3/64) (-23/64) (1/320) tau := by
                convert childLL hs011122 hx011122 hy011122 using 1 <;> norm_num
              exact Batch0188.cell1508.sound htau (by
                simp only [Batch0188.cell1508, Batch0188.tau1508, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111220 (by positivity) using 1 <;> norm_num)
            · have hs0111222 : InSquare (-3/64) (-113/320) (1/320) tau := by
                convert childUL hs011122 hx011122 hy011122 using 1 <;> norm_num
              exact Batch0188.cell1510.sound htau (by
                simp only [Batch0188.cell1510, Batch0188.tau1510, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy011122 | hy011122
            · have hs0111221 : InSquare (-13/320) (-23/64) (1/320) tau := by
                convert childLR hs011122 hx011122 hy011122 using 1 <;> norm_num
              exact Batch0188.cell1509.sound htau (by
                simp only [Batch0188.cell1509, Batch0188.tau1509, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111221 (by positivity) using 1 <;> norm_num)
            · have hs0111223 : InSquare (-13/320) (-113/320) (1/320) tau := by
                convert childUR hs011122 hx011122 hy011122 using 1 <;> norm_num
              exact Batch0188.cell1511.sound htau (by
                simp only [Batch0188.cell1511, Batch0188.tau1511, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01112 | hy01112
        · have hs011121 : InSquare (-1/32) (-59/160) (1/160) tau := by
            convert childLR hs01112 hx01112 hy01112 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx011121 | hx011121
          · rcases le_total tau.im (-59/160 : ℝ) with hy011121 | hy011121
            · have hs0111210 : InSquare (-11/320) (-119/320) (1/320) tau := by
                convert childLL hs011121 hx011121 hy011121 using 1 <;> norm_num
              exact Batch0188.cell1504.sound htau (by
                simp only [Batch0188.cell1504, Batch0188.tau1504, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111210 (by positivity) using 1 <;> norm_num)
            · have hs0111212 : InSquare (-11/320) (-117/320) (1/320) tau := by
                convert childUL hs011121 hx011121 hy011121 using 1 <;> norm_num
              exact Batch0188.cell1506.sound htau (by
                simp only [Batch0188.cell1506, Batch0188.tau1506, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011121 | hy011121
            · have hs0111211 : InSquare (-9/320) (-119/320) (1/320) tau := by
                convert childLR hs011121 hx011121 hy011121 using 1 <;> norm_num
              exact Batch0188.cell1505.sound htau (by
                simp only [Batch0188.cell1505, Batch0188.tau1505, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111211 (by positivity) using 1 <;> norm_num)
            · have hs0111213 : InSquare (-9/320) (-117/320) (1/320) tau := by
                convert childUR hs011121 hx011121 hy011121 using 1 <;> norm_num
              exact Batch0188.cell1507.sound htau (by
                simp only [Batch0188.cell1507, Batch0188.tau1507, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111213 (by positivity) using 1 <;> norm_num)
        · have hs011123 : InSquare (-1/32) (-57/160) (1/160) tau := by
            convert childUR hs01112 hx01112 hy01112 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx011123 | hx011123
          · rcases le_total tau.im (-57/160 : ℝ) with hy011123 | hy011123
            · have hs0111230 : InSquare (-11/320) (-23/64) (1/320) tau := by
                convert childLL hs011123 hx011123 hy011123 using 1 <;> norm_num
              exact Batch0189.cell1512.sound htau (by
                simp only [Batch0189.cell1512, Batch0189.tau1512, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111230 (by positivity) using 1 <;> norm_num)
            · have hs0111232 : InSquare (-11/320) (-113/320) (1/320) tau := by
                convert childUL hs011123 hx011123 hy011123 using 1 <;> norm_num
              exact Batch0189.cell1514.sound htau (by
                simp only [Batch0189.cell1514, Batch0189.tau1514, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy011123 | hy011123
            · have hs0111231 : InSquare (-9/320) (-23/64) (1/320) tau := by
                convert childLR hs011123 hx011123 hy011123 using 1 <;> norm_num
              exact Batch0189.cell1513.sound htau (by
                simp only [Batch0189.cell1513, Batch0189.tau1513, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111231 (by positivity) using 1 <;> norm_num)
            · have hs0111233 : InSquare (-9/320) (-113/320) (1/320) tau := by
                convert childUR hs011123 hx011123 hy011123 using 1 <;> norm_num
              exact Batch0189.cell1515.sound htau (by
                simp only [Batch0189.cell1515, Batch0189.tau1515, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/8 : ℝ) with hy0111 | hy0111
    · have hs01111 : InSquare (-1/80) (-31/80) (1/80) tau := by
        convert childLR hs hx0111 hy0111 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx01111 | hx01111
      · rcases le_total tau.im (-31/80 : ℝ) with hy01111 | hy01111
        · have hs011110 : InSquare (-3/160) (-63/160) (1/160) tau := by
            convert childLL hs01111 hx01111 hy01111 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx011110 | hx011110
          · rcases le_total tau.im (-63/160 : ℝ) with hy011110 | hy011110
            · have hs0111100 : InSquare (-7/320) (-127/320) (1/320) tau := by
                convert childLL hs011110 hx011110 hy011110 using 1 <;> norm_num
              rcases le_total tau.re (-7/320 : ℝ) with hx0111100 | hx0111100
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111100 | hy0111100
                · have hs01111000 : InSquare (-3/128) (-51/128) (1/640) tau := by
                    convert childLL hs0111100 hx0111100 hy0111100 using 1 <;> norm_num
                  exact Batch0356.cell2852.sound htau (by
                    simp only [Batch0356.cell2852, Batch0356.tau2852, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111000 (by positivity) using 1 <;> norm_num)
                · have hs01111002 : InSquare (-3/128) (-253/640) (1/640) tau := by
                    convert childUL hs0111100 hx0111100 hy0111100 using 1 <;> norm_num
                  exact Batch0356.cell2854.sound htau (by
                    simp only [Batch0356.cell2854, Batch0356.tau2854, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111100 | hy0111100
                · have hs01111001 : InSquare (-13/640) (-51/128) (1/640) tau := by
                    convert childLR hs0111100 hx0111100 hy0111100 using 1 <;> norm_num
                  exact Batch0356.cell2853.sound htau (by
                    simp only [Batch0356.cell2853, Batch0356.tau2853, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111001 (by positivity) using 1 <;> norm_num)
                · have hs01111003 : InSquare (-13/640) (-253/640) (1/640) tau := by
                    convert childUR hs0111100 hx0111100 hy0111100 using 1 <;> norm_num
                  exact Batch0356.cell2855.sound htau (by
                    simp only [Batch0356.cell2855, Batch0356.tau2855, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111003 (by positivity) using 1 <;> norm_num)
            · have hs0111102 : InSquare (-7/320) (-25/64) (1/320) tau := by
                convert childUL hs011110 hx011110 hy011110 using 1 <;> norm_num
              rcases le_total tau.re (-7/320 : ℝ) with hx0111102 | hx0111102
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111102 | hy0111102
                · have hs01111020 : InSquare (-3/128) (-251/640) (1/640) tau := by
                    convert childLL hs0111102 hx0111102 hy0111102 using 1 <;> norm_num
                  exact Batch0357.cell2860.sound htau (by
                    simp only [Batch0357.cell2860, Batch0357.tau2860, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111020 (by positivity) using 1 <;> norm_num)
                · have hs01111022 : InSquare (-3/128) (-249/640) (1/640) tau := by
                    convert childUL hs0111102 hx0111102 hy0111102 using 1 <;> norm_num
                  exact Batch0357.cell2862.sound htau (by
                    simp only [Batch0357.cell2862, Batch0357.tau2862, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111102 | hy0111102
                · have hs01111021 : InSquare (-13/640) (-251/640) (1/640) tau := by
                    convert childLR hs0111102 hx0111102 hy0111102 using 1 <;> norm_num
                  exact Batch0357.cell2861.sound htau (by
                    simp only [Batch0357.cell2861, Batch0357.tau2861, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111021 (by positivity) using 1 <;> norm_num)
                · have hs01111023 : InSquare (-13/640) (-249/640) (1/640) tau := by
                    convert childUR hs0111102 hx0111102 hy0111102 using 1 <;> norm_num
                  exact Batch0357.cell2863.sound htau (by
                    simp only [Batch0357.cell2863, Batch0357.tau2863, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011110 | hy011110
            · have hs0111101 : InSquare (-1/64) (-127/320) (1/320) tau := by
                convert childLR hs011110 hx011110 hy011110 using 1 <;> norm_num
              rcases le_total tau.re (-1/64 : ℝ) with hx0111101 | hx0111101
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111101 | hy0111101
                · have hs01111010 : InSquare (-11/640) (-51/128) (1/640) tau := by
                    convert childLL hs0111101 hx0111101 hy0111101 using 1 <;> norm_num
                  exact Batch0357.cell2856.sound htau (by
                    simp only [Batch0357.cell2856, Batch0357.tau2856, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111010 (by positivity) using 1 <;> norm_num)
                · have hs01111012 : InSquare (-11/640) (-253/640) (1/640) tau := by
                    convert childUL hs0111101 hx0111101 hy0111101 using 1 <;> norm_num
                  exact Batch0357.cell2858.sound htau (by
                    simp only [Batch0357.cell2858, Batch0357.tau2858, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111101 | hy0111101
                · have hs01111011 : InSquare (-9/640) (-51/128) (1/640) tau := by
                    convert childLR hs0111101 hx0111101 hy0111101 using 1 <;> norm_num
                  exact Batch0357.cell2857.sound htau (by
                    simp only [Batch0357.cell2857, Batch0357.tau2857, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111011 (by positivity) using 1 <;> norm_num)
                · have hs01111013 : InSquare (-9/640) (-253/640) (1/640) tau := by
                    convert childUR hs0111101 hx0111101 hy0111101 using 1 <;> norm_num
                  exact Batch0357.cell2859.sound htau (by
                    simp only [Batch0357.cell2859, Batch0357.tau2859, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111013 (by positivity) using 1 <;> norm_num)
            · have hs0111103 : InSquare (-1/64) (-25/64) (1/320) tau := by
                convert childUR hs011110 hx011110 hy011110 using 1 <;> norm_num
              rcases le_total tau.re (-1/64 : ℝ) with hx0111103 | hx0111103
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111103 | hy0111103
                · have hs01111030 : InSquare (-11/640) (-251/640) (1/640) tau := by
                    convert childLL hs0111103 hx0111103 hy0111103 using 1 <;> norm_num
                  exact Batch0358.cell2864.sound htau (by
                    simp only [Batch0358.cell2864, Batch0358.tau2864, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111030 (by positivity) using 1 <;> norm_num)
                · have hs01111032 : InSquare (-11/640) (-249/640) (1/640) tau := by
                    convert childUL hs0111103 hx0111103 hy0111103 using 1 <;> norm_num
                  exact Batch0358.cell2866.sound htau (by
                    simp only [Batch0358.cell2866, Batch0358.tau2866, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111103 | hy0111103
                · have hs01111031 : InSquare (-9/640) (-251/640) (1/640) tau := by
                    convert childLR hs0111103 hx0111103 hy0111103 using 1 <;> norm_num
                  exact Batch0358.cell2865.sound htau (by
                    simp only [Batch0358.cell2865, Batch0358.tau2865, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111031 (by positivity) using 1 <;> norm_num)
                · have hs01111033 : InSquare (-9/640) (-249/640) (1/640) tau := by
                    convert childUR hs0111103 hx0111103 hy0111103 using 1 <;> norm_num
                  exact Batch0358.cell2867.sound htau (by
                    simp only [Batch0358.cell2867, Batch0358.tau2867, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111033 (by positivity) using 1 <;> norm_num)
        · have hs011112 : InSquare (-3/160) (-61/160) (1/160) tau := by
            convert childUL hs01111 hx01111 hy01111 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx011112 | hx011112
          · rcases le_total tau.im (-61/160 : ℝ) with hy011112 | hy011112
            · have hs0111120 : InSquare (-7/320) (-123/320) (1/320) tau := by
                convert childLL hs011112 hx011112 hy011112 using 1 <;> norm_num
              exact Batch0186.cell1492.sound htau (by
                simp only [Batch0186.cell1492, Batch0186.tau1492, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111120 (by positivity) using 1 <;> norm_num)
            · have hs0111122 : InSquare (-7/320) (-121/320) (1/320) tau := by
                convert childUL hs011112 hx011112 hy011112 using 1 <;> norm_num
              exact Batch0186.cell1494.sound htau (by
                simp only [Batch0186.cell1494, Batch0186.tau1494, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011112 | hy011112
            · have hs0111121 : InSquare (-1/64) (-123/320) (1/320) tau := by
                convert childLR hs011112 hx011112 hy011112 using 1 <;> norm_num
              exact Batch0186.cell1493.sound htau (by
                simp only [Batch0186.cell1493, Batch0186.tau1493, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111121 (by positivity) using 1 <;> norm_num)
            · have hs0111123 : InSquare (-1/64) (-121/320) (1/320) tau := by
                convert childUR hs011112 hx011112 hy011112 using 1 <;> norm_num
              exact Batch0186.cell1495.sound htau (by
                simp only [Batch0186.cell1495, Batch0186.tau1495, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy01111 | hy01111
        · have hs011111 : InSquare (-1/160) (-63/160) (1/160) tau := by
            convert childLR hs01111 hx01111 hy01111 using 1 <;> norm_num
          rcases le_total tau.re (-1/160 : ℝ) with hx011111 | hx011111
          · rcases le_total tau.im (-63/160 : ℝ) with hy011111 | hy011111
            · have hs0111110 : InSquare (-3/320) (-127/320) (1/320) tau := by
                convert childLL hs011111 hx011111 hy011111 using 1 <;> norm_num
              rcases le_total tau.re (-3/320 : ℝ) with hx0111110 | hx0111110
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111110 | hy0111110
                · have hs01111100 : InSquare (-7/640) (-51/128) (1/640) tau := by
                    convert childLL hs0111110 hx0111110 hy0111110 using 1 <;> norm_num
                  exact Batch0358.cell2868.sound htau (by
                    simp only [Batch0358.cell2868, Batch0358.tau2868, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111100 (by positivity) using 1 <;> norm_num)
                · have hs01111102 : InSquare (-7/640) (-253/640) (1/640) tau := by
                    convert childUL hs0111110 hx0111110 hy0111110 using 1 <;> norm_num
                  exact Batch0358.cell2870.sound htau (by
                    simp only [Batch0358.cell2870, Batch0358.tau2870, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111110 | hy0111110
                · have hs01111101 : InSquare (-1/128) (-51/128) (1/640) tau := by
                    convert childLR hs0111110 hx0111110 hy0111110 using 1 <;> norm_num
                  exact Batch0358.cell2869.sound htau (by
                    simp only [Batch0358.cell2869, Batch0358.tau2869, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111101 (by positivity) using 1 <;> norm_num)
                · have hs01111103 : InSquare (-1/128) (-253/640) (1/640) tau := by
                    convert childUR hs0111110 hx0111110 hy0111110 using 1 <;> norm_num
                  exact Batch0358.cell2871.sound htau (by
                    simp only [Batch0358.cell2871, Batch0358.tau2871, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111103 (by positivity) using 1 <;> norm_num)
            · have hs0111112 : InSquare (-3/320) (-25/64) (1/320) tau := by
                convert childUL hs011111 hx011111 hy011111 using 1 <;> norm_num
              rcases le_total tau.re (-3/320 : ℝ) with hx0111112 | hx0111112
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111112 | hy0111112
                · have hs01111120 : InSquare (-7/640) (-251/640) (1/640) tau := by
                    convert childLL hs0111112 hx0111112 hy0111112 using 1 <;> norm_num
                  exact Batch0359.cell2876.sound htau (by
                    simp only [Batch0359.cell2876, Batch0359.tau2876, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111120 (by positivity) using 1 <;> norm_num)
                · have hs01111122 : InSquare (-7/640) (-249/640) (1/640) tau := by
                    convert childUL hs0111112 hx0111112 hy0111112 using 1 <;> norm_num
                  exact Batch0359.cell2878.sound htau (by
                    simp only [Batch0359.cell2878, Batch0359.tau2878, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111112 | hy0111112
                · have hs01111121 : InSquare (-1/128) (-251/640) (1/640) tau := by
                    convert childLR hs0111112 hx0111112 hy0111112 using 1 <;> norm_num
                  exact Batch0359.cell2877.sound htau (by
                    simp only [Batch0359.cell2877, Batch0359.tau2877, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111121 (by positivity) using 1 <;> norm_num)
                · have hs01111123 : InSquare (-1/128) (-249/640) (1/640) tau := by
                    convert childUR hs0111112 hx0111112 hy0111112 using 1 <;> norm_num
                  exact Batch0359.cell2879.sound htau (by
                    simp only [Batch0359.cell2879, Batch0359.tau2879, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011111 | hy011111
            · have hs0111111 : InSquare (-1/320) (-127/320) (1/320) tau := by
                convert childLR hs011111 hx011111 hy011111 using 1 <;> norm_num
              rcases le_total tau.re (-1/320 : ℝ) with hx0111111 | hx0111111
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111111 | hy0111111
                · have hs01111110 : InSquare (-3/640) (-51/128) (1/640) tau := by
                    convert childLL hs0111111 hx0111111 hy0111111 using 1 <;> norm_num
                  exact Batch0359.cell2872.sound htau (by
                    simp only [Batch0359.cell2872, Batch0359.tau2872, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111110 (by positivity) using 1 <;> norm_num)
                · have hs01111112 : InSquare (-3/640) (-253/640) (1/640) tau := by
                    convert childUL hs0111111 hx0111111 hy0111111 using 1 <;> norm_num
                  exact Batch0359.cell2874.sound htau (by
                    simp only [Batch0359.cell2874, Batch0359.tau2874, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111111 | hy0111111
                · have hs01111111 : InSquare (-1/640) (-51/128) (1/640) tau := by
                    convert childLR hs0111111 hx0111111 hy0111111 using 1 <;> norm_num
                  exact Batch0359.cell2873.sound htau (by
                    simp only [Batch0359.cell2873, Batch0359.tau2873, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111111 (by positivity) using 1 <;> norm_num)
                · have hs01111113 : InSquare (-1/640) (-253/640) (1/640) tau := by
                    convert childUR hs0111111 hx0111111 hy0111111 using 1 <;> norm_num
                  exact Batch0359.cell2875.sound htau (by
                    simp only [Batch0359.cell2875, Batch0359.tau2875, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111113 (by positivity) using 1 <;> norm_num)
            · have hs0111113 : InSquare (-1/320) (-25/64) (1/320) tau := by
                convert childUR hs011111 hx011111 hy011111 using 1 <;> norm_num
              rcases le_total tau.re (-1/320 : ℝ) with hx0111113 | hx0111113
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111113 | hy0111113
                · have hs01111130 : InSquare (-3/640) (-251/640) (1/640) tau := by
                    convert childLL hs0111113 hx0111113 hy0111113 using 1 <;> norm_num
                  exact Batch0360.cell2880.sound htau (by
                    simp only [Batch0360.cell2880, Batch0360.tau2880, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111130 (by positivity) using 1 <;> norm_num)
                · have hs01111132 : InSquare (-3/640) (-249/640) (1/640) tau := by
                    convert childUL hs0111113 hx0111113 hy0111113 using 1 <;> norm_num
                  exact Batch0360.cell2882.sound htau (by
                    simp only [Batch0360.cell2882, Batch0360.tau2882, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111113 | hy0111113
                · have hs01111131 : InSquare (-1/640) (-251/640) (1/640) tau := by
                    convert childLR hs0111113 hx0111113 hy0111113 using 1 <;> norm_num
                  exact Batch0360.cell2881.sound htau (by
                    simp only [Batch0360.cell2881, Batch0360.tau2881, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111131 (by positivity) using 1 <;> norm_num)
                · have hs01111133 : InSquare (-1/640) (-249/640) (1/640) tau := by
                    convert childUR hs0111113 hx0111113 hy0111113 using 1 <;> norm_num
                  exact Batch0360.cell2883.sound htau (by
                    simp only [Batch0360.cell2883, Batch0360.tau2883, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111133 (by positivity) using 1 <;> norm_num)
        · have hs011113 : InSquare (-1/160) (-61/160) (1/160) tau := by
            convert childUR hs01111 hx01111 hy01111 using 1 <;> norm_num
          rcases le_total tau.re (-1/160 : ℝ) with hx011113 | hx011113
          · rcases le_total tau.im (-61/160 : ℝ) with hy011113 | hy011113
            · have hs0111130 : InSquare (-3/320) (-123/320) (1/320) tau := by
                convert childLL hs011113 hx011113 hy011113 using 1 <;> norm_num
              exact Batch0187.cell1496.sound htau (by
                simp only [Batch0187.cell1496, Batch0187.tau1496, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111130 (by positivity) using 1 <;> norm_num)
            · have hs0111132 : InSquare (-3/320) (-121/320) (1/320) tau := by
                convert childUL hs011113 hx011113 hy011113 using 1 <;> norm_num
              exact Batch0187.cell1498.sound htau (by
                simp only [Batch0187.cell1498, Batch0187.tau1498, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011113 | hy011113
            · have hs0111131 : InSquare (-1/320) (-123/320) (1/320) tau := by
                convert childLR hs011113 hx011113 hy011113 using 1 <;> norm_num
              exact Batch0187.cell1497.sound htau (by
                simp only [Batch0187.cell1497, Batch0187.tau1497, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111131 (by positivity) using 1 <;> norm_num)
            · have hs0111133 : InSquare (-1/320) (-121/320) (1/320) tau := by
                convert childUR hs011113 hx011113 hy011113 using 1 <;> norm_num
              exact Batch0187.cell1499.sound htau (by
                simp only [Batch0187.cell1499, Batch0187.tau1499, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111133 (by positivity) using 1 <;> norm_num)
    · have hs01113 : InSquare (-1/80) (-29/80) (1/80) tau := by
        convert childUR hs hx0111 hy0111 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx01113 | hx01113
      · rcases le_total tau.im (-29/80 : ℝ) with hy01113 | hy01113
        · have hs011130 : InSquare (-3/160) (-59/160) (1/160) tau := by
            convert childLL hs01113 hx01113 hy01113 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx011130 | hx011130
          · rcases le_total tau.im (-59/160 : ℝ) with hy011130 | hy011130
            · have hs0111300 : InSquare (-7/320) (-119/320) (1/320) tau := by
                convert childLL hs011130 hx011130 hy011130 using 1 <;> norm_num
              exact Batch0189.cell1516.sound htau (by
                simp only [Batch0189.cell1516, Batch0189.tau1516, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111300 (by positivity) using 1 <;> norm_num)
            · have hs0111302 : InSquare (-7/320) (-117/320) (1/320) tau := by
                convert childUL hs011130 hx011130 hy011130 using 1 <;> norm_num
              exact Batch0189.cell1518.sound htau (by
                simp only [Batch0189.cell1518, Batch0189.tau1518, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011130 | hy011130
            · have hs0111301 : InSquare (-1/64) (-119/320) (1/320) tau := by
                convert childLR hs011130 hx011130 hy011130 using 1 <;> norm_num
              exact Batch0189.cell1517.sound htau (by
                simp only [Batch0189.cell1517, Batch0189.tau1517, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111301 (by positivity) using 1 <;> norm_num)
            · have hs0111303 : InSquare (-1/64) (-117/320) (1/320) tau := by
                convert childUR hs011130 hx011130 hy011130 using 1 <;> norm_num
              exact Batch0189.cell1519.sound htau (by
                simp only [Batch0189.cell1519, Batch0189.tau1519, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111303 (by positivity) using 1 <;> norm_num)
        · have hs011132 : InSquare (-3/160) (-57/160) (1/160) tau := by
            convert childUL hs01113 hx01113 hy01113 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx011132 | hx011132
          · rcases le_total tau.im (-57/160 : ℝ) with hy011132 | hy011132
            · have hs0111320 : InSquare (-7/320) (-23/64) (1/320) tau := by
                convert childLL hs011132 hx011132 hy011132 using 1 <;> norm_num
              exact Batch0190.cell1524.sound htau (by
                simp only [Batch0190.cell1524, Batch0190.tau1524, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111320 (by positivity) using 1 <;> norm_num)
            · have hs0111322 : InSquare (-7/320) (-113/320) (1/320) tau := by
                convert childUL hs011132 hx011132 hy011132 using 1 <;> norm_num
              exact Batch0190.cell1526.sound htau (by
                simp only [Batch0190.cell1526, Batch0190.tau1526, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy011132 | hy011132
            · have hs0111321 : InSquare (-1/64) (-23/64) (1/320) tau := by
                convert childLR hs011132 hx011132 hy011132 using 1 <;> norm_num
              exact Batch0190.cell1525.sound htau (by
                simp only [Batch0190.cell1525, Batch0190.tau1525, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111321 (by positivity) using 1 <;> norm_num)
            · have hs0111323 : InSquare (-1/64) (-113/320) (1/320) tau := by
                convert childUR hs011132 hx011132 hy011132 using 1 <;> norm_num
              exact Batch0190.cell1527.sound htau (by
                simp only [Batch0190.cell1527, Batch0190.tau1527, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01113 | hy01113
        · have hs011131 : InSquare (-1/160) (-59/160) (1/160) tau := by
            convert childLR hs01113 hx01113 hy01113 using 1 <;> norm_num
          rcases le_total tau.re (-1/160 : ℝ) with hx011131 | hx011131
          · rcases le_total tau.im (-59/160 : ℝ) with hy011131 | hy011131
            · have hs0111310 : InSquare (-3/320) (-119/320) (1/320) tau := by
                convert childLL hs011131 hx011131 hy011131 using 1 <;> norm_num
              exact Batch0190.cell1520.sound htau (by
                simp only [Batch0190.cell1520, Batch0190.tau1520, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111310 (by positivity) using 1 <;> norm_num)
            · have hs0111312 : InSquare (-3/320) (-117/320) (1/320) tau := by
                convert childUL hs011131 hx011131 hy011131 using 1 <;> norm_num
              exact Batch0190.cell1522.sound htau (by
                simp only [Batch0190.cell1522, Batch0190.tau1522, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011131 | hy011131
            · have hs0111311 : InSquare (-1/320) (-119/320) (1/320) tau := by
                convert childLR hs011131 hx011131 hy011131 using 1 <;> norm_num
              exact Batch0190.cell1521.sound htau (by
                simp only [Batch0190.cell1521, Batch0190.tau1521, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111311 (by positivity) using 1 <;> norm_num)
            · have hs0111313 : InSquare (-1/320) (-117/320) (1/320) tau := by
                convert childUR hs011131 hx011131 hy011131 using 1 <;> norm_num
              exact Batch0190.cell1523.sound htau (by
                simp only [Batch0190.cell1523, Batch0190.tau1523, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111313 (by positivity) using 1 <;> norm_num)
        · have hs011133 : InSquare (-1/160) (-57/160) (1/160) tau := by
            convert childUR hs01113 hx01113 hy01113 using 1 <;> norm_num
          exact Batch0050.cell0403.sound htau (by
            simp only [Batch0050.cell0403, Batch0050.tau0403, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0111

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0112 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0112

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx0112 | hx0112
  · rcases le_total tau.im (-13/40 : ℝ) with hy0112 | hy0112
    · have hs01120 : InSquare (-7/80) (-27/80) (1/80) tau := by
        convert childLL hs hx0112 hy0112 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx01120 | hx01120
      · rcases le_total tau.im (-27/80 : ℝ) with hy01120 | hy01120
        · have hs011200 : InSquare (-3/32) (-11/32) (1/160) tau := by
            convert childLL hs01120 hx01120 hy01120 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx011200 | hx011200
          · rcases le_total tau.im (-11/32 : ℝ) with hy011200 | hy011200
            · have hs0112000 : InSquare (-31/320) (-111/320) (1/320) tau := by
                convert childLL hs011200 hx011200 hy011200 using 1 <;> norm_num
              exact Batch0191.cell1528.sound htau (by
                simp only [Batch0191.cell1528, Batch0191.tau1528, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112000 (by positivity) using 1 <;> norm_num)
            · have hs0112002 : InSquare (-31/320) (-109/320) (1/320) tau := by
                convert childUL hs011200 hx011200 hy011200 using 1 <;> norm_num
              exact Batch0191.cell1530.sound htau (by
                simp only [Batch0191.cell1530, Batch0191.tau1530, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy011200 | hy011200
            · have hs0112001 : InSquare (-29/320) (-111/320) (1/320) tau := by
                convert childLR hs011200 hx011200 hy011200 using 1 <;> norm_num
              exact Batch0191.cell1529.sound htau (by
                simp only [Batch0191.cell1529, Batch0191.tau1529, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112001 (by positivity) using 1 <;> norm_num)
            · have hs0112003 : InSquare (-29/320) (-109/320) (1/320) tau := by
                convert childUR hs011200 hx011200 hy011200 using 1 <;> norm_num
              exact Batch0191.cell1531.sound htau (by
                simp only [Batch0191.cell1531, Batch0191.tau1531, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112003 (by positivity) using 1 <;> norm_num)
        · have hs011202 : InSquare (-3/32) (-53/160) (1/160) tau := by
            convert childUL hs01120 hx01120 hy01120 using 1 <;> norm_num
          exact Batch0050.cell0404.sound htau (by
            simp only [Batch0050.cell0404, Batch0050.tau0404, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01120 | hy01120
        · have hs011201 : InSquare (-13/160) (-11/32) (1/160) tau := by
            convert childLR hs01120 hx01120 hy01120 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx011201 | hx011201
          · rcases le_total tau.im (-11/32 : ℝ) with hy011201 | hy011201
            · have hs0112010 : InSquare (-27/320) (-111/320) (1/320) tau := by
                convert childLL hs011201 hx011201 hy011201 using 1 <;> norm_num
              exact Batch0191.cell1532.sound htau (by
                simp only [Batch0191.cell1532, Batch0191.tau1532, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112010 (by positivity) using 1 <;> norm_num)
            · have hs0112012 : InSquare (-27/320) (-109/320) (1/320) tau := by
                convert childUL hs011201 hx011201 hy011201 using 1 <;> norm_num
              exact Batch0191.cell1534.sound htau (by
                simp only [Batch0191.cell1534, Batch0191.tau1534, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy011201 | hy011201
            · have hs0112011 : InSquare (-5/64) (-111/320) (1/320) tau := by
                convert childLR hs011201 hx011201 hy011201 using 1 <;> norm_num
              exact Batch0191.cell1533.sound htau (by
                simp only [Batch0191.cell1533, Batch0191.tau1533, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112011 (by positivity) using 1 <;> norm_num)
            · have hs0112013 : InSquare (-5/64) (-109/320) (1/320) tau := by
                convert childUR hs011201 hx011201 hy011201 using 1 <;> norm_num
              exact Batch0191.cell1535.sound htau (by
                simp only [Batch0191.cell1535, Batch0191.tau1535, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112013 (by positivity) using 1 <;> norm_num)
        · have hs011203 : InSquare (-13/160) (-53/160) (1/160) tau := by
            convert childUR hs01120 hx01120 hy01120 using 1 <;> norm_num
          exact Batch0050.cell0405.sound htau (by
            simp only [Batch0050.cell0405, Batch0050.tau0405, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011203 (by positivity) using 1 <;> norm_num)
    · have hs01122 : InSquare (-7/80) (-5/16) (1/80) tau := by
        convert childUL hs hx0112 hy0112 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx01122 | hx01122
      · rcases le_total tau.im (-5/16 : ℝ) with hy01122 | hy01122
        · have hs011220 : InSquare (-3/32) (-51/160) (1/160) tau := by
            convert childLL hs01122 hx01122 hy01122 using 1 <;> norm_num
          exact Batch0051.cell0409.sound htau (by
            simp only [Batch0051.cell0409, Batch0051.tau0409, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011220 (by positivity) using 1 <;> norm_num)
        · have hs011222 : InSquare (-3/32) (-49/160) (1/160) tau := by
            convert childUL hs01122 hx01122 hy01122 using 1 <;> norm_num
          exact Batch0051.cell0411.sound htau (by
            simp only [Batch0051.cell0411, Batch0051.tau0411, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01122 | hy01122
        · have hs011221 : InSquare (-13/160) (-51/160) (1/160) tau := by
            convert childLR hs01122 hx01122 hy01122 using 1 <;> norm_num
          exact Batch0051.cell0410.sound htau (by
            simp only [Batch0051.cell0410, Batch0051.tau0410, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011221 (by positivity) using 1 <;> norm_num)
        · have hs011223 : InSquare (-13/160) (-49/160) (1/160) tau := by
            convert childUR hs01122 hx01122 hy01122 using 1 <;> norm_num
          exact Batch0051.cell0412.sound htau (by
            simp only [Batch0051.cell0412, Batch0051.tau0412, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy0112 | hy0112
    · have hs01121 : InSquare (-1/16) (-27/80) (1/80) tau := by
        convert childLR hs hx0112 hy0112 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx01121 | hx01121
      · rcases le_total tau.im (-27/80 : ℝ) with hy01121 | hy01121
        · have hs011210 : InSquare (-11/160) (-11/32) (1/160) tau := by
            convert childLL hs01121 hx01121 hy01121 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx011210 | hx011210
          · rcases le_total tau.im (-11/32 : ℝ) with hy011210 | hy011210
            · have hs0112100 : InSquare (-23/320) (-111/320) (1/320) tau := by
                convert childLL hs011210 hx011210 hy011210 using 1 <;> norm_num
              exact Batch0192.cell1536.sound htau (by
                simp only [Batch0192.cell1536, Batch0192.tau1536, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112100 (by positivity) using 1 <;> norm_num)
            · have hs0112102 : InSquare (-23/320) (-109/320) (1/320) tau := by
                convert childUL hs011210 hx011210 hy011210 using 1 <;> norm_num
              exact Batch0192.cell1538.sound htau (by
                simp only [Batch0192.cell1538, Batch0192.tau1538, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy011210 | hy011210
            · have hs0112101 : InSquare (-21/320) (-111/320) (1/320) tau := by
                convert childLR hs011210 hx011210 hy011210 using 1 <;> norm_num
              exact Batch0192.cell1537.sound htau (by
                simp only [Batch0192.cell1537, Batch0192.tau1537, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112101 (by positivity) using 1 <;> norm_num)
            · have hs0112103 : InSquare (-21/320) (-109/320) (1/320) tau := by
                convert childUR hs011210 hx011210 hy011210 using 1 <;> norm_num
              exact Batch0192.cell1539.sound htau (by
                simp only [Batch0192.cell1539, Batch0192.tau1539, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112103 (by positivity) using 1 <;> norm_num)
        · have hs011212 : InSquare (-11/160) (-53/160) (1/160) tau := by
            convert childUL hs01121 hx01121 hy01121 using 1 <;> norm_num
          exact Batch0050.cell0407.sound htau (by
            simp only [Batch0050.cell0407, Batch0050.tau0407, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01121 | hy01121
        · have hs011211 : InSquare (-9/160) (-11/32) (1/160) tau := by
            convert childLR hs01121 hx01121 hy01121 using 1 <;> norm_num
          exact Batch0050.cell0406.sound htau (by
            simp only [Batch0050.cell0406, Batch0050.tau0406, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011211 (by positivity) using 1 <;> norm_num)
        · have hs011213 : InSquare (-9/160) (-53/160) (1/160) tau := by
            convert childUR hs01121 hx01121 hy01121 using 1 <;> norm_num
          exact Batch0051.cell0408.sound htau (by
            simp only [Batch0051.cell0408, Batch0051.tau0408, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011213 (by positivity) using 1 <;> norm_num)
    · have hs01123 : InSquare (-1/16) (-5/16) (1/80) tau := by
        convert childUR hs hx0112 hy0112 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx01123 | hx01123
      · rcases le_total tau.im (-5/16 : ℝ) with hy01123 | hy01123
        · have hs011230 : InSquare (-11/160) (-51/160) (1/160) tau := by
            convert childLL hs01123 hx01123 hy01123 using 1 <;> norm_num
          exact Batch0051.cell0413.sound htau (by
            simp only [Batch0051.cell0413, Batch0051.tau0413, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011230 (by positivity) using 1 <;> norm_num)
        · have hs011232 : InSquare (-11/160) (-49/160) (1/160) tau := by
            convert childUL hs01123 hx01123 hy01123 using 1 <;> norm_num
          exact Batch0051.cell0415.sound htau (by
            simp only [Batch0051.cell0415, Batch0051.tau0415, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01123 | hy01123
        · have hs011231 : InSquare (-9/160) (-51/160) (1/160) tau := by
            convert childLR hs01123 hx01123 hy01123 using 1 <;> norm_num
          exact Batch0051.cell0414.sound htau (by
            simp only [Batch0051.cell0414, Batch0051.tau0414, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011231 (by positivity) using 1 <;> norm_num)
        · have hs011233 : InSquare (-9/160) (-49/160) (1/160) tau := by
            convert childUR hs01123 hx01123 hy01123 using 1 <;> norm_num
          exact Batch0052.cell0416.sound htau (by
            simp only [Batch0052.cell0416, Batch0052.tau0416, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0112

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0113 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0113

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx0113 | hx0113
  · rcases le_total tau.im (-13/40 : ℝ) with hy0113 | hy0113
    · have hs01130 : InSquare (-3/80) (-27/80) (1/80) tau := by
        convert childLL hs hx0113 hy0113 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx01130 | hx01130
      · rcases le_total tau.im (-27/80 : ℝ) with hy01130 | hy01130
        · have hs011300 : InSquare (-7/160) (-11/32) (1/160) tau := by
            convert childLL hs01130 hx01130 hy01130 using 1 <;> norm_num
          exact Batch0052.cell0417.sound htau (by
            simp only [Batch0052.cell0417, Batch0052.tau0417, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011300 (by positivity) using 1 <;> norm_num)
        · have hs011302 : InSquare (-7/160) (-53/160) (1/160) tau := by
            convert childUL hs01130 hx01130 hy01130 using 1 <;> norm_num
          exact Batch0052.cell0419.sound htau (by
            simp only [Batch0052.cell0419, Batch0052.tau0419, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01130 | hy01130
        · have hs011301 : InSquare (-1/32) (-11/32) (1/160) tau := by
            convert childLR hs01130 hx01130 hy01130 using 1 <;> norm_num
          exact Batch0052.cell0418.sound htau (by
            simp only [Batch0052.cell0418, Batch0052.tau0418, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011301 (by positivity) using 1 <;> norm_num)
        · have hs011303 : InSquare (-1/32) (-53/160) (1/160) tau := by
            convert childUR hs01130 hx01130 hy01130 using 1 <;> norm_num
          exact Batch0052.cell0420.sound htau (by
            simp only [Batch0052.cell0420, Batch0052.tau0420, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011303 (by positivity) using 1 <;> norm_num)
    · have hs01132 : InSquare (-3/80) (-5/16) (1/80) tau := by
        convert childUL hs hx0113 hy0113 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx01132 | hx01132
      · rcases le_total tau.im (-5/16 : ℝ) with hy01132 | hy01132
        · have hs011320 : InSquare (-7/160) (-51/160) (1/160) tau := by
            convert childLL hs01132 hx01132 hy01132 using 1 <;> norm_num
          exact Batch0053.cell0425.sound htau (by
            simp only [Batch0053.cell0425, Batch0053.tau0425, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011320 (by positivity) using 1 <;> norm_num)
        · have hs011322 : InSquare (-7/160) (-49/160) (1/160) tau := by
            convert childUL hs01132 hx01132 hy01132 using 1 <;> norm_num
          exact Batch0053.cell0427.sound htau (by
            simp only [Batch0053.cell0427, Batch0053.tau0427, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01132 | hy01132
        · have hs011321 : InSquare (-1/32) (-51/160) (1/160) tau := by
            convert childLR hs01132 hx01132 hy01132 using 1 <;> norm_num
          exact Batch0053.cell0426.sound htau (by
            simp only [Batch0053.cell0426, Batch0053.tau0426, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011321 (by positivity) using 1 <;> norm_num)
        · have hs011323 : InSquare (-1/32) (-49/160) (1/160) tau := by
            convert childUR hs01132 hx01132 hy01132 using 1 <;> norm_num
          exact Batch0053.cell0428.sound htau (by
            simp only [Batch0053.cell0428, Batch0053.tau0428, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy0113 | hy0113
    · have hs01131 : InSquare (-1/80) (-27/80) (1/80) tau := by
        convert childLR hs hx0113 hy0113 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx01131 | hx01131
      · rcases le_total tau.im (-27/80 : ℝ) with hy01131 | hy01131
        · have hs011310 : InSquare (-3/160) (-11/32) (1/160) tau := by
            convert childLL hs01131 hx01131 hy01131 using 1 <;> norm_num
          exact Batch0052.cell0421.sound htau (by
            simp only [Batch0052.cell0421, Batch0052.tau0421, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011310 (by positivity) using 1 <;> norm_num)
        · have hs011312 : InSquare (-3/160) (-53/160) (1/160) tau := by
            convert childUL hs01131 hx01131 hy01131 using 1 <;> norm_num
          exact Batch0052.cell0423.sound htau (by
            simp only [Batch0052.cell0423, Batch0052.tau0423, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01131 | hy01131
        · have hs011311 : InSquare (-1/160) (-11/32) (1/160) tau := by
            convert childLR hs01131 hx01131 hy01131 using 1 <;> norm_num
          exact Batch0052.cell0422.sound htau (by
            simp only [Batch0052.cell0422, Batch0052.tau0422, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011311 (by positivity) using 1 <;> norm_num)
        · have hs011313 : InSquare (-1/160) (-53/160) (1/160) tau := by
            convert childUR hs01131 hx01131 hy01131 using 1 <;> norm_num
          exact Batch0053.cell0424.sound htau (by
            simp only [Batch0053.cell0424, Batch0053.tau0424, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011313 (by positivity) using 1 <;> norm_num)
    · have hs01133 : InSquare (-1/80) (-5/16) (1/80) tau := by
        convert childUR hs hx0113 hy0113 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx01133 | hx01133
      · rcases le_total tau.im (-5/16 : ℝ) with hy01133 | hy01133
        · have hs011330 : InSquare (-3/160) (-51/160) (1/160) tau := by
            convert childLL hs01133 hx01133 hy01133 using 1 <;> norm_num
          exact Batch0053.cell0429.sound htau (by
            simp only [Batch0053.cell0429, Batch0053.tau0429, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011330 (by positivity) using 1 <;> norm_num)
        · have hs011332 : InSquare (-3/160) (-49/160) (1/160) tau := by
            convert childUL hs01133 hx01133 hy01133 using 1 <;> norm_num
          exact Batch0053.cell0431.sound htau (by
            simp only [Batch0053.cell0431, Batch0053.tau0431, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01133 | hy01133
        · have hs011331 : InSquare (-1/160) (-51/160) (1/160) tau := by
            convert childLR hs01133 hx01133 hy01133 using 1 <;> norm_num
          exact Batch0053.cell0430.sound htau (by
            simp only [Batch0053.cell0430, Batch0053.tau0430, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011331 (by positivity) using 1 <;> norm_num)
        · have hs011333 : InSquare (-1/160) (-49/160) (1/160) tau := by
            convert childUR hs01133 hx01133 hy01133 using 1 <;> norm_num
          exact Batch0054.cell0432.sound htau (by
            simp only [Batch0054.cell0432, Batch0054.tau0432, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0113

end


