-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2210__5
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2210__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:10:28.954356+00:00
-- url     : https://prove2.me/theorems/8797ad49-9c1b-4b3f-854f-5ae5cba26b9a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2210 (+4 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2211, GeneralCK.Certific…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2210 (+4 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2211, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2212, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2213, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2230)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2210 (+4 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2211, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2212, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2213, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2230)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2210 (+4 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2211, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2212, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2213, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2230) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2210 (+4 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2211, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2212, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2213, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2230).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0106
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0107
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0108
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0238
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0239
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0109
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0110
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0240
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0241
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0242
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0243
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0244
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0111
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0112
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0245
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0246
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0247
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0248

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2210 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2210

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx2210 | hx2210
  · rcases le_total tau.im (9/40 : ℝ) with hy2210 | hy2210
    · have hs22100 : InSquare (-23/80) (17/80) (1/80) tau := by
        convert childLL hs hx2210 hy2210 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx22100 | hx22100
      · rcases le_total tau.im (17/80 : ℝ) with hy22100 | hy22100
        · have hs221000 : InSquare (-47/160) (33/160) (1/160) tau := by
            convert childLL hs22100 hx22100 hy22100 using 1 <;> norm_num
          exact Batch0106.cell0855.sound htau (by
            simp only [Batch0106.cell0855, Batch0106.tau0855, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221000 (by positivity) using 1 <;> norm_num)
        · have hs221002 : InSquare (-47/160) (7/32) (1/160) tau := by
            convert childUL hs22100 hx22100 hy22100 using 1 <;> norm_num
          exact Batch0107.cell0857.sound htau (by
            simp only [Batch0107.cell0857, Batch0107.tau0857, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy22100 | hy22100
        · have hs221001 : InSquare (-9/32) (33/160) (1/160) tau := by
            convert childLR hs22100 hx22100 hy22100 using 1 <;> norm_num
          exact Batch0107.cell0856.sound htau (by
            simp only [Batch0107.cell0856, Batch0107.tau0856, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221001 (by positivity) using 1 <;> norm_num)
        · have hs221003 : InSquare (-9/32) (7/32) (1/160) tau := by
            convert childUR hs22100 hx22100 hy22100 using 1 <;> norm_num
          exact Batch0107.cell0858.sound htau (by
            simp only [Batch0107.cell0858, Batch0107.tau0858, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221003 (by positivity) using 1 <;> norm_num)
    · have hs22102 : InSquare (-23/80) (19/80) (1/80) tau := by
        convert childUL hs hx2210 hy2210 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx22102 | hx22102
      · rcases le_total tau.im (19/80 : ℝ) with hy22102 | hy22102
        · have hs221020 : InSquare (-47/160) (37/160) (1/160) tau := by
            convert childLL hs22102 hx22102 hy22102 using 1 <;> norm_num
          exact Batch0107.cell0863.sound htau (by
            simp only [Batch0107.cell0863, Batch0107.tau0863, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221020 (by positivity) using 1 <;> norm_num)
        · have hs221022 : InSquare (-47/160) (39/160) (1/160) tau := by
            convert childUL hs22102 hx22102 hy22102 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx221022 | hx221022
          · rcases le_total tau.im (39/160 : ℝ) with hy221022 | hy221022
            · have hs2210220 : InSquare (-19/64) (77/320) (1/320) tau := by
                convert childLL hs221022 hx221022 hy221022 using 1 <;> norm_num
              exact Batch0238.cell1909.sound htau (by
                simp only [Batch0238.cell1909, Batch0238.tau1909, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2210220 (by positivity) using 1 <;> norm_num)
            · have hs2210222 : InSquare (-19/64) (79/320) (1/320) tau := by
                convert childUL hs221022 hx221022 hy221022 using 1 <;> norm_num
              exact Batch0238.cell1911.sound htau (by
                simp only [Batch0238.cell1911, Batch0238.tau1911, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2210222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (39/160 : ℝ) with hy221022 | hy221022
            · have hs2210221 : InSquare (-93/320) (77/320) (1/320) tau := by
                convert childLR hs221022 hx221022 hy221022 using 1 <;> norm_num
              exact Batch0238.cell1910.sound htau (by
                simp only [Batch0238.cell1910, Batch0238.tau1910, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2210221 (by positivity) using 1 <;> norm_num)
            · have hs2210223 : InSquare (-93/320) (79/320) (1/320) tau := by
                convert childUR hs221022 hx221022 hy221022 using 1 <;> norm_num
              exact Batch0239.cell1912.sound htau (by
                simp only [Batch0239.cell1912, Batch0239.tau1912, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2210223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy22102 | hy22102
        · have hs221021 : InSquare (-9/32) (37/160) (1/160) tau := by
            convert childLR hs22102 hx22102 hy22102 using 1 <;> norm_num
          exact Batch0108.cell0864.sound htau (by
            simp only [Batch0108.cell0864, Batch0108.tau0864, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221021 (by positivity) using 1 <;> norm_num)
        · have hs221023 : InSquare (-9/32) (39/160) (1/160) tau := by
            convert childUR hs22102 hx22102 hy22102 using 1 <;> norm_num
          exact Batch0108.cell0865.sound htau (by
            simp only [Batch0108.cell0865, Batch0108.tau0865, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy2210 | hy2210
    · have hs22101 : InSquare (-21/80) (17/80) (1/80) tau := by
        convert childLR hs hx2210 hy2210 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx22101 | hx22101
      · rcases le_total tau.im (17/80 : ℝ) with hy22101 | hy22101
        · have hs221010 : InSquare (-43/160) (33/160) (1/160) tau := by
            convert childLL hs22101 hx22101 hy22101 using 1 <;> norm_num
          exact Batch0107.cell0859.sound htau (by
            simp only [Batch0107.cell0859, Batch0107.tau0859, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221010 (by positivity) using 1 <;> norm_num)
        · have hs221012 : InSquare (-43/160) (7/32) (1/160) tau := by
            convert childUL hs22101 hx22101 hy22101 using 1 <;> norm_num
          exact Batch0107.cell0861.sound htau (by
            simp only [Batch0107.cell0861, Batch0107.tau0861, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy22101 | hy22101
        · have hs221011 : InSquare (-41/160) (33/160) (1/160) tau := by
            convert childLR hs22101 hx22101 hy22101 using 1 <;> norm_num
          exact Batch0107.cell0860.sound htau (by
            simp only [Batch0107.cell0860, Batch0107.tau0860, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221011 (by positivity) using 1 <;> norm_num)
        · have hs221013 : InSquare (-41/160) (7/32) (1/160) tau := by
            convert childUR hs22101 hx22101 hy22101 using 1 <;> norm_num
          exact Batch0107.cell0862.sound htau (by
            simp only [Batch0107.cell0862, Batch0107.tau0862, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221013 (by positivity) using 1 <;> norm_num)
    · have hs22103 : InSquare (-21/80) (19/80) (1/80) tau := by
        convert childUR hs hx2210 hy2210 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx22103 | hx22103
      · rcases le_total tau.im (19/80 : ℝ) with hy22103 | hy22103
        · have hs221030 : InSquare (-43/160) (37/160) (1/160) tau := by
            convert childLL hs22103 hx22103 hy22103 using 1 <;> norm_num
          exact Batch0108.cell0866.sound htau (by
            simp only [Batch0108.cell0866, Batch0108.tau0866, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221030 (by positivity) using 1 <;> norm_num)
        · have hs221032 : InSquare (-43/160) (39/160) (1/160) tau := by
            convert childUL hs22103 hx22103 hy22103 using 1 <;> norm_num
          exact Batch0108.cell0868.sound htau (by
            simp only [Batch0108.cell0868, Batch0108.tau0868, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy22103 | hy22103
        · have hs221031 : InSquare (-41/160) (37/160) (1/160) tau := by
            convert childLR hs22103 hx22103 hy22103 using 1 <;> norm_num
          exact Batch0108.cell0867.sound htau (by
            simp only [Batch0108.cell0867, Batch0108.tau0867, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221031 (by positivity) using 1 <;> norm_num)
        · have hs221033 : InSquare (-41/160) (39/160) (1/160) tau := by
            convert childUR hs22103 hx22103 hy22103 using 1 <;> norm_num
          exact Batch0108.cell0869.sound htau (by
            simp only [Batch0108.cell0869, Batch0108.tau0869, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2210

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2211 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2211

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx2211 | hx2211
  · rcases le_total tau.im (9/40 : ℝ) with hy2211 | hy2211
    · have hs22110 : InSquare (-19/80) (17/80) (1/80) tau := by
        convert childLL hs hx2211 hy2211 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx22110 | hx22110
      · rcases le_total tau.im (17/80 : ℝ) with hy22110 | hy22110
        · have hs221100 : InSquare (-39/160) (33/160) (1/160) tau := by
            convert childLL hs22110 hx22110 hy22110 using 1 <;> norm_num
          exact Batch0108.cell0870.sound htau (by
            simp only [Batch0108.cell0870, Batch0108.tau0870, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221100 (by positivity) using 1 <;> norm_num)
        · have hs221102 : InSquare (-39/160) (7/32) (1/160) tau := by
            convert childUL hs22110 hx22110 hy22110 using 1 <;> norm_num
          exact Batch0109.cell0872.sound htau (by
            simp only [Batch0109.cell0872, Batch0109.tau0872, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy22110 | hy22110
        · have hs221101 : InSquare (-37/160) (33/160) (1/160) tau := by
            convert childLR hs22110 hx22110 hy22110 using 1 <;> norm_num
          exact Batch0108.cell0871.sound htau (by
            simp only [Batch0108.cell0871, Batch0108.tau0871, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221101 (by positivity) using 1 <;> norm_num)
        · have hs221103 : InSquare (-37/160) (7/32) (1/160) tau := by
            convert childUR hs22110 hx22110 hy22110 using 1 <;> norm_num
          exact Batch0109.cell0873.sound htau (by
            simp only [Batch0109.cell0873, Batch0109.tau0873, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221103 (by positivity) using 1 <;> norm_num)
    · have hs22112 : InSquare (-19/80) (19/80) (1/80) tau := by
        convert childUL hs hx2211 hy2211 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx22112 | hx22112
      · rcases le_total tau.im (19/80 : ℝ) with hy22112 | hy22112
        · have hs221120 : InSquare (-39/160) (37/160) (1/160) tau := by
            convert childLL hs22112 hx22112 hy22112 using 1 <;> norm_num
          exact Batch0109.cell0878.sound htau (by
            simp only [Batch0109.cell0878, Batch0109.tau0878, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221120 (by positivity) using 1 <;> norm_num)
        · have hs221122 : InSquare (-39/160) (39/160) (1/160) tau := by
            convert childUL hs22112 hx22112 hy22112 using 1 <;> norm_num
          exact Batch0110.cell0880.sound htau (by
            simp only [Batch0110.cell0880, Batch0110.tau0880, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy22112 | hy22112
        · have hs221121 : InSquare (-37/160) (37/160) (1/160) tau := by
            convert childLR hs22112 hx22112 hy22112 using 1 <;> norm_num
          exact Batch0109.cell0879.sound htau (by
            simp only [Batch0109.cell0879, Batch0109.tau0879, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221121 (by positivity) using 1 <;> norm_num)
        · have hs221123 : InSquare (-37/160) (39/160) (1/160) tau := by
            convert childUR hs22112 hx22112 hy22112 using 1 <;> norm_num
          exact Batch0110.cell0881.sound htau (by
            simp only [Batch0110.cell0881, Batch0110.tau0881, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy2211 | hy2211
    · have hs22111 : InSquare (-17/80) (17/80) (1/80) tau := by
        convert childLR hs hx2211 hy2211 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx22111 | hx22111
      · rcases le_total tau.im (17/80 : ℝ) with hy22111 | hy22111
        · have hs221110 : InSquare (-7/32) (33/160) (1/160) tau := by
            convert childLL hs22111 hx22111 hy22111 using 1 <;> norm_num
          exact Batch0109.cell0874.sound htau (by
            simp only [Batch0109.cell0874, Batch0109.tau0874, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221110 (by positivity) using 1 <;> norm_num)
        · have hs221112 : InSquare (-7/32) (7/32) (1/160) tau := by
            convert childUL hs22111 hx22111 hy22111 using 1 <;> norm_num
          exact Batch0109.cell0876.sound htau (by
            simp only [Batch0109.cell0876, Batch0109.tau0876, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy22111 | hy22111
        · have hs221111 : InSquare (-33/160) (33/160) (1/160) tau := by
            convert childLR hs22111 hx22111 hy22111 using 1 <;> norm_num
          exact Batch0109.cell0875.sound htau (by
            simp only [Batch0109.cell0875, Batch0109.tau0875, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221111 (by positivity) using 1 <;> norm_num)
        · have hs221113 : InSquare (-33/160) (7/32) (1/160) tau := by
            convert childUR hs22111 hx22111 hy22111 using 1 <;> norm_num
          exact Batch0109.cell0877.sound htau (by
            simp only [Batch0109.cell0877, Batch0109.tau0877, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221113 (by positivity) using 1 <;> norm_num)
    · have hs22113 : InSquare (-17/80) (19/80) (1/80) tau := by
        convert childUR hs hx2211 hy2211 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx22113 | hx22113
      · rcases le_total tau.im (19/80 : ℝ) with hy22113 | hy22113
        · have hs221130 : InSquare (-7/32) (37/160) (1/160) tau := by
            convert childLL hs22113 hx22113 hy22113 using 1 <;> norm_num
          exact Batch0110.cell0882.sound htau (by
            simp only [Batch0110.cell0882, Batch0110.tau0882, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221130 (by positivity) using 1 <;> norm_num)
        · have hs221132 : InSquare (-7/32) (39/160) (1/160) tau := by
            convert childUL hs22113 hx22113 hy22113 using 1 <;> norm_num
          exact Batch0110.cell0884.sound htau (by
            simp only [Batch0110.cell0884, Batch0110.tau0884, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy22113 | hy22113
        · have hs221131 : InSquare (-33/160) (37/160) (1/160) tau := by
            convert childLR hs22113 hx22113 hy22113 using 1 <;> norm_num
          exact Batch0110.cell0883.sound htau (by
            simp only [Batch0110.cell0883, Batch0110.tau0883, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221131 (by positivity) using 1 <;> norm_num)
        · have hs221133 : InSquare (-33/160) (39/160) (1/160) tau := by
            convert childUR hs22113 hx22113 hy22113 using 1 <;> norm_num
          exact Batch0110.cell0885.sound htau (by
            simp only [Batch0110.cell0885, Batch0110.tau0885, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2211

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2212 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2212

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_221222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/160) (47/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/80)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2212200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-19/64) (89/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+47/160)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2212202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-19/64) (91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+47/160)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2212203 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-93/320) (91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/80)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2212230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/320) (93/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/32)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2212232 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/320) (19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/32)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2212233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-89/320) (19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/40)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx2212 | hx2212
  · rcases le_total tau.im (11/40 : ℝ) with hy2212 | hy2212
    · have hs22120 : InSquare (-23/80) (21/80) (1/80) tau := by
        convert childLL hs hx2212 hy2212 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx22120 | hx22120
      · rcases le_total tau.im (21/80 : ℝ) with hy22120 | hy22120
        · have hs221200 : InSquare (-47/160) (41/160) (1/160) tau := by
            convert childLL hs22120 hx22120 hy22120 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx221200 | hx221200
          · rcases le_total tau.im (41/160 : ℝ) with hy221200 | hy221200
            · have hs2212000 : InSquare (-19/64) (81/320) (1/320) tau := by
                convert childLL hs221200 hx221200 hy221200 using 1 <;> norm_num
              exact Batch0239.cell1913.sound htau (by
                simp only [Batch0239.cell1913, Batch0239.tau1913, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212000 (by positivity) using 1 <;> norm_num)
            · have hs2212002 : InSquare (-19/64) (83/320) (1/320) tau := by
                convert childUL hs221200 hx221200 hy221200 using 1 <;> norm_num
              exact Batch0239.cell1915.sound htau (by
                simp only [Batch0239.cell1915, Batch0239.tau1915, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (41/160 : ℝ) with hy221200 | hy221200
            · have hs2212001 : InSquare (-93/320) (81/320) (1/320) tau := by
                convert childLR hs221200 hx221200 hy221200 using 1 <;> norm_num
              exact Batch0239.cell1914.sound htau (by
                simp only [Batch0239.cell1914, Batch0239.tau1914, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212001 (by positivity) using 1 <;> norm_num)
            · have hs2212003 : InSquare (-93/320) (83/320) (1/320) tau := by
                convert childUR hs221200 hx221200 hy221200 using 1 <;> norm_num
              exact Batch0239.cell1916.sound htau (by
                simp only [Batch0239.cell1916, Batch0239.tau1916, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212003 (by positivity) using 1 <;> norm_num)
        · have hs221202 : InSquare (-47/160) (43/160) (1/160) tau := by
            convert childUL hs22120 hx22120 hy22120 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx221202 | hx221202
          · rcases le_total tau.im (43/160 : ℝ) with hy221202 | hy221202
            · have hs2212020 : InSquare (-19/64) (17/64) (1/320) tau := by
                convert childLL hs221202 hx221202 hy221202 using 1 <;> norm_num
              exact Batch0240.cell1921.sound htau (by
                simp only [Batch0240.cell1921, Batch0240.tau1921, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212020 (by positivity) using 1 <;> norm_num)
            · have hs2212022 : InSquare (-19/64) (87/320) (1/320) tau := by
                convert childUL hs221202 hx221202 hy221202 using 1 <;> norm_num
              exact Batch0240.cell1923.sound htau (by
                simp only [Batch0240.cell1923, Batch0240.tau1923, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy221202 | hy221202
            · have hs2212021 : InSquare (-93/320) (17/64) (1/320) tau := by
                convert childLR hs221202 hx221202 hy221202 using 1 <;> norm_num
              exact Batch0240.cell1922.sound htau (by
                simp only [Batch0240.cell1922, Batch0240.tau1922, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212021 (by positivity) using 1 <;> norm_num)
            · have hs2212023 : InSquare (-93/320) (87/320) (1/320) tau := by
                convert childUR hs221202 hx221202 hy221202 using 1 <;> norm_num
              exact Batch0240.cell1924.sound htau (by
                simp only [Batch0240.cell1924, Batch0240.tau1924, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy22120 | hy22120
        · have hs221201 : InSquare (-9/32) (41/160) (1/160) tau := by
            convert childLR hs22120 hx22120 hy22120 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx221201 | hx221201
          · rcases le_total tau.im (41/160 : ℝ) with hy221201 | hy221201
            · have hs2212010 : InSquare (-91/320) (81/320) (1/320) tau := by
                convert childLL hs221201 hx221201 hy221201 using 1 <;> norm_num
              exact Batch0239.cell1917.sound htau (by
                simp only [Batch0239.cell1917, Batch0239.tau1917, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212010 (by positivity) using 1 <;> norm_num)
            · have hs2212012 : InSquare (-91/320) (83/320) (1/320) tau := by
                convert childUL hs221201 hx221201 hy221201 using 1 <;> norm_num
              exact Batch0239.cell1919.sound htau (by
                simp only [Batch0239.cell1919, Batch0239.tau1919, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (41/160 : ℝ) with hy221201 | hy221201
            · have hs2212011 : InSquare (-89/320) (81/320) (1/320) tau := by
                convert childLR hs221201 hx221201 hy221201 using 1 <;> norm_num
              exact Batch0239.cell1918.sound htau (by
                simp only [Batch0239.cell1918, Batch0239.tau1918, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212011 (by positivity) using 1 <;> norm_num)
            · have hs2212013 : InSquare (-89/320) (83/320) (1/320) tau := by
                convert childUR hs221201 hx221201 hy221201 using 1 <;> norm_num
              exact Batch0240.cell1920.sound htau (by
                simp only [Batch0240.cell1920, Batch0240.tau1920, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212013 (by positivity) using 1 <;> norm_num)
        · have hs221203 : InSquare (-9/32) (43/160) (1/160) tau := by
            convert childUR hs22120 hx22120 hy22120 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx221203 | hx221203
          · rcases le_total tau.im (43/160 : ℝ) with hy221203 | hy221203
            · have hs2212030 : InSquare (-91/320) (17/64) (1/320) tau := by
                convert childLL hs221203 hx221203 hy221203 using 1 <;> norm_num
              exact Batch0240.cell1925.sound htau (by
                simp only [Batch0240.cell1925, Batch0240.tau1925, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212030 (by positivity) using 1 <;> norm_num)
            · have hs2212032 : InSquare (-91/320) (87/320) (1/320) tau := by
                convert childUL hs221203 hx221203 hy221203 using 1 <;> norm_num
              exact Batch0240.cell1927.sound htau (by
                simp only [Batch0240.cell1927, Batch0240.tau1927, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy221203 | hy221203
            · have hs2212031 : InSquare (-89/320) (17/64) (1/320) tau := by
                convert childLR hs221203 hx221203 hy221203 using 1 <;> norm_num
              exact Batch0240.cell1926.sound htau (by
                simp only [Batch0240.cell1926, Batch0240.tau1926, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212031 (by positivity) using 1 <;> norm_num)
            · have hs2212033 : InSquare (-89/320) (87/320) (1/320) tau := by
                convert childUR hs221203 hx221203 hy221203 using 1 <;> norm_num
              exact Batch0241.cell1928.sound htau (by
                simp only [Batch0241.cell1928, Batch0241.tau1928, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212033 (by positivity) using 1 <;> norm_num)
    · have hs22122 : InSquare (-23/80) (23/80) (1/80) tau := by
        convert childUL hs hx2212 hy2212 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx22122 | hx22122
      · rcases le_total tau.im (23/80 : ℝ) with hy22122 | hy22122
        · have hs221220 : InSquare (-47/160) (9/32) (1/160) tau := by
            convert childLL hs22122 hx22122 hy22122 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx221220 | hx221220
          · rcases le_total tau.im (9/32 : ℝ) with hy221220 | hy221220
            · have hs2212200 : InSquare (-19/64) (89/320) (1/320) tau := by
                convert childLL hs221220 hx221220 hy221220 using 1 <;> norm_num
              exact (outside_2212200 htau hs2212200).elim
            · have hs2212202 : InSquare (-19/64) (91/320) (1/320) tau := by
                convert childUL hs221220 hx221220 hy221220 using 1 <;> norm_num
              exact (outside_2212202 htau hs2212202).elim
          · rcases le_total tau.im (9/32 : ℝ) with hy221220 | hy221220
            · have hs2212201 : InSquare (-93/320) (89/320) (1/320) tau := by
                convert childLR hs221220 hx221220 hy221220 using 1 <;> norm_num
              exact Batch0242.cell1937.sound htau (by
                simp only [Batch0242.cell1937, Batch0242.tau1937, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212201 (by positivity) using 1 <;> norm_num)
            · have hs2212203 : InSquare (-93/320) (91/320) (1/320) tau := by
                convert childUR hs221220 hx221220 hy221220 using 1 <;> norm_num
              exact (outside_2212203 htau hs2212203).elim
        · have hs221222 : InSquare (-47/160) (47/160) (1/160) tau := by
            convert childUL hs22122 hx22122 hy22122 using 1 <;> norm_num
          exact (outside_221222 htau hs221222).elim
      · rcases le_total tau.im (23/80 : ℝ) with hy22122 | hy22122
        · have hs221221 : InSquare (-9/32) (9/32) (1/160) tau := by
            convert childLR hs22122 hx22122 hy22122 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx221221 | hx221221
          · rcases le_total tau.im (9/32 : ℝ) with hy221221 | hy221221
            · have hs2212210 : InSquare (-91/320) (89/320) (1/320) tau := by
                convert childLL hs221221 hx221221 hy221221 using 1 <;> norm_num
              exact Batch0242.cell1938.sound htau (by
                simp only [Batch0242.cell1938, Batch0242.tau1938, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212210 (by positivity) using 1 <;> norm_num)
            · have hs2212212 : InSquare (-91/320) (91/320) (1/320) tau := by
                convert childUL hs221221 hx221221 hy221221 using 1 <;> norm_num
              exact Batch0242.cell1940.sound htau (by
                simp only [Batch0242.cell1940, Batch0242.tau1940, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy221221 | hy221221
            · have hs2212211 : InSquare (-89/320) (89/320) (1/320) tau := by
                convert childLR hs221221 hx221221 hy221221 using 1 <;> norm_num
              exact Batch0242.cell1939.sound htau (by
                simp only [Batch0242.cell1939, Batch0242.tau1939, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212211 (by positivity) using 1 <;> norm_num)
            · have hs2212213 : InSquare (-89/320) (91/320) (1/320) tau := by
                convert childUR hs221221 hx221221 hy221221 using 1 <;> norm_num
              exact Batch0242.cell1941.sound htau (by
                simp only [Batch0242.cell1941, Batch0242.tau1941, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212213 (by positivity) using 1 <;> norm_num)
        · have hs221223 : InSquare (-9/32) (47/160) (1/160) tau := by
            convert childUR hs22122 hx22122 hy22122 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx221223 | hx221223
          · rcases le_total tau.im (47/160 : ℝ) with hy221223 | hy221223
            · have hs2212230 : InSquare (-91/320) (93/320) (1/320) tau := by
                convert childLL hs221223 hx221223 hy221223 using 1 <;> norm_num
              exact (outside_2212230 htau hs2212230).elim
            · have hs2212232 : InSquare (-91/320) (19/64) (1/320) tau := by
                convert childUL hs221223 hx221223 hy221223 using 1 <;> norm_num
              exact (outside_2212232 htau hs2212232).elim
          · rcases le_total tau.im (47/160 : ℝ) with hy221223 | hy221223
            · have hs2212231 : InSquare (-89/320) (93/320) (1/320) tau := by
                convert childLR hs221223 hx221223 hy221223 using 1 <;> norm_num
              exact Batch0242.cell1942.sound htau (by
                simp only [Batch0242.cell1942, Batch0242.tau1942, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212231 (by positivity) using 1 <;> norm_num)
            · have hs2212233 : InSquare (-89/320) (19/64) (1/320) tau := by
                convert childUR hs221223 hx221223 hy221223 using 1 <;> norm_num
              exact (outside_2212233 htau hs2212233).elim
  · rcases le_total tau.im (11/40 : ℝ) with hy2212 | hy2212
    · have hs22121 : InSquare (-21/80) (21/80) (1/80) tau := by
        convert childLR hs hx2212 hy2212 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx22121 | hx22121
      · rcases le_total tau.im (21/80 : ℝ) with hy22121 | hy22121
        · have hs221210 : InSquare (-43/160) (41/160) (1/160) tau := by
            convert childLL hs22121 hx22121 hy22121 using 1 <;> norm_num
          exact Batch0110.cell0886.sound htau (by
            simp only [Batch0110.cell0886, Batch0110.tau0886, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221210 (by positivity) using 1 <;> norm_num)
        · have hs221212 : InSquare (-43/160) (43/160) (1/160) tau := by
            convert childUL hs22121 hx22121 hy22121 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx221212 | hx221212
          · rcases le_total tau.im (43/160 : ℝ) with hy221212 | hy221212
            · have hs2212120 : InSquare (-87/320) (17/64) (1/320) tau := by
                convert childLL hs221212 hx221212 hy221212 using 1 <;> norm_num
              exact Batch0241.cell1929.sound htau (by
                simp only [Batch0241.cell1929, Batch0241.tau1929, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212120 (by positivity) using 1 <;> norm_num)
            · have hs2212122 : InSquare (-87/320) (87/320) (1/320) tau := by
                convert childUL hs221212 hx221212 hy221212 using 1 <;> norm_num
              exact Batch0241.cell1931.sound htau (by
                simp only [Batch0241.cell1931, Batch0241.tau1931, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy221212 | hy221212
            · have hs2212121 : InSquare (-17/64) (17/64) (1/320) tau := by
                convert childLR hs221212 hx221212 hy221212 using 1 <;> norm_num
              exact Batch0241.cell1930.sound htau (by
                simp only [Batch0241.cell1930, Batch0241.tau1930, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212121 (by positivity) using 1 <;> norm_num)
            · have hs2212123 : InSquare (-17/64) (87/320) (1/320) tau := by
                convert childUR hs221212 hx221212 hy221212 using 1 <;> norm_num
              exact Batch0241.cell1932.sound htau (by
                simp only [Batch0241.cell1932, Batch0241.tau1932, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy22121 | hy22121
        · have hs221211 : InSquare (-41/160) (41/160) (1/160) tau := by
            convert childLR hs22121 hx22121 hy22121 using 1 <;> norm_num
          exact Batch0110.cell0887.sound htau (by
            simp only [Batch0110.cell0887, Batch0110.tau0887, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221211 (by positivity) using 1 <;> norm_num)
        · have hs221213 : InSquare (-41/160) (43/160) (1/160) tau := by
            convert childUR hs22121 hx22121 hy22121 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx221213 | hx221213
          · rcases le_total tau.im (43/160 : ℝ) with hy221213 | hy221213
            · have hs2212130 : InSquare (-83/320) (17/64) (1/320) tau := by
                convert childLL hs221213 hx221213 hy221213 using 1 <;> norm_num
              exact Batch0241.cell1933.sound htau (by
                simp only [Batch0241.cell1933, Batch0241.tau1933, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212130 (by positivity) using 1 <;> norm_num)
            · have hs2212132 : InSquare (-83/320) (87/320) (1/320) tau := by
                convert childUL hs221213 hx221213 hy221213 using 1 <;> norm_num
              exact Batch0241.cell1935.sound htau (by
                simp only [Batch0241.cell1935, Batch0241.tau1935, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy221213 | hy221213
            · have hs2212131 : InSquare (-81/320) (17/64) (1/320) tau := by
                convert childLR hs221213 hx221213 hy221213 using 1 <;> norm_num
              exact Batch0241.cell1934.sound htau (by
                simp only [Batch0241.cell1934, Batch0241.tau1934, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212131 (by positivity) using 1 <;> norm_num)
            · have hs2212133 : InSquare (-81/320) (87/320) (1/320) tau := by
                convert childUR hs221213 hx221213 hy221213 using 1 <;> norm_num
              exact Batch0242.cell1936.sound htau (by
                simp only [Batch0242.cell1936, Batch0242.tau1936, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212133 (by positivity) using 1 <;> norm_num)
    · have hs22123 : InSquare (-21/80) (23/80) (1/80) tau := by
        convert childUR hs hx2212 hy2212 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx22123 | hx22123
      · rcases le_total tau.im (23/80 : ℝ) with hy22123 | hy22123
        · have hs221230 : InSquare (-43/160) (9/32) (1/160) tau := by
            convert childLL hs22123 hx22123 hy22123 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx221230 | hx221230
          · rcases le_total tau.im (9/32 : ℝ) with hy221230 | hy221230
            · have hs2212300 : InSquare (-87/320) (89/320) (1/320) tau := by
                convert childLL hs221230 hx221230 hy221230 using 1 <;> norm_num
              exact Batch0242.cell1943.sound htau (by
                simp only [Batch0242.cell1943, Batch0242.tau1943, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212300 (by positivity) using 1 <;> norm_num)
            · have hs2212302 : InSquare (-87/320) (91/320) (1/320) tau := by
                convert childUL hs221230 hx221230 hy221230 using 1 <;> norm_num
              exact Batch0243.cell1945.sound htau (by
                simp only [Batch0243.cell1945, Batch0243.tau1945, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy221230 | hy221230
            · have hs2212301 : InSquare (-17/64) (89/320) (1/320) tau := by
                convert childLR hs221230 hx221230 hy221230 using 1 <;> norm_num
              exact Batch0243.cell1944.sound htau (by
                simp only [Batch0243.cell1944, Batch0243.tau1944, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212301 (by positivity) using 1 <;> norm_num)
            · have hs2212303 : InSquare (-17/64) (91/320) (1/320) tau := by
                convert childUR hs221230 hx221230 hy221230 using 1 <;> norm_num
              exact Batch0243.cell1946.sound htau (by
                simp only [Batch0243.cell1946, Batch0243.tau1946, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212303 (by positivity) using 1 <;> norm_num)
        · have hs221232 : InSquare (-43/160) (47/160) (1/160) tau := by
            convert childUL hs22123 hx22123 hy22123 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx221232 | hx221232
          · rcases le_total tau.im (47/160 : ℝ) with hy221232 | hy221232
            · have hs2212320 : InSquare (-87/320) (93/320) (1/320) tau := by
                convert childLL hs221232 hx221232 hy221232 using 1 <;> norm_num
              exact Batch0243.cell1951.sound htau (by
                simp only [Batch0243.cell1951, Batch0243.tau1951, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212320 (by positivity) using 1 <;> norm_num)
            · have hs2212322 : InSquare (-87/320) (19/64) (1/320) tau := by
                convert childUL hs221232 hx221232 hy221232 using 1 <;> norm_num
              exact Batch0244.cell1953.sound htau (by
                simp only [Batch0244.cell1953, Batch0244.tau1953, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy221232 | hy221232
            · have hs2212321 : InSquare (-17/64) (93/320) (1/320) tau := by
                convert childLR hs221232 hx221232 hy221232 using 1 <;> norm_num
              exact Batch0244.cell1952.sound htau (by
                simp only [Batch0244.cell1952, Batch0244.tau1952, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212321 (by positivity) using 1 <;> norm_num)
            · have hs2212323 : InSquare (-17/64) (19/64) (1/320) tau := by
                convert childUR hs221232 hx221232 hy221232 using 1 <;> norm_num
              exact Batch0244.cell1954.sound htau (by
                simp only [Batch0244.cell1954, Batch0244.tau1954, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy22123 | hy22123
        · have hs221231 : InSquare (-41/160) (9/32) (1/160) tau := by
            convert childLR hs22123 hx22123 hy22123 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx221231 | hx221231
          · rcases le_total tau.im (9/32 : ℝ) with hy221231 | hy221231
            · have hs2212310 : InSquare (-83/320) (89/320) (1/320) tau := by
                convert childLL hs221231 hx221231 hy221231 using 1 <;> norm_num
              exact Batch0243.cell1947.sound htau (by
                simp only [Batch0243.cell1947, Batch0243.tau1947, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212310 (by positivity) using 1 <;> norm_num)
            · have hs2212312 : InSquare (-83/320) (91/320) (1/320) tau := by
                convert childUL hs221231 hx221231 hy221231 using 1 <;> norm_num
              exact Batch0243.cell1949.sound htau (by
                simp only [Batch0243.cell1949, Batch0243.tau1949, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy221231 | hy221231
            · have hs2212311 : InSquare (-81/320) (89/320) (1/320) tau := by
                convert childLR hs221231 hx221231 hy221231 using 1 <;> norm_num
              exact Batch0243.cell1948.sound htau (by
                simp only [Batch0243.cell1948, Batch0243.tau1948, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212311 (by positivity) using 1 <;> norm_num)
            · have hs2212313 : InSquare (-81/320) (91/320) (1/320) tau := by
                convert childUR hs221231 hx221231 hy221231 using 1 <;> norm_num
              exact Batch0243.cell1950.sound htau (by
                simp only [Batch0243.cell1950, Batch0243.tau1950, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212313 (by positivity) using 1 <;> norm_num)
        · have hs221233 : InSquare (-41/160) (47/160) (1/160) tau := by
            convert childUR hs22123 hx22123 hy22123 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx221233 | hx221233
          · rcases le_total tau.im (47/160 : ℝ) with hy221233 | hy221233
            · have hs2212330 : InSquare (-83/320) (93/320) (1/320) tau := by
                convert childLL hs221233 hx221233 hy221233 using 1 <;> norm_num
              exact Batch0244.cell1955.sound htau (by
                simp only [Batch0244.cell1955, Batch0244.tau1955, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212330 (by positivity) using 1 <;> norm_num)
            · have hs2212332 : InSquare (-83/320) (19/64) (1/320) tau := by
                convert childUL hs221233 hx221233 hy221233 using 1 <;> norm_num
              exact Batch0244.cell1957.sound htau (by
                simp only [Batch0244.cell1957, Batch0244.tau1957, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy221233 | hy221233
            · have hs2212331 : InSquare (-81/320) (93/320) (1/320) tau := by
                convert childLR hs221233 hx221233 hy221233 using 1 <;> norm_num
              exact Batch0244.cell1956.sound htau (by
                simp only [Batch0244.cell1956, Batch0244.tau1956, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212331 (by positivity) using 1 <;> norm_num)
            · have hs2212333 : InSquare (-81/320) (19/64) (1/320) tau := by
                convert childUR hs221233 hx221233 hy221233 using 1 <;> norm_num
              exact Batch0244.cell1958.sound htau (by
                simp only [Batch0244.cell1958, Batch0244.tau1958, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2212

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2213 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2213

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx2213 | hx2213
  · rcases le_total tau.im (11/40 : ℝ) with hy2213 | hy2213
    · have hs22130 : InSquare (-19/80) (21/80) (1/80) tau := by
        convert childLL hs hx2213 hy2213 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx22130 | hx22130
      · rcases le_total tau.im (21/80 : ℝ) with hy22130 | hy22130
        · have hs221300 : InSquare (-39/160) (41/160) (1/160) tau := by
            convert childLL hs22130 hx22130 hy22130 using 1 <;> norm_num
          exact Batch0111.cell0888.sound htau (by
            simp only [Batch0111.cell0888, Batch0111.tau0888, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221300 (by positivity) using 1 <;> norm_num)
        · have hs221302 : InSquare (-39/160) (43/160) (1/160) tau := by
            convert childUL hs22130 hx22130 hy22130 using 1 <;> norm_num
          exact Batch0111.cell0890.sound htau (by
            simp only [Batch0111.cell0890, Batch0111.tau0890, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy22130 | hy22130
        · have hs221301 : InSquare (-37/160) (41/160) (1/160) tau := by
            convert childLR hs22130 hx22130 hy22130 using 1 <;> norm_num
          exact Batch0111.cell0889.sound htau (by
            simp only [Batch0111.cell0889, Batch0111.tau0889, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221301 (by positivity) using 1 <;> norm_num)
        · have hs221303 : InSquare (-37/160) (43/160) (1/160) tau := by
            convert childUR hs22130 hx22130 hy22130 using 1 <;> norm_num
          exact Batch0111.cell0891.sound htau (by
            simp only [Batch0111.cell0891, Batch0111.tau0891, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221303 (by positivity) using 1 <;> norm_num)
    · have hs22132 : InSquare (-19/80) (23/80) (1/80) tau := by
        convert childUL hs hx2213 hy2213 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx22132 | hx22132
      · rcases le_total tau.im (23/80 : ℝ) with hy22132 | hy22132
        · have hs221320 : InSquare (-39/160) (9/32) (1/160) tau := by
            convert childLL hs22132 hx22132 hy22132 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx221320 | hx221320
          · rcases le_total tau.im (9/32 : ℝ) with hy221320 | hy221320
            · have hs2213200 : InSquare (-79/320) (89/320) (1/320) tau := by
                convert childLL hs221320 hx221320 hy221320 using 1 <;> norm_num
              exact Batch0244.cell1959.sound htau (by
                simp only [Batch0244.cell1959, Batch0244.tau1959, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213200 (by positivity) using 1 <;> norm_num)
            · have hs2213202 : InSquare (-79/320) (91/320) (1/320) tau := by
                convert childUL hs221320 hx221320 hy221320 using 1 <;> norm_num
              exact Batch0245.cell1961.sound htau (by
                simp only [Batch0245.cell1961, Batch0245.tau1961, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy221320 | hy221320
            · have hs2213201 : InSquare (-77/320) (89/320) (1/320) tau := by
                convert childLR hs221320 hx221320 hy221320 using 1 <;> norm_num
              exact Batch0245.cell1960.sound htau (by
                simp only [Batch0245.cell1960, Batch0245.tau1960, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213201 (by positivity) using 1 <;> norm_num)
            · have hs2213203 : InSquare (-77/320) (91/320) (1/320) tau := by
                convert childUR hs221320 hx221320 hy221320 using 1 <;> norm_num
              exact Batch0245.cell1962.sound htau (by
                simp only [Batch0245.cell1962, Batch0245.tau1962, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213203 (by positivity) using 1 <;> norm_num)
        · have hs221322 : InSquare (-39/160) (47/160) (1/160) tau := by
            convert childUL hs22132 hx22132 hy22132 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx221322 | hx221322
          · rcases le_total tau.im (47/160 : ℝ) with hy221322 | hy221322
            · have hs2213220 : InSquare (-79/320) (93/320) (1/320) tau := by
                convert childLL hs221322 hx221322 hy221322 using 1 <;> norm_num
              exact Batch0245.cell1967.sound htau (by
                simp only [Batch0245.cell1967, Batch0245.tau1967, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213220 (by positivity) using 1 <;> norm_num)
            · have hs2213222 : InSquare (-79/320) (19/64) (1/320) tau := by
                convert childUL hs221322 hx221322 hy221322 using 1 <;> norm_num
              exact Batch0246.cell1969.sound htau (by
                simp only [Batch0246.cell1969, Batch0246.tau1969, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy221322 | hy221322
            · have hs2213221 : InSquare (-77/320) (93/320) (1/320) tau := by
                convert childLR hs221322 hx221322 hy221322 using 1 <;> norm_num
              exact Batch0246.cell1968.sound htau (by
                simp only [Batch0246.cell1968, Batch0246.tau1968, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213221 (by positivity) using 1 <;> norm_num)
            · have hs2213223 : InSquare (-77/320) (19/64) (1/320) tau := by
                convert childUR hs221322 hx221322 hy221322 using 1 <;> norm_num
              exact Batch0246.cell1970.sound htau (by
                simp only [Batch0246.cell1970, Batch0246.tau1970, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy22132 | hy22132
        · have hs221321 : InSquare (-37/160) (9/32) (1/160) tau := by
            convert childLR hs22132 hx22132 hy22132 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx221321 | hx221321
          · rcases le_total tau.im (9/32 : ℝ) with hy221321 | hy221321
            · have hs2213210 : InSquare (-15/64) (89/320) (1/320) tau := by
                convert childLL hs221321 hx221321 hy221321 using 1 <;> norm_num
              exact Batch0245.cell1963.sound htau (by
                simp only [Batch0245.cell1963, Batch0245.tau1963, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213210 (by positivity) using 1 <;> norm_num)
            · have hs2213212 : InSquare (-15/64) (91/320) (1/320) tau := by
                convert childUL hs221321 hx221321 hy221321 using 1 <;> norm_num
              exact Batch0245.cell1965.sound htau (by
                simp only [Batch0245.cell1965, Batch0245.tau1965, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy221321 | hy221321
            · have hs2213211 : InSquare (-73/320) (89/320) (1/320) tau := by
                convert childLR hs221321 hx221321 hy221321 using 1 <;> norm_num
              exact Batch0245.cell1964.sound htau (by
                simp only [Batch0245.cell1964, Batch0245.tau1964, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213211 (by positivity) using 1 <;> norm_num)
            · have hs2213213 : InSquare (-73/320) (91/320) (1/320) tau := by
                convert childUR hs221321 hx221321 hy221321 using 1 <;> norm_num
              exact Batch0245.cell1966.sound htau (by
                simp only [Batch0245.cell1966, Batch0245.tau1966, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213213 (by positivity) using 1 <;> norm_num)
        · have hs221323 : InSquare (-37/160) (47/160) (1/160) tau := by
            convert childUR hs22132 hx22132 hy22132 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx221323 | hx221323
          · rcases le_total tau.im (47/160 : ℝ) with hy221323 | hy221323
            · have hs2213230 : InSquare (-15/64) (93/320) (1/320) tau := by
                convert childLL hs221323 hx221323 hy221323 using 1 <;> norm_num
              exact Batch0246.cell1971.sound htau (by
                simp only [Batch0246.cell1971, Batch0246.tau1971, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213230 (by positivity) using 1 <;> norm_num)
            · have hs2213232 : InSquare (-15/64) (19/64) (1/320) tau := by
                convert childUL hs221323 hx221323 hy221323 using 1 <;> norm_num
              exact Batch0246.cell1973.sound htau (by
                simp only [Batch0246.cell1973, Batch0246.tau1973, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy221323 | hy221323
            · have hs2213231 : InSquare (-73/320) (93/320) (1/320) tau := by
                convert childLR hs221323 hx221323 hy221323 using 1 <;> norm_num
              exact Batch0246.cell1972.sound htau (by
                simp only [Batch0246.cell1972, Batch0246.tau1972, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213231 (by positivity) using 1 <;> norm_num)
            · have hs2213233 : InSquare (-73/320) (19/64) (1/320) tau := by
                convert childUR hs221323 hx221323 hy221323 using 1 <;> norm_num
              exact Batch0246.cell1974.sound htau (by
                simp only [Batch0246.cell1974, Batch0246.tau1974, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy2213 | hy2213
    · have hs22131 : InSquare (-17/80) (21/80) (1/80) tau := by
        convert childLR hs hx2213 hy2213 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx22131 | hx22131
      · rcases le_total tau.im (21/80 : ℝ) with hy22131 | hy22131
        · have hs221310 : InSquare (-7/32) (41/160) (1/160) tau := by
            convert childLL hs22131 hx22131 hy22131 using 1 <;> norm_num
          exact Batch0111.cell0892.sound htau (by
            simp only [Batch0111.cell0892, Batch0111.tau0892, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221310 (by positivity) using 1 <;> norm_num)
        · have hs221312 : InSquare (-7/32) (43/160) (1/160) tau := by
            convert childUL hs22131 hx22131 hy22131 using 1 <;> norm_num
          exact Batch0111.cell0894.sound htau (by
            simp only [Batch0111.cell0894, Batch0111.tau0894, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy22131 | hy22131
        · have hs221311 : InSquare (-33/160) (41/160) (1/160) tau := by
            convert childLR hs22131 hx22131 hy22131 using 1 <;> norm_num
          exact Batch0111.cell0893.sound htau (by
            simp only [Batch0111.cell0893, Batch0111.tau0893, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221311 (by positivity) using 1 <;> norm_num)
        · have hs221313 : InSquare (-33/160) (43/160) (1/160) tau := by
            convert childUR hs22131 hx22131 hy22131 using 1 <;> norm_num
          exact Batch0111.cell0895.sound htau (by
            simp only [Batch0111.cell0895, Batch0111.tau0895, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221313 (by positivity) using 1 <;> norm_num)
    · have hs22133 : InSquare (-17/80) (23/80) (1/80) tau := by
        convert childUR hs hx2213 hy2213 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx22133 | hx22133
      · rcases le_total tau.im (23/80 : ℝ) with hy22133 | hy22133
        · have hs221330 : InSquare (-7/32) (9/32) (1/160) tau := by
            convert childLL hs22133 hx22133 hy22133 using 1 <;> norm_num
          exact Batch0112.cell0896.sound htau (by
            simp only [Batch0112.cell0896, Batch0112.tau0896, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221330 (by positivity) using 1 <;> norm_num)
        · have hs221332 : InSquare (-7/32) (47/160) (1/160) tau := by
            convert childUL hs22133 hx22133 hy22133 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx221332 | hx221332
          · rcases le_total tau.im (47/160 : ℝ) with hy221332 | hy221332
            · have hs2213320 : InSquare (-71/320) (93/320) (1/320) tau := by
                convert childLL hs221332 hx221332 hy221332 using 1 <;> norm_num
              exact Batch0246.cell1975.sound htau (by
                simp only [Batch0246.cell1975, Batch0246.tau1975, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213320 (by positivity) using 1 <;> norm_num)
            · have hs2213322 : InSquare (-71/320) (19/64) (1/320) tau := by
                convert childUL hs221332 hx221332 hy221332 using 1 <;> norm_num
              exact Batch0247.cell1977.sound htau (by
                simp only [Batch0247.cell1977, Batch0247.tau1977, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy221332 | hy221332
            · have hs2213321 : InSquare (-69/320) (93/320) (1/320) tau := by
                convert childLR hs221332 hx221332 hy221332 using 1 <;> norm_num
              exact Batch0247.cell1976.sound htau (by
                simp only [Batch0247.cell1976, Batch0247.tau1976, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213321 (by positivity) using 1 <;> norm_num)
            · have hs2213323 : InSquare (-69/320) (19/64) (1/320) tau := by
                convert childUR hs221332 hx221332 hy221332 using 1 <;> norm_num
              exact Batch0247.cell1978.sound htau (by
                simp only [Batch0247.cell1978, Batch0247.tau1978, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy22133 | hy22133
        · have hs221331 : InSquare (-33/160) (9/32) (1/160) tau := by
            convert childLR hs22133 hx22133 hy22133 using 1 <;> norm_num
          exact Batch0112.cell0897.sound htau (by
            simp only [Batch0112.cell0897, Batch0112.tau0897, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221331 (by positivity) using 1 <;> norm_num)
        · have hs221333 : InSquare (-33/160) (47/160) (1/160) tau := by
            convert childUR hs22133 hx22133 hy22133 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx221333 | hx221333
          · rcases le_total tau.im (47/160 : ℝ) with hy221333 | hy221333
            · have hs2213330 : InSquare (-67/320) (93/320) (1/320) tau := by
                convert childLL hs221333 hx221333 hy221333 using 1 <;> norm_num
              exact Batch0247.cell1979.sound htau (by
                simp only [Batch0247.cell1979, Batch0247.tau1979, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213330 (by positivity) using 1 <;> norm_num)
            · have hs2213332 : InSquare (-67/320) (19/64) (1/320) tau := by
                convert childUL hs221333 hx221333 hy221333 using 1 <;> norm_num
              exact Batch0247.cell1981.sound htau (by
                simp only [Batch0247.cell1981, Batch0247.tau1981, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy221333 | hy221333
            · have hs2213331 : InSquare (-13/64) (93/320) (1/320) tau := by
                convert childLR hs221333 hx221333 hy221333 using 1 <;> norm_num
              exact Batch0247.cell1980.sound htau (by
                simp only [Batch0247.cell1980, Batch0247.tau1980, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213331 (by positivity) using 1 <;> norm_num)
            · have hs2213333 : InSquare (-13/64) (19/64) (1/320) tau := by
                convert childUR hs221333 hx221333 hy221333 using 1 <;> norm_num
              exact Batch0247.cell1982.sound htau (by
                simp only [Batch0247.cell1982, Batch0247.tau1982, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2213

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2230 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2230

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_22300 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/80) (5/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/40)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/80) (27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/40)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22303 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-21/80) (27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/4)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_223012 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-43/160) (51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/80)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_223013 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-41/160) (51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/4)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2230100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-87/320) (97/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+43/160)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2230102 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-87/320) (99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+43/160)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2230103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-17/64) (99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/80)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx2230 | hx2230
  · rcases le_total tau.im (13/40 : ℝ) with hy2230 | hy2230
    · have hs22300 : InSquare (-23/80) (5/16) (1/80) tau := by
        convert childLL hs hx2230 hy2230 using 1 <;> norm_num
      exact (outside_22300 htau hs22300).elim
    · have hs22302 : InSquare (-23/80) (27/80) (1/80) tau := by
        convert childUL hs hx2230 hy2230 using 1 <;> norm_num
      exact (outside_22302 htau hs22302).elim
  · rcases le_total tau.im (13/40 : ℝ) with hy2230 | hy2230
    · have hs22301 : InSquare (-21/80) (5/16) (1/80) tau := by
        convert childLR hs hx2230 hy2230 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx22301 | hx22301
      · rcases le_total tau.im (5/16 : ℝ) with hy22301 | hy22301
        · have hs223010 : InSquare (-43/160) (49/160) (1/160) tau := by
            convert childLL hs22301 hx22301 hy22301 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx223010 | hx223010
          · rcases le_total tau.im (49/160 : ℝ) with hy223010 | hy223010
            · have hs2230100 : InSquare (-87/320) (97/320) (1/320) tau := by
                convert childLL hs223010 hx223010 hy223010 using 1 <;> norm_num
              exact (outside_2230100 htau hs2230100).elim
            · have hs2230102 : InSquare (-87/320) (99/320) (1/320) tau := by
                convert childUL hs223010 hx223010 hy223010 using 1 <;> norm_num
              exact (outside_2230102 htau hs2230102).elim
          · rcases le_total tau.im (49/160 : ℝ) with hy223010 | hy223010
            · have hs2230101 : InSquare (-17/64) (97/320) (1/320) tau := by
                convert childLR hs223010 hx223010 hy223010 using 1 <;> norm_num
              exact Batch0247.cell1983.sound htau (by
                simp only [Batch0247.cell1983, Batch0247.tau1983, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2230101 (by positivity) using 1 <;> norm_num)
            · have hs2230103 : InSquare (-17/64) (99/320) (1/320) tau := by
                convert childUR hs223010 hx223010 hy223010 using 1 <;> norm_num
              exact (outside_2230103 htau hs2230103).elim
        · have hs223012 : InSquare (-43/160) (51/160) (1/160) tau := by
            convert childUL hs22301 hx22301 hy22301 using 1 <;> norm_num
          exact (outside_223012 htau hs223012).elim
      · rcases le_total tau.im (5/16 : ℝ) with hy22301 | hy22301
        · have hs223011 : InSquare (-41/160) (49/160) (1/160) tau := by
            convert childLR hs22301 hx22301 hy22301 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx223011 | hx223011
          · rcases le_total tau.im (49/160 : ℝ) with hy223011 | hy223011
            · have hs2230110 : InSquare (-83/320) (97/320) (1/320) tau := by
                convert childLL hs223011 hx223011 hy223011 using 1 <;> norm_num
              exact Batch0248.cell1984.sound htau (by
                simp only [Batch0248.cell1984, Batch0248.tau1984, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2230110 (by positivity) using 1 <;> norm_num)
            · have hs2230112 : InSquare (-83/320) (99/320) (1/320) tau := by
                convert childUL hs223011 hx223011 hy223011 using 1 <;> norm_num
              exact Batch0248.cell1986.sound htau (by
                simp only [Batch0248.cell1986, Batch0248.tau1986, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2230112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy223011 | hy223011
            · have hs2230111 : InSquare (-81/320) (97/320) (1/320) tau := by
                convert childLR hs223011 hx223011 hy223011 using 1 <;> norm_num
              exact Batch0248.cell1985.sound htau (by
                simp only [Batch0248.cell1985, Batch0248.tau1985, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2230111 (by positivity) using 1 <;> norm_num)
            · have hs2230113 : InSquare (-81/320) (99/320) (1/320) tau := by
                convert childUR hs223011 hx223011 hy223011 using 1 <;> norm_num
              exact Batch0248.cell1987.sound htau (by
                simp only [Batch0248.cell1987, Batch0248.tau1987, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2230113 (by positivity) using 1 <;> norm_num)
        · have hs223013 : InSquare (-41/160) (51/160) (1/160) tau := by
            convert childUR hs22301 hx22301 hy22301 using 1 <;> norm_num
          exact (outside_223013 htau hs223013).elim
    · have hs22303 : InSquare (-21/80) (27/80) (1/80) tau := by
        convert childUR hs hx2230 hy2230 using 1 <;> norm_num
      exact (outside_22303 htau hs22303).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2230

end


