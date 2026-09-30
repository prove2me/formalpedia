-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage0120__18
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage0120__18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:20:05.361985+00:00
-- url     : https://prove2.me/theorems/cea0c857-1df4-4ea7-bc62-9ab0f2cc1fb6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0120 (+17 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0121, GeneralCK.Certifi…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0120 (+17 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0121, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0122, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0123, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0130, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0131, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0132, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0133, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0200, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0201, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0202, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0203, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0210, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0211, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0212, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0213, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0220, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0221)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0120 (+17 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0121, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0122, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0123, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0130, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0131, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0132, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0133, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0200, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0201, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0202, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0203, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0210, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0211, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0212, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0213, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0220, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0221)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0120 (+17 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0121, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0122, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0123, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0130, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0131, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0132, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0133, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0200, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0201, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0202, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0203, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0210, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0211, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0212, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0213, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0220, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0221) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0120 (+17 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0121, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0122, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0123, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0130, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0131, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0132, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0133, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0200, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0201, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0202, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0203, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0210, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0211, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0212, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0213, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0220, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0221).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0054
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0055
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0056
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0057
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0058
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0006
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0059
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0007
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0060
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0008
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0192
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0061
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0062
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0063
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0064
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0009
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0065
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0066
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0067
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0010
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0068
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0069
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0011

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0120 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0120

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx0120 | hx0120
  · rcases le_total tau.im (-11/40 : ℝ) with hy0120 | hy0120
    · have hs01200 : InSquare (-3/16) (-23/80) (1/80) tau := by
        convert childLL hs hx0120 hy0120 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx01200 | hx01200
      · rcases le_total tau.im (-23/80 : ℝ) with hy01200 | hy01200
        · have hs012000 : InSquare (-31/160) (-47/160) (1/160) tau := by
            convert childLL hs01200 hx01200 hy01200 using 1 <;> norm_num
          exact Batch0054.cell0433.sound htau (by
            simp only [Batch0054.cell0433, Batch0054.tau0433, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012000 (by positivity) using 1 <;> norm_num)
        · have hs012002 : InSquare (-31/160) (-9/32) (1/160) tau := by
            convert childUL hs01200 hx01200 hy01200 using 1 <;> norm_num
          exact Batch0054.cell0435.sound htau (by
            simp only [Batch0054.cell0435, Batch0054.tau0435, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy01200 | hy01200
        · have hs012001 : InSquare (-29/160) (-47/160) (1/160) tau := by
            convert childLR hs01200 hx01200 hy01200 using 1 <;> norm_num
          exact Batch0054.cell0434.sound htau (by
            simp only [Batch0054.cell0434, Batch0054.tau0434, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012001 (by positivity) using 1 <;> norm_num)
        · have hs012003 : InSquare (-29/160) (-9/32) (1/160) tau := by
            convert childUR hs01200 hx01200 hy01200 using 1 <;> norm_num
          exact Batch0054.cell0436.sound htau (by
            simp only [Batch0054.cell0436, Batch0054.tau0436, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012003 (by positivity) using 1 <;> norm_num)
    · have hs01202 : InSquare (-3/16) (-21/80) (1/80) tau := by
        convert childUL hs hx0120 hy0120 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx01202 | hx01202
      · rcases le_total tau.im (-21/80 : ℝ) with hy01202 | hy01202
        · have hs012020 : InSquare (-31/160) (-43/160) (1/160) tau := by
            convert childLL hs01202 hx01202 hy01202 using 1 <;> norm_num
          exact Batch0055.cell0441.sound htau (by
            simp only [Batch0055.cell0441, Batch0055.tau0441, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012020 (by positivity) using 1 <;> norm_num)
        · have hs012022 : InSquare (-31/160) (-41/160) (1/160) tau := by
            convert childUL hs01202 hx01202 hy01202 using 1 <;> norm_num
          exact Batch0055.cell0443.sound htau (by
            simp only [Batch0055.cell0443, Batch0055.tau0443, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy01202 | hy01202
        · have hs012021 : InSquare (-29/160) (-43/160) (1/160) tau := by
            convert childLR hs01202 hx01202 hy01202 using 1 <;> norm_num
          exact Batch0055.cell0442.sound htau (by
            simp only [Batch0055.cell0442, Batch0055.tau0442, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012021 (by positivity) using 1 <;> norm_num)
        · have hs012023 : InSquare (-29/160) (-41/160) (1/160) tau := by
            convert childUR hs01202 hx01202 hy01202 using 1 <;> norm_num
          exact Batch0055.cell0444.sound htau (by
            simp only [Batch0055.cell0444, Batch0055.tau0444, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy0120 | hy0120
    · have hs01201 : InSquare (-13/80) (-23/80) (1/80) tau := by
        convert childLR hs hx0120 hy0120 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx01201 | hx01201
      · rcases le_total tau.im (-23/80 : ℝ) with hy01201 | hy01201
        · have hs012010 : InSquare (-27/160) (-47/160) (1/160) tau := by
            convert childLL hs01201 hx01201 hy01201 using 1 <;> norm_num
          exact Batch0054.cell0437.sound htau (by
            simp only [Batch0054.cell0437, Batch0054.tau0437, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012010 (by positivity) using 1 <;> norm_num)
        · have hs012012 : InSquare (-27/160) (-9/32) (1/160) tau := by
            convert childUL hs01201 hx01201 hy01201 using 1 <;> norm_num
          exact Batch0054.cell0439.sound htau (by
            simp only [Batch0054.cell0439, Batch0054.tau0439, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy01201 | hy01201
        · have hs012011 : InSquare (-5/32) (-47/160) (1/160) tau := by
            convert childLR hs01201 hx01201 hy01201 using 1 <;> norm_num
          exact Batch0054.cell0438.sound htau (by
            simp only [Batch0054.cell0438, Batch0054.tau0438, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012011 (by positivity) using 1 <;> norm_num)
        · have hs012013 : InSquare (-5/32) (-9/32) (1/160) tau := by
            convert childUR hs01201 hx01201 hy01201 using 1 <;> norm_num
          exact Batch0055.cell0440.sound htau (by
            simp only [Batch0055.cell0440, Batch0055.tau0440, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012013 (by positivity) using 1 <;> norm_num)
    · have hs01203 : InSquare (-13/80) (-21/80) (1/80) tau := by
        convert childUR hs hx0120 hy0120 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx01203 | hx01203
      · rcases le_total tau.im (-21/80 : ℝ) with hy01203 | hy01203
        · have hs012030 : InSquare (-27/160) (-43/160) (1/160) tau := by
            convert childLL hs01203 hx01203 hy01203 using 1 <;> norm_num
          exact Batch0055.cell0445.sound htau (by
            simp only [Batch0055.cell0445, Batch0055.tau0445, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012030 (by positivity) using 1 <;> norm_num)
        · have hs012032 : InSquare (-27/160) (-41/160) (1/160) tau := by
            convert childUL hs01203 hx01203 hy01203 using 1 <;> norm_num
          exact Batch0055.cell0447.sound htau (by
            simp only [Batch0055.cell0447, Batch0055.tau0447, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy01203 | hy01203
        · have hs012031 : InSquare (-5/32) (-43/160) (1/160) tau := by
            convert childLR hs01203 hx01203 hy01203 using 1 <;> norm_num
          exact Batch0055.cell0446.sound htau (by
            simp only [Batch0055.cell0446, Batch0055.tau0446, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012031 (by positivity) using 1 <;> norm_num)
        · have hs012033 : InSquare (-5/32) (-41/160) (1/160) tau := by
            convert childUR hs01203 hx01203 hy01203 using 1 <;> norm_num
          exact Batch0056.cell0448.sound htau (by
            simp only [Batch0056.cell0448, Batch0056.tau0448, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0120

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0121 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0121

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx0121 | hx0121
  · rcases le_total tau.im (-11/40 : ℝ) with hy0121 | hy0121
    · have hs01210 : InSquare (-11/80) (-23/80) (1/80) tau := by
        convert childLL hs hx0121 hy0121 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx01210 | hx01210
      · rcases le_total tau.im (-23/80 : ℝ) with hy01210 | hy01210
        · have hs012100 : InSquare (-23/160) (-47/160) (1/160) tau := by
            convert childLL hs01210 hx01210 hy01210 using 1 <;> norm_num
          exact Batch0056.cell0449.sound htau (by
            simp only [Batch0056.cell0449, Batch0056.tau0449, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012100 (by positivity) using 1 <;> norm_num)
        · have hs012102 : InSquare (-23/160) (-9/32) (1/160) tau := by
            convert childUL hs01210 hx01210 hy01210 using 1 <;> norm_num
          exact Batch0056.cell0451.sound htau (by
            simp only [Batch0056.cell0451, Batch0056.tau0451, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy01210 | hy01210
        · have hs012101 : InSquare (-21/160) (-47/160) (1/160) tau := by
            convert childLR hs01210 hx01210 hy01210 using 1 <;> norm_num
          exact Batch0056.cell0450.sound htau (by
            simp only [Batch0056.cell0450, Batch0056.tau0450, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012101 (by positivity) using 1 <;> norm_num)
        · have hs012103 : InSquare (-21/160) (-9/32) (1/160) tau := by
            convert childUR hs01210 hx01210 hy01210 using 1 <;> norm_num
          exact Batch0056.cell0452.sound htau (by
            simp only [Batch0056.cell0452, Batch0056.tau0452, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012103 (by positivity) using 1 <;> norm_num)
    · have hs01212 : InSquare (-11/80) (-21/80) (1/80) tau := by
        convert childUL hs hx0121 hy0121 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx01212 | hx01212
      · rcases le_total tau.im (-21/80 : ℝ) with hy01212 | hy01212
        · have hs012120 : InSquare (-23/160) (-43/160) (1/160) tau := by
            convert childLL hs01212 hx01212 hy01212 using 1 <;> norm_num
          exact Batch0057.cell0457.sound htau (by
            simp only [Batch0057.cell0457, Batch0057.tau0457, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012120 (by positivity) using 1 <;> norm_num)
        · have hs012122 : InSquare (-23/160) (-41/160) (1/160) tau := by
            convert childUL hs01212 hx01212 hy01212 using 1 <;> norm_num
          exact Batch0057.cell0459.sound htau (by
            simp only [Batch0057.cell0459, Batch0057.tau0459, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy01212 | hy01212
        · have hs012121 : InSquare (-21/160) (-43/160) (1/160) tau := by
            convert childLR hs01212 hx01212 hy01212 using 1 <;> norm_num
          exact Batch0057.cell0458.sound htau (by
            simp only [Batch0057.cell0458, Batch0057.tau0458, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012121 (by positivity) using 1 <;> norm_num)
        · have hs012123 : InSquare (-21/160) (-41/160) (1/160) tau := by
            convert childUR hs01212 hx01212 hy01212 using 1 <;> norm_num
          exact Batch0057.cell0460.sound htau (by
            simp only [Batch0057.cell0460, Batch0057.tau0460, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy0121 | hy0121
    · have hs01211 : InSquare (-9/80) (-23/80) (1/80) tau := by
        convert childLR hs hx0121 hy0121 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx01211 | hx01211
      · rcases le_total tau.im (-23/80 : ℝ) with hy01211 | hy01211
        · have hs012110 : InSquare (-19/160) (-47/160) (1/160) tau := by
            convert childLL hs01211 hx01211 hy01211 using 1 <;> norm_num
          exact Batch0056.cell0453.sound htau (by
            simp only [Batch0056.cell0453, Batch0056.tau0453, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012110 (by positivity) using 1 <;> norm_num)
        · have hs012112 : InSquare (-19/160) (-9/32) (1/160) tau := by
            convert childUL hs01211 hx01211 hy01211 using 1 <;> norm_num
          exact Batch0056.cell0455.sound htau (by
            simp only [Batch0056.cell0455, Batch0056.tau0455, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy01211 | hy01211
        · have hs012111 : InSquare (-17/160) (-47/160) (1/160) tau := by
            convert childLR hs01211 hx01211 hy01211 using 1 <;> norm_num
          exact Batch0056.cell0454.sound htau (by
            simp only [Batch0056.cell0454, Batch0056.tau0454, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012111 (by positivity) using 1 <;> norm_num)
        · have hs012113 : InSquare (-17/160) (-9/32) (1/160) tau := by
            convert childUR hs01211 hx01211 hy01211 using 1 <;> norm_num
          exact Batch0057.cell0456.sound htau (by
            simp only [Batch0057.cell0456, Batch0057.tau0456, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012113 (by positivity) using 1 <;> norm_num)
    · have hs01213 : InSquare (-9/80) (-21/80) (1/80) tau := by
        convert childUR hs hx0121 hy0121 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx01213 | hx01213
      · rcases le_total tau.im (-21/80 : ℝ) with hy01213 | hy01213
        · have hs012130 : InSquare (-19/160) (-43/160) (1/160) tau := by
            convert childLL hs01213 hx01213 hy01213 using 1 <;> norm_num
          exact Batch0057.cell0461.sound htau (by
            simp only [Batch0057.cell0461, Batch0057.tau0461, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012130 (by positivity) using 1 <;> norm_num)
        · have hs012132 : InSquare (-19/160) (-41/160) (1/160) tau := by
            convert childUL hs01213 hx01213 hy01213 using 1 <;> norm_num
          exact Batch0057.cell0463.sound htau (by
            simp only [Batch0057.cell0463, Batch0057.tau0463, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy01213 | hy01213
        · have hs012131 : InSquare (-17/160) (-43/160) (1/160) tau := by
            convert childLR hs01213 hx01213 hy01213 using 1 <;> norm_num
          exact Batch0057.cell0462.sound htau (by
            simp only [Batch0057.cell0462, Batch0057.tau0462, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012131 (by positivity) using 1 <;> norm_num)
        · have hs012133 : InSquare (-17/160) (-41/160) (1/160) tau := by
            convert childUR hs01213 hx01213 hy01213 using 1 <;> norm_num
          exact Batch0058.cell0464.sound htau (by
            simp only [Batch0058.cell0464, Batch0058.tau0464, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0121

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0122 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0122

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx0122 | hx0122
  · rcases le_total tau.im (-9/40 : ℝ) with hy0122 | hy0122
    · have hs01220 : InSquare (-3/16) (-19/80) (1/80) tau := by
        convert childLL hs hx0122 hy0122 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx01220 | hx01220
      · rcases le_total tau.im (-19/80 : ℝ) with hy01220 | hy01220
        · have hs012200 : InSquare (-31/160) (-39/160) (1/160) tau := by
            convert childLL hs01220 hx01220 hy01220 using 1 <;> norm_num
          exact Batch0058.cell0465.sound htau (by
            simp only [Batch0058.cell0465, Batch0058.tau0465, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012200 (by positivity) using 1 <;> norm_num)
        · have hs012202 : InSquare (-31/160) (-37/160) (1/160) tau := by
            convert childUL hs01220 hx01220 hy01220 using 1 <;> norm_num
          exact Batch0058.cell0467.sound htau (by
            simp only [Batch0058.cell0467, Batch0058.tau0467, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy01220 | hy01220
        · have hs012201 : InSquare (-29/160) (-39/160) (1/160) tau := by
            convert childLR hs01220 hx01220 hy01220 using 1 <;> norm_num
          exact Batch0058.cell0466.sound htau (by
            simp only [Batch0058.cell0466, Batch0058.tau0466, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012201 (by positivity) using 1 <;> norm_num)
        · have hs012203 : InSquare (-29/160) (-37/160) (1/160) tau := by
            convert childUR hs01220 hx01220 hy01220 using 1 <;> norm_num
          exact Batch0058.cell0468.sound htau (by
            simp only [Batch0058.cell0468, Batch0058.tau0468, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012203 (by positivity) using 1 <;> norm_num)
    · have hs01222 : InSquare (-3/16) (-17/80) (1/80) tau := by
        convert childUL hs hx0122 hy0122 using 1 <;> norm_num
      exact Batch0006.cell0052.sound htau (by
        simp only [Batch0006.cell0052, Batch0006.tau0052, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01222 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy0122 | hy0122
    · have hs01221 : InSquare (-13/80) (-19/80) (1/80) tau := by
        convert childLR hs hx0122 hy0122 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx01221 | hx01221
      · rcases le_total tau.im (-19/80 : ℝ) with hy01221 | hy01221
        · have hs012210 : InSquare (-27/160) (-39/160) (1/160) tau := by
            convert childLL hs01221 hx01221 hy01221 using 1 <;> norm_num
          exact Batch0058.cell0469.sound htau (by
            simp only [Batch0058.cell0469, Batch0058.tau0469, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012210 (by positivity) using 1 <;> norm_num)
        · have hs012212 : InSquare (-27/160) (-37/160) (1/160) tau := by
            convert childUL hs01221 hx01221 hy01221 using 1 <;> norm_num
          exact Batch0058.cell0471.sound htau (by
            simp only [Batch0058.cell0471, Batch0058.tau0471, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy01221 | hy01221
        · have hs012211 : InSquare (-5/32) (-39/160) (1/160) tau := by
            convert childLR hs01221 hx01221 hy01221 using 1 <;> norm_num
          exact Batch0058.cell0470.sound htau (by
            simp only [Batch0058.cell0470, Batch0058.tau0470, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012211 (by positivity) using 1 <;> norm_num)
        · have hs012213 : InSquare (-5/32) (-37/160) (1/160) tau := by
            convert childUR hs01221 hx01221 hy01221 using 1 <;> norm_num
          exact Batch0059.cell0472.sound htau (by
            simp only [Batch0059.cell0472, Batch0059.tau0472, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012213 (by positivity) using 1 <;> norm_num)
    · have hs01223 : InSquare (-13/80) (-17/80) (1/80) tau := by
        convert childUR hs hx0122 hy0122 using 1 <;> norm_num
      exact Batch0006.cell0053.sound htau (by
        simp only [Batch0006.cell0053, Batch0006.tau0053, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01223 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0122

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0123 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0123

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx0123 | hx0123
  · rcases le_total tau.im (-9/40 : ℝ) with hy0123 | hy0123
    · have hs01230 : InSquare (-11/80) (-19/80) (1/80) tau := by
        convert childLL hs hx0123 hy0123 using 1 <;> norm_num
      exact Batch0006.cell0054.sound htau (by
        simp only [Batch0006.cell0054, Batch0006.tau0054, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01230 (by positivity) using 1 <;> norm_num)
    · have hs01232 : InSquare (-11/80) (-17/80) (1/80) tau := by
        convert childUL hs hx0123 hy0123 using 1 <;> norm_num
      exact Batch0007.cell0056.sound htau (by
        simp only [Batch0007.cell0056, Batch0007.tau0056, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01232 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy0123 | hy0123
    · have hs01231 : InSquare (-9/80) (-19/80) (1/80) tau := by
        convert childLR hs hx0123 hy0123 using 1 <;> norm_num
      exact Batch0006.cell0055.sound htau (by
        simp only [Batch0006.cell0055, Batch0006.tau0055, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01231 (by positivity) using 1 <;> norm_num)
    · have hs01233 : InSquare (-9/80) (-17/80) (1/80) tau := by
        convert childUR hs hx0123 hy0123 using 1 <;> norm_num
      exact Batch0007.cell0057.sound htau (by
        simp only [Batch0007.cell0057, Batch0007.tau0057, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0123

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0130 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0130

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx0130 | hx0130
  · rcases le_total tau.im (-11/40 : ℝ) with hy0130 | hy0130
    · have hs01300 : InSquare (-7/80) (-23/80) (1/80) tau := by
        convert childLL hs hx0130 hy0130 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx01300 | hx01300
      · rcases le_total tau.im (-23/80 : ℝ) with hy01300 | hy01300
        · have hs013000 : InSquare (-3/32) (-47/160) (1/160) tau := by
            convert childLL hs01300 hx01300 hy01300 using 1 <;> norm_num
          exact Batch0059.cell0473.sound htau (by
            simp only [Batch0059.cell0473, Batch0059.tau0473, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013000 (by positivity) using 1 <;> norm_num)
        · have hs013002 : InSquare (-3/32) (-9/32) (1/160) tau := by
            convert childUL hs01300 hx01300 hy01300 using 1 <;> norm_num
          exact Batch0059.cell0475.sound htau (by
            simp only [Batch0059.cell0475, Batch0059.tau0475, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy01300 | hy01300
        · have hs013001 : InSquare (-13/160) (-47/160) (1/160) tau := by
            convert childLR hs01300 hx01300 hy01300 using 1 <;> norm_num
          exact Batch0059.cell0474.sound htau (by
            simp only [Batch0059.cell0474, Batch0059.tau0474, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013001 (by positivity) using 1 <;> norm_num)
        · have hs013003 : InSquare (-13/160) (-9/32) (1/160) tau := by
            convert childUR hs01300 hx01300 hy01300 using 1 <;> norm_num
          exact Batch0059.cell0476.sound htau (by
            simp only [Batch0059.cell0476, Batch0059.tau0476, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013003 (by positivity) using 1 <;> norm_num)
    · have hs01302 : InSquare (-7/80) (-21/80) (1/80) tau := by
        convert childUL hs hx0130 hy0130 using 1 <;> norm_num
      exact Batch0007.cell0058.sound htau (by
        simp only [Batch0007.cell0058, Batch0007.tau0058, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01302 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy0130 | hy0130
    · have hs01301 : InSquare (-1/16) (-23/80) (1/80) tau := by
        convert childLR hs hx0130 hy0130 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx01301 | hx01301
      · rcases le_total tau.im (-23/80 : ℝ) with hy01301 | hy01301
        · have hs013010 : InSquare (-11/160) (-47/160) (1/160) tau := by
            convert childLL hs01301 hx01301 hy01301 using 1 <;> norm_num
          exact Batch0059.cell0477.sound htau (by
            simp only [Batch0059.cell0477, Batch0059.tau0477, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013010 (by positivity) using 1 <;> norm_num)
        · have hs013012 : InSquare (-11/160) (-9/32) (1/160) tau := by
            convert childUL hs01301 hx01301 hy01301 using 1 <;> norm_num
          exact Batch0059.cell0479.sound htau (by
            simp only [Batch0059.cell0479, Batch0059.tau0479, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy01301 | hy01301
        · have hs013011 : InSquare (-9/160) (-47/160) (1/160) tau := by
            convert childLR hs01301 hx01301 hy01301 using 1 <;> norm_num
          exact Batch0059.cell0478.sound htau (by
            simp only [Batch0059.cell0478, Batch0059.tau0478, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013011 (by positivity) using 1 <;> norm_num)
        · have hs013013 : InSquare (-9/160) (-9/32) (1/160) tau := by
            convert childUR hs01301 hx01301 hy01301 using 1 <;> norm_num
          exact Batch0060.cell0480.sound htau (by
            simp only [Batch0060.cell0480, Batch0060.tau0480, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013013 (by positivity) using 1 <;> norm_num)
    · have hs01303 : InSquare (-1/16) (-21/80) (1/80) tau := by
        convert childUR hs hx0130 hy0130 using 1 <;> norm_num
      exact Batch0007.cell0059.sound htau (by
        simp only [Batch0007.cell0059, Batch0007.tau0059, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01303 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0130

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0131 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0131

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx0131 | hx0131
  · rcases le_total tau.im (-11/40 : ℝ) with hy0131 | hy0131
    · have hs01310 : InSquare (-3/80) (-23/80) (1/80) tau := by
        convert childLL hs hx0131 hy0131 using 1 <;> norm_num
      exact Batch0007.cell0060.sound htau (by
        simp only [Batch0007.cell0060, Batch0007.tau0060, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01310 (by positivity) using 1 <;> norm_num)
    · have hs01312 : InSquare (-3/80) (-21/80) (1/80) tau := by
        convert childUL hs hx0131 hy0131 using 1 <;> norm_num
      exact Batch0007.cell0062.sound htau (by
        simp only [Batch0007.cell0062, Batch0007.tau0062, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01312 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy0131 | hy0131
    · have hs01311 : InSquare (-1/80) (-23/80) (1/80) tau := by
        convert childLR hs hx0131 hy0131 using 1 <;> norm_num
      exact Batch0007.cell0061.sound htau (by
        simp only [Batch0007.cell0061, Batch0007.tau0061, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01311 (by positivity) using 1 <;> norm_num)
    · have hs01313 : InSquare (-1/80) (-21/80) (1/80) tau := by
        convert childUR hs hx0131 hy0131 using 1 <;> norm_num
      exact Batch0007.cell0063.sound htau (by
        simp only [Batch0007.cell0063, Batch0007.tau0063, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01313 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0131

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0132 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0132

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx0132 | hx0132
  · rcases le_total tau.im (-9/40 : ℝ) with hy0132 | hy0132
    · have hs01320 : InSquare (-7/80) (-19/80) (1/80) tau := by
        convert childLL hs hx0132 hy0132 using 1 <;> norm_num
      exact Batch0008.cell0064.sound htau (by
        simp only [Batch0008.cell0064, Batch0008.tau0064, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01320 (by positivity) using 1 <;> norm_num)
    · have hs01322 : InSquare (-7/80) (-17/80) (1/80) tau := by
        convert childUL hs hx0132 hy0132 using 1 <;> norm_num
      exact Batch0008.cell0066.sound htau (by
        simp only [Batch0008.cell0066, Batch0008.tau0066, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01322 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy0132 | hy0132
    · have hs01321 : InSquare (-1/16) (-19/80) (1/80) tau := by
        convert childLR hs hx0132 hy0132 using 1 <;> norm_num
      exact Batch0008.cell0065.sound htau (by
        simp only [Batch0008.cell0065, Batch0008.tau0065, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01321 (by positivity) using 1 <;> norm_num)
    · have hs01323 : InSquare (-1/16) (-17/80) (1/80) tau := by
        convert childUR hs hx0132 hy0132 using 1 <;> norm_num
      exact Batch0008.cell0067.sound htau (by
        simp only [Batch0008.cell0067, Batch0008.tau0067, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01323 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0132

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0133 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0133

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx0133 | hx0133
  · rcases le_total tau.im (-9/40 : ℝ) with hy0133 | hy0133
    · have hs01330 : InSquare (-3/80) (-19/80) (1/80) tau := by
        convert childLL hs hx0133 hy0133 using 1 <;> norm_num
      exact Batch0008.cell0068.sound htau (by
        simp only [Batch0008.cell0068, Batch0008.tau0068, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01330 (by positivity) using 1 <;> norm_num)
    · have hs01332 : InSquare (-3/80) (-17/80) (1/80) tau := by
        convert childUL hs hx0133 hy0133 using 1 <;> norm_num
      exact Batch0008.cell0070.sound htau (by
        simp only [Batch0008.cell0070, Batch0008.tau0070, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01332 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy0133 | hy0133
    · have hs01331 : InSquare (-1/80) (-19/80) (1/80) tau := by
        convert childLR hs hx0133 hy0133 using 1 <;> norm_num
      exact Batch0008.cell0069.sound htau (by
        simp only [Batch0008.cell0069, Batch0008.tau0069, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01331 (by positivity) using 1 <;> norm_num)
    · have hs01333 : InSquare (-1/80) (-17/80) (1/80) tau := by
        convert childUR hs hx0133 hy0133 using 1 <;> norm_num
      exact Batch0008.cell0071.sound htau (by
        simp only [Batch0008.cell0071, Batch0008.tau0071, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0133

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0200 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0200

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_02000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/80) (-3/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/8)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_02002 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/80) (-13/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/8)]
  have himSq : (3/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_020010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-59/160) (-31/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/80)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_020012 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-59/160) (-29/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/80)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0200110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/64) (-63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+57/160)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0200111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-113/320) (-63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/20)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0200112 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/64) (-61/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+57/160)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/8 : ℝ) with hx0200 | hx0200
  · rcases le_total tau.im (-7/40 : ℝ) with hy0200 | hy0200
    · have hs02000 : InSquare (-31/80) (-3/16) (1/80) tau := by
        convert childLL hs hx0200 hy0200 using 1 <;> norm_num
      exact (outside_02000 htau hs02000).elim
    · have hs02002 : InSquare (-31/80) (-13/80) (1/80) tau := by
        convert childUL hs hx0200 hy0200 using 1 <;> norm_num
      exact (outside_02002 htau hs02002).elim
  · rcases le_total tau.im (-7/40 : ℝ) with hy0200 | hy0200
    · have hs02001 : InSquare (-29/80) (-3/16) (1/80) tau := by
        convert childLR hs hx0200 hy0200 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx02001 | hx02001
      · rcases le_total tau.im (-3/16 : ℝ) with hy02001 | hy02001
        · have hs020010 : InSquare (-59/160) (-31/160) (1/160) tau := by
            convert childLL hs02001 hx02001 hy02001 using 1 <;> norm_num
          exact (outside_020010 htau hs020010).elim
        · have hs020012 : InSquare (-59/160) (-29/160) (1/160) tau := by
            convert childUL hs02001 hx02001 hy02001 using 1 <;> norm_num
          exact (outside_020012 htau hs020012).elim
      · rcases le_total tau.im (-3/16 : ℝ) with hy02001 | hy02001
        · have hs020011 : InSquare (-57/160) (-31/160) (1/160) tau := by
            convert childLR hs02001 hx02001 hy02001 using 1 <;> norm_num
          rcases le_total tau.re (-57/160 : ℝ) with hx020011 | hx020011
          · rcases le_total tau.im (-31/160 : ℝ) with hy020011 | hy020011
            · have hs0200110 : InSquare (-23/64) (-63/320) (1/320) tau := by
                convert childLL hs020011 hx020011 hy020011 using 1 <;> norm_num
              exact (outside_0200110 htau hs0200110).elim
            · have hs0200112 : InSquare (-23/64) (-61/320) (1/320) tau := by
                convert childUL hs020011 hx020011 hy020011 using 1 <;> norm_num
              exact (outside_0200112 htau hs0200112).elim
          · rcases le_total tau.im (-31/160 : ℝ) with hy020011 | hy020011
            · have hs0200111 : InSquare (-113/320) (-63/320) (1/320) tau := by
                convert childLR hs020011 hx020011 hy020011 using 1 <;> norm_num
              exact (outside_0200111 htau hs0200111).elim
            · have hs0200113 : InSquare (-113/320) (-61/320) (1/320) tau := by
                convert childUR hs020011 hx020011 hy020011 using 1 <;> norm_num
              exact Batch0192.cell1540.sound htau (by
                simp only [Batch0192.cell1540, Batch0192.tau1540, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0200113 (by positivity) using 1 <;> norm_num)
        · have hs020013 : InSquare (-57/160) (-29/160) (1/160) tau := by
            convert childUR hs02001 hx02001 hy02001 using 1 <;> norm_num
          exact Batch0060.cell0481.sound htau (by
            simp only [Batch0060.cell0481, Batch0060.tau0481, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020013 (by positivity) using 1 <;> norm_num)
    · have hs02003 : InSquare (-29/80) (-13/80) (1/80) tau := by
        convert childUR hs hx0200 hy0200 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx02003 | hx02003
      · rcases le_total tau.im (-13/80 : ℝ) with hy02003 | hy02003
        · have hs020030 : InSquare (-59/160) (-27/160) (1/160) tau := by
            convert childLL hs02003 hx02003 hy02003 using 1 <;> norm_num
          exact Batch0060.cell0482.sound htau (by
            simp only [Batch0060.cell0482, Batch0060.tau0482, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020030 (by positivity) using 1 <;> norm_num)
        · have hs020032 : InSquare (-59/160) (-5/32) (1/160) tau := by
            convert childUL hs02003 hx02003 hy02003 using 1 <;> norm_num
          exact Batch0060.cell0484.sound htau (by
            simp only [Batch0060.cell0484, Batch0060.tau0484, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy02003 | hy02003
        · have hs020031 : InSquare (-57/160) (-27/160) (1/160) tau := by
            convert childLR hs02003 hx02003 hy02003 using 1 <;> norm_num
          exact Batch0060.cell0483.sound htau (by
            simp only [Batch0060.cell0483, Batch0060.tau0483, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020031 (by positivity) using 1 <;> norm_num)
        · have hs020033 : InSquare (-57/160) (-5/32) (1/160) tau := by
            convert childUR hs02003 hx02003 hy02003 using 1 <;> norm_num
          exact Batch0060.cell0485.sound htau (by
            simp only [Batch0060.cell0485, Batch0060.tau0485, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0200

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0201 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0201

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx0201 | hx0201
  · rcases le_total tau.im (-7/40 : ℝ) with hy0201 | hy0201
    · have hs02010 : InSquare (-27/80) (-3/16) (1/80) tau := by
        convert childLL hs hx0201 hy0201 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx02010 | hx02010
      · rcases le_total tau.im (-3/16 : ℝ) with hy02010 | hy02010
        · have hs020100 : InSquare (-11/32) (-31/160) (1/160) tau := by
            convert childLL hs02010 hx02010 hy02010 using 1 <;> norm_num
          exact Batch0060.cell0486.sound htau (by
            simp only [Batch0060.cell0486, Batch0060.tau0486, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020100 (by positivity) using 1 <;> norm_num)
        · have hs020102 : InSquare (-11/32) (-29/160) (1/160) tau := by
            convert childUL hs02010 hx02010 hy02010 using 1 <;> norm_num
          exact Batch0061.cell0488.sound htau (by
            simp only [Batch0061.cell0488, Batch0061.tau0488, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy02010 | hy02010
        · have hs020101 : InSquare (-53/160) (-31/160) (1/160) tau := by
            convert childLR hs02010 hx02010 hy02010 using 1 <;> norm_num
          exact Batch0060.cell0487.sound htau (by
            simp only [Batch0060.cell0487, Batch0060.tau0487, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020101 (by positivity) using 1 <;> norm_num)
        · have hs020103 : InSquare (-53/160) (-29/160) (1/160) tau := by
            convert childUR hs02010 hx02010 hy02010 using 1 <;> norm_num
          exact Batch0061.cell0489.sound htau (by
            simp only [Batch0061.cell0489, Batch0061.tau0489, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020103 (by positivity) using 1 <;> norm_num)
    · have hs02012 : InSquare (-27/80) (-13/80) (1/80) tau := by
        convert childUL hs hx0201 hy0201 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx02012 | hx02012
      · rcases le_total tau.im (-13/80 : ℝ) with hy02012 | hy02012
        · have hs020120 : InSquare (-11/32) (-27/160) (1/160) tau := by
            convert childLL hs02012 hx02012 hy02012 using 1 <;> norm_num
          exact Batch0061.cell0494.sound htau (by
            simp only [Batch0061.cell0494, Batch0061.tau0494, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020120 (by positivity) using 1 <;> norm_num)
        · have hs020122 : InSquare (-11/32) (-5/32) (1/160) tau := by
            convert childUL hs02012 hx02012 hy02012 using 1 <;> norm_num
          exact Batch0062.cell0496.sound htau (by
            simp only [Batch0062.cell0496, Batch0062.tau0496, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy02012 | hy02012
        · have hs020121 : InSquare (-53/160) (-27/160) (1/160) tau := by
            convert childLR hs02012 hx02012 hy02012 using 1 <;> norm_num
          exact Batch0061.cell0495.sound htau (by
            simp only [Batch0061.cell0495, Batch0061.tau0495, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020121 (by positivity) using 1 <;> norm_num)
        · have hs020123 : InSquare (-53/160) (-5/32) (1/160) tau := by
            convert childUR hs02012 hx02012 hy02012 using 1 <;> norm_num
          exact Batch0062.cell0497.sound htau (by
            simp only [Batch0062.cell0497, Batch0062.tau0497, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy0201 | hy0201
    · have hs02011 : InSquare (-5/16) (-3/16) (1/80) tau := by
        convert childLR hs hx0201 hy0201 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx02011 | hx02011
      · rcases le_total tau.im (-3/16 : ℝ) with hy02011 | hy02011
        · have hs020110 : InSquare (-51/160) (-31/160) (1/160) tau := by
            convert childLL hs02011 hx02011 hy02011 using 1 <;> norm_num
          exact Batch0061.cell0490.sound htau (by
            simp only [Batch0061.cell0490, Batch0061.tau0490, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020110 (by positivity) using 1 <;> norm_num)
        · have hs020112 : InSquare (-51/160) (-29/160) (1/160) tau := by
            convert childUL hs02011 hx02011 hy02011 using 1 <;> norm_num
          exact Batch0061.cell0492.sound htau (by
            simp only [Batch0061.cell0492, Batch0061.tau0492, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy02011 | hy02011
        · have hs020111 : InSquare (-49/160) (-31/160) (1/160) tau := by
            convert childLR hs02011 hx02011 hy02011 using 1 <;> norm_num
          exact Batch0061.cell0491.sound htau (by
            simp only [Batch0061.cell0491, Batch0061.tau0491, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020111 (by positivity) using 1 <;> norm_num)
        · have hs020113 : InSquare (-49/160) (-29/160) (1/160) tau := by
            convert childUR hs02011 hx02011 hy02011 using 1 <;> norm_num
          exact Batch0061.cell0493.sound htau (by
            simp only [Batch0061.cell0493, Batch0061.tau0493, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020113 (by positivity) using 1 <;> norm_num)
    · have hs02013 : InSquare (-5/16) (-13/80) (1/80) tau := by
        convert childUR hs hx0201 hy0201 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx02013 | hx02013
      · rcases le_total tau.im (-13/80 : ℝ) with hy02013 | hy02013
        · have hs020130 : InSquare (-51/160) (-27/160) (1/160) tau := by
            convert childLL hs02013 hx02013 hy02013 using 1 <;> norm_num
          exact Batch0062.cell0498.sound htau (by
            simp only [Batch0062.cell0498, Batch0062.tau0498, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020130 (by positivity) using 1 <;> norm_num)
        · have hs020132 : InSquare (-51/160) (-5/32) (1/160) tau := by
            convert childUL hs02013 hx02013 hy02013 using 1 <;> norm_num
          exact Batch0062.cell0500.sound htau (by
            simp only [Batch0062.cell0500, Batch0062.tau0500, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy02013 | hy02013
        · have hs020131 : InSquare (-49/160) (-27/160) (1/160) tau := by
            convert childLR hs02013 hx02013 hy02013 using 1 <;> norm_num
          exact Batch0062.cell0499.sound htau (by
            simp only [Batch0062.cell0499, Batch0062.tau0499, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020131 (by positivity) using 1 <;> norm_num)
        · have hs020133 : InSquare (-49/160) (-5/32) (1/160) tau := by
            convert childUR hs02013 hx02013 hy02013 using 1 <;> norm_num
          exact Batch0062.cell0501.sound htau (by
            simp only [Batch0062.cell0501, Batch0062.tau0501, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0201

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0202 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0202

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_020200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (-23/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (11/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_020202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (-21/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (1/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_020220 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (-19/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (9/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_020222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (-17/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (1/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/8 : ℝ) with hx0202 | hx0202
  · rcases le_total tau.im (-1/8 : ℝ) with hy0202 | hy0202
    · have hs02020 : InSquare (-31/80) (-11/80) (1/80) tau := by
        convert childLL hs hx0202 hy0202 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx02020 | hx02020
      · rcases le_total tau.im (-11/80 : ℝ) with hy02020 | hy02020
        · have hs020200 : InSquare (-63/160) (-23/160) (1/160) tau := by
            convert childLL hs02020 hx02020 hy02020 using 1 <;> norm_num
          exact (outside_020200 htau hs020200).elim
        · have hs020202 : InSquare (-63/160) (-21/160) (1/160) tau := by
            convert childUL hs02020 hx02020 hy02020 using 1 <;> norm_num
          exact (outside_020202 htau hs020202).elim
      · rcases le_total tau.im (-11/80 : ℝ) with hy02020 | hy02020
        · have hs020201 : InSquare (-61/160) (-23/160) (1/160) tau := by
            convert childLR hs02020 hx02020 hy02020 using 1 <;> norm_num
          exact Batch0062.cell0502.sound htau (by
            simp only [Batch0062.cell0502, Batch0062.tau0502, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020201 (by positivity) using 1 <;> norm_num)
        · have hs020203 : InSquare (-61/160) (-21/160) (1/160) tau := by
            convert childUR hs02020 hx02020 hy02020 using 1 <;> norm_num
          exact Batch0062.cell0503.sound htau (by
            simp only [Batch0062.cell0503, Batch0062.tau0503, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020203 (by positivity) using 1 <;> norm_num)
    · have hs02022 : InSquare (-31/80) (-9/80) (1/80) tau := by
        convert childUL hs hx0202 hy0202 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx02022 | hx02022
      · rcases le_total tau.im (-9/80 : ℝ) with hy02022 | hy02022
        · have hs020220 : InSquare (-63/160) (-19/160) (1/160) tau := by
            convert childLL hs02022 hx02022 hy02022 using 1 <;> norm_num
          exact (outside_020220 htau hs020220).elim
        · have hs020222 : InSquare (-63/160) (-17/160) (1/160) tau := by
            convert childUL hs02022 hx02022 hy02022 using 1 <;> norm_num
          exact (outside_020222 htau hs020222).elim
      · rcases le_total tau.im (-9/80 : ℝ) with hy02022 | hy02022
        · have hs020221 : InSquare (-61/160) (-19/160) (1/160) tau := by
            convert childLR hs02022 hx02022 hy02022 using 1 <;> norm_num
          exact Batch0063.cell0508.sound htau (by
            simp only [Batch0063.cell0508, Batch0063.tau0508, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020221 (by positivity) using 1 <;> norm_num)
        · have hs020223 : InSquare (-61/160) (-17/160) (1/160) tau := by
            convert childUR hs02022 hx02022 hy02022 using 1 <;> norm_num
          exact Batch0063.cell0509.sound htau (by
            simp only [Batch0063.cell0509, Batch0063.tau0509, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy0202 | hy0202
    · have hs02021 : InSquare (-29/80) (-11/80) (1/80) tau := by
        convert childLR hs hx0202 hy0202 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx02021 | hx02021
      · rcases le_total tau.im (-11/80 : ℝ) with hy02021 | hy02021
        · have hs020210 : InSquare (-59/160) (-23/160) (1/160) tau := by
            convert childLL hs02021 hx02021 hy02021 using 1 <;> norm_num
          exact Batch0063.cell0504.sound htau (by
            simp only [Batch0063.cell0504, Batch0063.tau0504, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020210 (by positivity) using 1 <;> norm_num)
        · have hs020212 : InSquare (-59/160) (-21/160) (1/160) tau := by
            convert childUL hs02021 hx02021 hy02021 using 1 <;> norm_num
          exact Batch0063.cell0506.sound htau (by
            simp only [Batch0063.cell0506, Batch0063.tau0506, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-11/80 : ℝ) with hy02021 | hy02021
        · have hs020211 : InSquare (-57/160) (-23/160) (1/160) tau := by
            convert childLR hs02021 hx02021 hy02021 using 1 <;> norm_num
          exact Batch0063.cell0505.sound htau (by
            simp only [Batch0063.cell0505, Batch0063.tau0505, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020211 (by positivity) using 1 <;> norm_num)
        · have hs020213 : InSquare (-57/160) (-21/160) (1/160) tau := by
            convert childUR hs02021 hx02021 hy02021 using 1 <;> norm_num
          exact Batch0063.cell0507.sound htau (by
            simp only [Batch0063.cell0507, Batch0063.tau0507, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020213 (by positivity) using 1 <;> norm_num)
    · have hs02023 : InSquare (-29/80) (-9/80) (1/80) tau := by
        convert childUR hs hx0202 hy0202 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx02023 | hx02023
      · rcases le_total tau.im (-9/80 : ℝ) with hy02023 | hy02023
        · have hs020230 : InSquare (-59/160) (-19/160) (1/160) tau := by
            convert childLL hs02023 hx02023 hy02023 using 1 <;> norm_num
          exact Batch0063.cell0510.sound htau (by
            simp only [Batch0063.cell0510, Batch0063.tau0510, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020230 (by positivity) using 1 <;> norm_num)
        · have hs020232 : InSquare (-59/160) (-17/160) (1/160) tau := by
            convert childUL hs02023 hx02023 hy02023 using 1 <;> norm_num
          exact Batch0064.cell0512.sound htau (by
            simp only [Batch0064.cell0512, Batch0064.tau0512, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-9/80 : ℝ) with hy02023 | hy02023
        · have hs020231 : InSquare (-57/160) (-19/160) (1/160) tau := by
            convert childLR hs02023 hx02023 hy02023 using 1 <;> norm_num
          exact Batch0063.cell0511.sound htau (by
            simp only [Batch0063.cell0511, Batch0063.tau0511, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020231 (by positivity) using 1 <;> norm_num)
        · have hs020233 : InSquare (-57/160) (-17/160) (1/160) tau := by
            convert childUR hs02023 hx02023 hy02023 using 1 <;> norm_num
          exact Batch0064.cell0513.sound htau (by
            simp only [Batch0064.cell0513, Batch0064.tau0513, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0202

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0203 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0203

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx0203 | hx0203
  · rcases le_total tau.im (-1/8 : ℝ) with hy0203 | hy0203
    · have hs02030 : InSquare (-27/80) (-11/80) (1/80) tau := by
        convert childLL hs hx0203 hy0203 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx02030 | hx02030
      · rcases le_total tau.im (-11/80 : ℝ) with hy02030 | hy02030
        · have hs020300 : InSquare (-11/32) (-23/160) (1/160) tau := by
            convert childLL hs02030 hx02030 hy02030 using 1 <;> norm_num
          exact Batch0064.cell0514.sound htau (by
            simp only [Batch0064.cell0514, Batch0064.tau0514, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020300 (by positivity) using 1 <;> norm_num)
        · have hs020302 : InSquare (-11/32) (-21/160) (1/160) tau := by
            convert childUL hs02030 hx02030 hy02030 using 1 <;> norm_num
          exact Batch0064.cell0516.sound htau (by
            simp only [Batch0064.cell0516, Batch0064.tau0516, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-11/80 : ℝ) with hy02030 | hy02030
        · have hs020301 : InSquare (-53/160) (-23/160) (1/160) tau := by
            convert childLR hs02030 hx02030 hy02030 using 1 <;> norm_num
          exact Batch0064.cell0515.sound htau (by
            simp only [Batch0064.cell0515, Batch0064.tau0515, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020301 (by positivity) using 1 <;> norm_num)
        · have hs020303 : InSquare (-53/160) (-21/160) (1/160) tau := by
            convert childUR hs02030 hx02030 hy02030 using 1 <;> norm_num
          exact Batch0064.cell0517.sound htau (by
            simp only [Batch0064.cell0517, Batch0064.tau0517, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020303 (by positivity) using 1 <;> norm_num)
    · have hs02032 : InSquare (-27/80) (-9/80) (1/80) tau := by
        convert childUL hs hx0203 hy0203 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx02032 | hx02032
      · rcases le_total tau.im (-9/80 : ℝ) with hy02032 | hy02032
        · have hs020320 : InSquare (-11/32) (-19/160) (1/160) tau := by
            convert childLL hs02032 hx02032 hy02032 using 1 <;> norm_num
          exact Batch0065.cell0522.sound htau (by
            simp only [Batch0065.cell0522, Batch0065.tau0522, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020320 (by positivity) using 1 <;> norm_num)
        · have hs020322 : InSquare (-11/32) (-17/160) (1/160) tau := by
            convert childUL hs02032 hx02032 hy02032 using 1 <;> norm_num
          exact Batch0065.cell0524.sound htau (by
            simp only [Batch0065.cell0524, Batch0065.tau0524, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-9/80 : ℝ) with hy02032 | hy02032
        · have hs020321 : InSquare (-53/160) (-19/160) (1/160) tau := by
            convert childLR hs02032 hx02032 hy02032 using 1 <;> norm_num
          exact Batch0065.cell0523.sound htau (by
            simp only [Batch0065.cell0523, Batch0065.tau0523, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020321 (by positivity) using 1 <;> norm_num)
        · have hs020323 : InSquare (-53/160) (-17/160) (1/160) tau := by
            convert childUR hs02032 hx02032 hy02032 using 1 <;> norm_num
          exact Batch0065.cell0525.sound htau (by
            simp only [Batch0065.cell0525, Batch0065.tau0525, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy0203 | hy0203
    · have hs02031 : InSquare (-5/16) (-11/80) (1/80) tau := by
        convert childLR hs hx0203 hy0203 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx02031 | hx02031
      · rcases le_total tau.im (-11/80 : ℝ) with hy02031 | hy02031
        · have hs020310 : InSquare (-51/160) (-23/160) (1/160) tau := by
            convert childLL hs02031 hx02031 hy02031 using 1 <;> norm_num
          exact Batch0064.cell0518.sound htau (by
            simp only [Batch0064.cell0518, Batch0064.tau0518, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020310 (by positivity) using 1 <;> norm_num)
        · have hs020312 : InSquare (-51/160) (-21/160) (1/160) tau := by
            convert childUL hs02031 hx02031 hy02031 using 1 <;> norm_num
          exact Batch0065.cell0520.sound htau (by
            simp only [Batch0065.cell0520, Batch0065.tau0520, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-11/80 : ℝ) with hy02031 | hy02031
        · have hs020311 : InSquare (-49/160) (-23/160) (1/160) tau := by
            convert childLR hs02031 hx02031 hy02031 using 1 <;> norm_num
          exact Batch0064.cell0519.sound htau (by
            simp only [Batch0064.cell0519, Batch0064.tau0519, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020311 (by positivity) using 1 <;> norm_num)
        · have hs020313 : InSquare (-49/160) (-21/160) (1/160) tau := by
            convert childUR hs02031 hx02031 hy02031 using 1 <;> norm_num
          exact Batch0065.cell0521.sound htau (by
            simp only [Batch0065.cell0521, Batch0065.tau0521, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020313 (by positivity) using 1 <;> norm_num)
    · have hs02033 : InSquare (-5/16) (-9/80) (1/80) tau := by
        convert childUR hs hx0203 hy0203 using 1 <;> norm_num
      exact Batch0009.cell0072.sound htau (by
        simp only [Batch0009.cell0072, Batch0009.tau0072, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0203

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0210 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0210

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx0210 | hx0210
  · rcases le_total tau.im (-7/40 : ℝ) with hy0210 | hy0210
    · have hs02100 : InSquare (-23/80) (-3/16) (1/80) tau := by
        convert childLL hs hx0210 hy0210 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx02100 | hx02100
      · rcases le_total tau.im (-3/16 : ℝ) with hy02100 | hy02100
        · have hs021000 : InSquare (-47/160) (-31/160) (1/160) tau := by
            convert childLL hs02100 hx02100 hy02100 using 1 <;> norm_num
          exact Batch0065.cell0526.sound htau (by
            simp only [Batch0065.cell0526, Batch0065.tau0526, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021000 (by positivity) using 1 <;> norm_num)
        · have hs021002 : InSquare (-47/160) (-29/160) (1/160) tau := by
            convert childUL hs02100 hx02100 hy02100 using 1 <;> norm_num
          exact Batch0066.cell0528.sound htau (by
            simp only [Batch0066.cell0528, Batch0066.tau0528, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy02100 | hy02100
        · have hs021001 : InSquare (-9/32) (-31/160) (1/160) tau := by
            convert childLR hs02100 hx02100 hy02100 using 1 <;> norm_num
          exact Batch0065.cell0527.sound htau (by
            simp only [Batch0065.cell0527, Batch0065.tau0527, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021001 (by positivity) using 1 <;> norm_num)
        · have hs021003 : InSquare (-9/32) (-29/160) (1/160) tau := by
            convert childUR hs02100 hx02100 hy02100 using 1 <;> norm_num
          exact Batch0066.cell0529.sound htau (by
            simp only [Batch0066.cell0529, Batch0066.tau0529, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021003 (by positivity) using 1 <;> norm_num)
    · have hs02102 : InSquare (-23/80) (-13/80) (1/80) tau := by
        convert childUL hs hx0210 hy0210 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx02102 | hx02102
      · rcases le_total tau.im (-13/80 : ℝ) with hy02102 | hy02102
        · have hs021020 : InSquare (-47/160) (-27/160) (1/160) tau := by
            convert childLL hs02102 hx02102 hy02102 using 1 <;> norm_num
          exact Batch0066.cell0534.sound htau (by
            simp only [Batch0066.cell0534, Batch0066.tau0534, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021020 (by positivity) using 1 <;> norm_num)
        · have hs021022 : InSquare (-47/160) (-5/32) (1/160) tau := by
            convert childUL hs02102 hx02102 hy02102 using 1 <;> norm_num
          exact Batch0067.cell0536.sound htau (by
            simp only [Batch0067.cell0536, Batch0067.tau0536, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy02102 | hy02102
        · have hs021021 : InSquare (-9/32) (-27/160) (1/160) tau := by
            convert childLR hs02102 hx02102 hy02102 using 1 <;> norm_num
          exact Batch0066.cell0535.sound htau (by
            simp only [Batch0066.cell0535, Batch0066.tau0535, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021021 (by positivity) using 1 <;> norm_num)
        · have hs021023 : InSquare (-9/32) (-5/32) (1/160) tau := by
            convert childUR hs02102 hx02102 hy02102 using 1 <;> norm_num
          exact Batch0067.cell0537.sound htau (by
            simp only [Batch0067.cell0537, Batch0067.tau0537, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy0210 | hy0210
    · have hs02101 : InSquare (-21/80) (-3/16) (1/80) tau := by
        convert childLR hs hx0210 hy0210 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx02101 | hx02101
      · rcases le_total tau.im (-3/16 : ℝ) with hy02101 | hy02101
        · have hs021010 : InSquare (-43/160) (-31/160) (1/160) tau := by
            convert childLL hs02101 hx02101 hy02101 using 1 <;> norm_num
          exact Batch0066.cell0530.sound htau (by
            simp only [Batch0066.cell0530, Batch0066.tau0530, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021010 (by positivity) using 1 <;> norm_num)
        · have hs021012 : InSquare (-43/160) (-29/160) (1/160) tau := by
            convert childUL hs02101 hx02101 hy02101 using 1 <;> norm_num
          exact Batch0066.cell0532.sound htau (by
            simp only [Batch0066.cell0532, Batch0066.tau0532, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy02101 | hy02101
        · have hs021011 : InSquare (-41/160) (-31/160) (1/160) tau := by
            convert childLR hs02101 hx02101 hy02101 using 1 <;> norm_num
          exact Batch0066.cell0531.sound htau (by
            simp only [Batch0066.cell0531, Batch0066.tau0531, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021011 (by positivity) using 1 <;> norm_num)
        · have hs021013 : InSquare (-41/160) (-29/160) (1/160) tau := by
            convert childUR hs02101 hx02101 hy02101 using 1 <;> norm_num
          exact Batch0066.cell0533.sound htau (by
            simp only [Batch0066.cell0533, Batch0066.tau0533, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021013 (by positivity) using 1 <;> norm_num)
    · have hs02103 : InSquare (-21/80) (-13/80) (1/80) tau := by
        convert childUR hs hx0210 hy0210 using 1 <;> norm_num
      exact Batch0009.cell0073.sound htau (by
        simp only [Batch0009.cell0073, Batch0009.tau0073, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02103 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0210

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0211 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0211

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx0211 | hx0211
  · rcases le_total tau.im (-7/40 : ℝ) with hy0211 | hy0211
    · have hs02110 : InSquare (-19/80) (-3/16) (1/80) tau := by
        convert childLL hs hx0211 hy0211 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx02110 | hx02110
      · rcases le_total tau.im (-3/16 : ℝ) with hy02110 | hy02110
        · have hs021100 : InSquare (-39/160) (-31/160) (1/160) tau := by
            convert childLL hs02110 hx02110 hy02110 using 1 <;> norm_num
          exact Batch0067.cell0538.sound htau (by
            simp only [Batch0067.cell0538, Batch0067.tau0538, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021100 (by positivity) using 1 <;> norm_num)
        · have hs021102 : InSquare (-39/160) (-29/160) (1/160) tau := by
            convert childUL hs02110 hx02110 hy02110 using 1 <;> norm_num
          exact Batch0067.cell0540.sound htau (by
            simp only [Batch0067.cell0540, Batch0067.tau0540, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy02110 | hy02110
        · have hs021101 : InSquare (-37/160) (-31/160) (1/160) tau := by
            convert childLR hs02110 hx02110 hy02110 using 1 <;> norm_num
          exact Batch0067.cell0539.sound htau (by
            simp only [Batch0067.cell0539, Batch0067.tau0539, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021101 (by positivity) using 1 <;> norm_num)
        · have hs021103 : InSquare (-37/160) (-29/160) (1/160) tau := by
            convert childUR hs02110 hx02110 hy02110 using 1 <;> norm_num
          exact Batch0067.cell0541.sound htau (by
            simp only [Batch0067.cell0541, Batch0067.tau0541, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021103 (by positivity) using 1 <;> norm_num)
    · have hs02112 : InSquare (-19/80) (-13/80) (1/80) tau := by
        convert childUL hs hx0211 hy0211 using 1 <;> norm_num
      exact Batch0009.cell0075.sound htau (by
        simp only [Batch0009.cell0075, Batch0009.tau0075, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02112 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy0211 | hy0211
    · have hs02111 : InSquare (-17/80) (-3/16) (1/80) tau := by
        convert childLR hs hx0211 hy0211 using 1 <;> norm_num
      exact Batch0009.cell0074.sound htau (by
        simp only [Batch0009.cell0074, Batch0009.tau0074, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02111 (by positivity) using 1 <;> norm_num)
    · have hs02113 : InSquare (-17/80) (-13/80) (1/80) tau := by
        convert childUR hs hx0211 hy0211 using 1 <;> norm_num
      exact Batch0009.cell0076.sound htau (by
        simp only [Batch0009.cell0076, Batch0009.tau0076, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02113 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0211

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0212 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0212

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx0212 | hx0212
  · rcases le_total tau.im (-1/8 : ℝ) with hy0212 | hy0212
    · have hs02120 : InSquare (-23/80) (-11/80) (1/80) tau := by
        convert childLL hs hx0212 hy0212 using 1 <;> norm_num
      exact Batch0009.cell0077.sound htau (by
        simp only [Batch0009.cell0077, Batch0009.tau0077, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02120 (by positivity) using 1 <;> norm_num)
    · have hs02122 : InSquare (-23/80) (-9/80) (1/80) tau := by
        convert childUL hs hx0212 hy0212 using 1 <;> norm_num
      exact Batch0009.cell0079.sound htau (by
        simp only [Batch0009.cell0079, Batch0009.tau0079, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02122 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy0212 | hy0212
    · have hs02121 : InSquare (-21/80) (-11/80) (1/80) tau := by
        convert childLR hs hx0212 hy0212 using 1 <;> norm_num
      exact Batch0009.cell0078.sound htau (by
        simp only [Batch0009.cell0078, Batch0009.tau0078, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02121 (by positivity) using 1 <;> norm_num)
    · have hs02123 : InSquare (-21/80) (-9/80) (1/80) tau := by
        convert childUR hs hx0212 hy0212 using 1 <;> norm_num
      exact Batch0010.cell0080.sound htau (by
        simp only [Batch0010.cell0080, Batch0010.tau0080, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02123 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0212

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0213 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0213

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx0213 | hx0213
  · rcases le_total tau.im (-1/8 : ℝ) with hy0213 | hy0213
    · have hs02130 : InSquare (-19/80) (-11/80) (1/80) tau := by
        convert childLL hs hx0213 hy0213 using 1 <;> norm_num
      exact Batch0010.cell0081.sound htau (by
        simp only [Batch0010.cell0081, Batch0010.tau0081, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02130 (by positivity) using 1 <;> norm_num)
    · have hs02132 : InSquare (-19/80) (-9/80) (1/80) tau := by
        convert childUL hs hx0213 hy0213 using 1 <;> norm_num
      exact Batch0010.cell0083.sound htau (by
        simp only [Batch0010.cell0083, Batch0010.tau0083, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02132 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy0213 | hy0213
    · have hs02131 : InSquare (-17/80) (-11/80) (1/80) tau := by
        convert childLR hs hx0213 hy0213 using 1 <;> norm_num
      exact Batch0010.cell0082.sound htau (by
        simp only [Batch0010.cell0082, Batch0010.tau0082, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02131 (by positivity) using 1 <;> norm_num)
    · have hs02133 : InSquare (-17/80) (-9/80) (1/80) tau := by
        convert childUR hs hx0213 hy0213 using 1 <;> norm_num
      exact Batch0010.cell0084.sound htau (by
        simp only [Batch0010.cell0084, Batch0010.tau0084, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0213

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0220 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0220

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (-3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/8 : ℝ) with hx0220 | hx0220
  · rcases le_total tau.im (-3/40 : ℝ) with hy0220 | hy0220
    · have hs02200 : InSquare (-31/80) (-7/80) (1/80) tau := by
        convert childLL hs hx0220 hy0220 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx02200 | hx02200
      · rcases le_total tau.im (-7/80 : ℝ) with hy02200 | hy02200
        · have hs022000 : InSquare (-63/160) (-3/32) (1/160) tau := by
            convert childLL hs02200 hx02200 hy02200 using 1 <;> norm_num
          exact Batch0067.cell0542.sound htau (by
            simp only [Batch0067.cell0542, Batch0067.tau0542, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022000 (by positivity) using 1 <;> norm_num)
        · have hs022002 : InSquare (-63/160) (-13/160) (1/160) tau := by
            convert childUL hs02200 hx02200 hy02200 using 1 <;> norm_num
          exact Batch0068.cell0544.sound htau (by
            simp only [Batch0068.cell0544, Batch0068.tau0544, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-7/80 : ℝ) with hy02200 | hy02200
        · have hs022001 : InSquare (-61/160) (-3/32) (1/160) tau := by
            convert childLR hs02200 hx02200 hy02200 using 1 <;> norm_num
          exact Batch0067.cell0543.sound htau (by
            simp only [Batch0067.cell0543, Batch0067.tau0543, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022001 (by positivity) using 1 <;> norm_num)
        · have hs022003 : InSquare (-61/160) (-13/160) (1/160) tau := by
            convert childUR hs02200 hx02200 hy02200 using 1 <;> norm_num
          exact Batch0068.cell0545.sound htau (by
            simp only [Batch0068.cell0545, Batch0068.tau0545, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022003 (by positivity) using 1 <;> norm_num)
    · have hs02202 : InSquare (-31/80) (-1/16) (1/80) tau := by
        convert childUL hs hx0220 hy0220 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx02202 | hx02202
      · rcases le_total tau.im (-1/16 : ℝ) with hy02202 | hy02202
        · have hs022020 : InSquare (-63/160) (-11/160) (1/160) tau := by
            convert childLL hs02202 hx02202 hy02202 using 1 <;> norm_num
          exact Batch0068.cell0550.sound htau (by
            simp only [Batch0068.cell0550, Batch0068.tau0550, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022020 (by positivity) using 1 <;> norm_num)
        · have hs022022 : InSquare (-63/160) (-9/160) (1/160) tau := by
            convert childUL hs02202 hx02202 hy02202 using 1 <;> norm_num
          exact Batch0069.cell0552.sound htau (by
            simp only [Batch0069.cell0552, Batch0069.tau0552, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-1/16 : ℝ) with hy02202 | hy02202
        · have hs022021 : InSquare (-61/160) (-11/160) (1/160) tau := by
            convert childLR hs02202 hx02202 hy02202 using 1 <;> norm_num
          exact Batch0068.cell0551.sound htau (by
            simp only [Batch0068.cell0551, Batch0068.tau0551, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022021 (by positivity) using 1 <;> norm_num)
        · have hs022023 : InSquare (-61/160) (-9/160) (1/160) tau := by
            convert childUR hs02202 hx02202 hy02202 using 1 <;> norm_num
          exact Batch0069.cell0553.sound htau (by
            simp only [Batch0069.cell0553, Batch0069.tau0553, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/40 : ℝ) with hy0220 | hy0220
    · have hs02201 : InSquare (-29/80) (-7/80) (1/80) tau := by
        convert childLR hs hx0220 hy0220 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx02201 | hx02201
      · rcases le_total tau.im (-7/80 : ℝ) with hy02201 | hy02201
        · have hs022010 : InSquare (-59/160) (-3/32) (1/160) tau := by
            convert childLL hs02201 hx02201 hy02201 using 1 <;> norm_num
          exact Batch0068.cell0546.sound htau (by
            simp only [Batch0068.cell0546, Batch0068.tau0546, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022010 (by positivity) using 1 <;> norm_num)
        · have hs022012 : InSquare (-59/160) (-13/160) (1/160) tau := by
            convert childUL hs02201 hx02201 hy02201 using 1 <;> norm_num
          exact Batch0068.cell0548.sound htau (by
            simp only [Batch0068.cell0548, Batch0068.tau0548, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-7/80 : ℝ) with hy02201 | hy02201
        · have hs022011 : InSquare (-57/160) (-3/32) (1/160) tau := by
            convert childLR hs02201 hx02201 hy02201 using 1 <;> norm_num
          exact Batch0068.cell0547.sound htau (by
            simp only [Batch0068.cell0547, Batch0068.tau0547, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022011 (by positivity) using 1 <;> norm_num)
        · have hs022013 : InSquare (-57/160) (-13/160) (1/160) tau := by
            convert childUR hs02201 hx02201 hy02201 using 1 <;> norm_num
          exact Batch0068.cell0549.sound htau (by
            simp only [Batch0068.cell0549, Batch0068.tau0549, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022013 (by positivity) using 1 <;> norm_num)
    · have hs02203 : InSquare (-29/80) (-1/16) (1/80) tau := by
        convert childUR hs hx0220 hy0220 using 1 <;> norm_num
      exact Batch0010.cell0085.sound htau (by
        simp only [Batch0010.cell0085, Batch0010.tau0085, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02203 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0220

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0221 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0221

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (-3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx0221 | hx0221
  · rcases le_total tau.im (-3/40 : ℝ) with hy0221 | hy0221
    · have hs02210 : InSquare (-27/80) (-7/80) (1/80) tau := by
        convert childLL hs hx0221 hy0221 using 1 <;> norm_num
      exact Batch0010.cell0086.sound htau (by
        simp only [Batch0010.cell0086, Batch0010.tau0086, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02210 (by positivity) using 1 <;> norm_num)
    · have hs02212 : InSquare (-27/80) (-1/16) (1/80) tau := by
        convert childUL hs hx0221 hy0221 using 1 <;> norm_num
      exact Batch0011.cell0088.sound htau (by
        simp only [Batch0011.cell0088, Batch0011.tau0088, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02212 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/40 : ℝ) with hy0221 | hy0221
    · have hs02211 : InSquare (-5/16) (-7/80) (1/80) tau := by
        convert childLR hs hx0221 hy0221 using 1 <;> norm_num
      exact Batch0010.cell0087.sound htau (by
        simp only [Batch0010.cell0087, Batch0010.tau0087, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02211 (by positivity) using 1 <;> norm_num)
    · have hs02213 : InSquare (-5/16) (-1/16) (1/80) tau := by
        convert childUR hs hx0221 hy0221 using 1 <;> norm_num
      exact Batch0011.cell0089.sound htau (by
        simp only [Batch0011.cell0089, Batch0011.tau0089, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02213 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0221

end


