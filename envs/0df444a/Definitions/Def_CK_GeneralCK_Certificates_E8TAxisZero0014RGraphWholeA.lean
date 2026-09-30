-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0014RGraphWholeA
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0014RGraphWholeA
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T10:52:00.247801+00:00
-- url     : https://prove2.me/theorems/3bc2e825-35c1-48f5-80f3-dfa11cab55a7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0014RGraphWholeA` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0014RGraphWholeA` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0014RGraphWholeA` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0014RGraphWholeA (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0014RGraphWholeA.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularUnconditionalSource

-- ===== source module GeneralCK.Certificates.E8TAxisZero0014RGraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0014RGraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-11008532462562, 633147705915515795023331642470956594340716867⟩,
   ⟨126629467412457383891962325730825599082799199938, 126629688724481676249275652944676708236045099266⟩,
   ⟨-48443448447076028754, 88524896683991564691804152586044155267537223⟩,
   ⟨17704944549989160507950547738237037944793455675, 17705048910478437691815944333768101463291331460⟩,
   ⟨-139571805779583766986298350, 41744257530780406772375555176985441782474566⟩,
   ⟨8348826778198315973601393351082387052204886503, 8348900962101486169767782353446789003711585553⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0014RGraphWholeA

end


