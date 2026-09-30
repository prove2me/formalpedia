-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0014RGraphCenterA
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0014RGraphCenterA
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T10:31:33.013048+00:00
-- url     : https://prove2.me/theorems/a2596b61-0c7e-4155-a010-e8275dc9944a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0014RGraphCenterA` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0014RGraphCenterA` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0014RGraphCenterA` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0014RGraphCenterA (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0014RGraphCenterA.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularUnconditionalSource

-- ===== source module GeneralCK.Certificates.E8TAxisZero0014RGraphCenterA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0014RGraphCenterA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨316573714637776686286688825891685102881059728, 316573714637776686286688825891685102881073626⟩,
   ⟨126629522740422691195352252146003422400745393810, 126629522740422691195352252146003422400839723412⟩,
   ⟨44262383116714132504672510178574288184028508, 44262383116714132504672510178574891893262847⟩,
   ⟨17704970640082501731328311565699156571078398903, 17704970640082501731328311565702778826483456922⟩,
   ⟨20872082400462391839611010604646198615818455, 20872082400462391839611030889276466922065339⟩,
   ⟨8348845324160105020359873552895629693499602464, 8348845324160105020359979032973024885798041570⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0014RGraphCenterA

end


