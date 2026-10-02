-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v004
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v004
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:14:57.533912+00:00
-- url     : https://prove2.me/theorems/cb2bec5e-3b42-4166-be9d-4ec4084b033b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation (proof segment of doubleCapHighResidual_middle)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation (proof segment of doubleCapHighResidual_middle)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation (proof segment of doubleCapHighResidual_middle)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation (proof segment of doubleCapHighResidual_middle) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddleAggregation (proof segment of doubleCapHighResidual_middle).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0041__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0046__6
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v004 (m : ℝ) (hL : 1373/5120 ≤ m) (hU : m ≤ 1397/5120) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc32 : m ≤ 43/160
  · exact Cell0042.accepted_cell m (by linarith [hL]) hc32
  ·
    by_cases hc33 : m ≤ 1379/5120
    · exact Cell0043.accepted_cell m (by linarith [(lt_of_not_ge hc32).le]) hc33
    ·
      by_cases hc34 : m ≤ 691/2560
      · exact Cell0044.accepted_cell m (by linarith [(lt_of_not_ge hc33).le]) hc34
      ·
        by_cases hc35 : m ≤ 277/1024
        · exact Cell0045.accepted_cell m (by linarith [(lt_of_not_ge hc34).le]) hc35
        ·
          by_cases hc36 : m ≤ 347/1280
          · exact Cell0046.accepted_cell m (by linarith [(lt_of_not_ge hc35).le]) hc36
          ·
            by_cases hc37 : m ≤ 1391/5120
            · exact Cell0047.accepted_cell m (by linarith [(lt_of_not_ge hc36).le]) hc37
            ·
              by_cases hc38 : m ≤ 697/2560
              · exact Cell0048.accepted_cell m (by linarith [(lt_of_not_ge hc37).le]) hc38
              ·
                exact Cell0049.accepted_cell m (by linarith [(lt_of_not_ge hc38).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


