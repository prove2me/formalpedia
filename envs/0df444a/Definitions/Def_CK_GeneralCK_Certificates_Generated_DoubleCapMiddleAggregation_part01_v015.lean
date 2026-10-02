-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v015
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v015
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:57:22.911688+00:00
-- url     : https://prove2.me/theorems/25acf3b0-70eb-48d7-ba69-0abc3765f0e8
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0129__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0134__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v015 (m : ℝ) (hL : 1637/5120 ≤ m) (hU : m ≤ 1661/5120) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc120 : m ≤ 41/128
  · exact Cell0130.accepted_cell m (by linarith [hL]) hc120
  ·
    by_cases hc121 : m ≤ 1643/5120
    · exact Cell0131.accepted_cell m (by linarith [(lt_of_not_ge hc120).le]) hc121
    ·
      by_cases hc122 : m ≤ 823/2560
      · exact Cell0132.accepted_cell m (by linarith [(lt_of_not_ge hc121).le]) hc122
      ·
        by_cases hc123 : m ≤ 1649/5120
        · exact Cell0133.accepted_cell m (by linarith [(lt_of_not_ge hc122).le]) hc123
        ·
          by_cases hc124 : m ≤ 413/1280
          · exact Cell0134.accepted_cell m (by linarith [(lt_of_not_ge hc123).le]) hc124
          ·
            by_cases hc125 : m ≤ 331/1024
            · exact Cell0135.accepted_cell m (by linarith [(lt_of_not_ge hc124).le]) hc125
            ·
              by_cases hc126 : m ≤ 829/2560
              · exact Cell0136.accepted_cell m (by linarith [(lt_of_not_ge hc125).le]) hc126
              ·
                exact Cell0137.accepted_cell m (by linarith [(lt_of_not_ge hc126).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


