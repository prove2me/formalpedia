-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v021
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v021
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:52:20.56969+00:00
-- url     : https://prove2.me/theorems/338b30f9-2cff-4dac-983f-76e0ca88b081
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0174__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0179__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0184__6
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v021 (m : ℝ) (hL : 437/1280 ≤ m) (hU : m ≤ 11/32) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc168 : m ≤ 3499/10240
  · exact Cell0178.accepted_cell m (by linarith [hL]) hc168
  ·
    by_cases hc169 : m ≤ 1751/5120
    · exact Cell0179.accepted_cell m (by linarith [(lt_of_not_ge hc168).le]) hc169
    ·
      by_cases hc170 : m ≤ 701/2048
      · exact Cell0180.accepted_cell m (by linarith [(lt_of_not_ge hc169).le]) hc170
      ·
        by_cases hc171 : m ≤ 877/2560
        · exact Cell0181.accepted_cell m (by linarith [(lt_of_not_ge hc170).le]) hc171
        ·
          by_cases hc172 : m ≤ 3511/10240
          · exact Cell0182.accepted_cell m (by linarith [(lt_of_not_ge hc171).le]) hc172
          ·
            by_cases hc173 : m ≤ 1757/5120
            · exact Cell0183.accepted_cell m (by linarith [(lt_of_not_ge hc172).le]) hc173
            ·
              by_cases hc174 : m ≤ 3517/10240
              · exact Cell0184.accepted_cell m (by linarith [(lt_of_not_ge hc173).le]) hc174
              ·
                exact Cell0185.accepted_cell m (by linarith [(lt_of_not_ge hc174).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


