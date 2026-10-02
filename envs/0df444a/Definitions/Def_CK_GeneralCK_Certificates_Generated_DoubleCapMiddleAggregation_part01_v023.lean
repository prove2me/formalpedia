-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v023
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v023
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:45:59.857254+00:00
-- url     : https://prove2.me/theorems/ed93ced1-4d7f-4979-a620-f56428e39899
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0190__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0195__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0201__6
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v023 (m : ℝ) (hL : 443/1280 ≤ m) (hU : m ≤ 223/640) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc184 : m ≤ 3547/10240
  · exact Cell0194.accepted_cell m (by linarith [hL]) hc184
  ·
    by_cases hc185 : m ≤ 355/1024
    · exact Cell0195.accepted_cell m (by linarith [(lt_of_not_ge hc184).le]) hc185
    ·
      by_cases hc186 : m ≤ 3553/10240
      · exact Cell0196.accepted_cell m (by linarith [(lt_of_not_ge hc185).le]) hc186
      ·
        by_cases hc187 : m ≤ 889/2560
        · exact Cell0197.accepted_cell m (by linarith [(lt_of_not_ge hc186).le]) hc187
        ·
          by_cases hc188 : m ≤ 3559/10240
          · exact Cell0198.accepted_cell m (by linarith [(lt_of_not_ge hc187).le]) hc188
          ·
            by_cases hc189 : m ≤ 1781/5120
            · exact Cell0199.accepted_cell m (by linarith [(lt_of_not_ge hc188).le]) hc189
            ·
              by_cases hc190 : m ≤ 713/2048
              · exact Cell0200.accepted_cell m (by linarith [(lt_of_not_ge hc189).le]) hc190
              ·
                exact Cell0201.accepted_cell m (by linarith [(lt_of_not_ge hc190).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


