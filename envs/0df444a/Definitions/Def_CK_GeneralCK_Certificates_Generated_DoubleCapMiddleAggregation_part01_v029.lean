-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v029
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v029
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T23:34:02.046302+00:00
-- url     : https://prove2.me/theorems/6b333832-bef9-45bb-8218-de91dc767b78
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0238__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0243__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0249__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v029 (m : ℝ) (hL : 461/1280 ≤ m) (hU : m ≤ 29/80) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc232 : m ≤ 3691/10240
  · exact Cell0242.accepted_cell m (by linarith [hL]) hc232
  ·
    by_cases hc233 : m ≤ 1847/5120
    · exact Cell0243.accepted_cell m (by linarith [(lt_of_not_ge hc232).le]) hc233
    ·
      by_cases hc234 : m ≤ 3697/10240
      · exact Cell0244.accepted_cell m (by linarith [(lt_of_not_ge hc233).le]) hc234
      ·
        by_cases hc235 : m ≤ 185/512
        · exact Cell0245.accepted_cell m (by linarith [(lt_of_not_ge hc234).le]) hc235
        ·
          by_cases hc236 : m ≤ 3703/10240
          · exact Cell0246.accepted_cell m (by linarith [(lt_of_not_ge hc235).le]) hc236
          ·
            by_cases hc237 : m ≤ 1853/5120
            · exact Cell0247.accepted_cell m (by linarith [(lt_of_not_ge hc236).le]) hc237
            ·
              by_cases hc238 : m ≤ 3709/10240
              · exact Cell0248.accepted_cell m (by linarith [(lt_of_not_ge hc237).le]) hc238
              ·
                exact Cell0249.accepted_cell m (by linarith [(lt_of_not_ge hc238).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


