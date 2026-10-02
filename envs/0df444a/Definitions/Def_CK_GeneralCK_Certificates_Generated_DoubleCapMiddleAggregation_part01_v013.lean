-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v013
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v013
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:42:55.880769+00:00
-- url     : https://prove2.me/theorems/bded4fa5-7fae-4ceb-bf29-b4293f62787e
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0113__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0120__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v013 (m : ℝ) (hL : 1589/5120 ≤ m) (hU : m ≤ 1613/5120) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc104 : m ≤ 199/640
  · exact Cell0114.accepted_cell m (by linarith [hL]) hc104
  ·
    by_cases hc105 : m ≤ 319/1024
    · exact Cell0115.accepted_cell m (by linarith [(lt_of_not_ge hc104).le]) hc105
    ·
      by_cases hc106 : m ≤ 799/2560
      · exact Cell0116.accepted_cell m (by linarith [(lt_of_not_ge hc105).le]) hc106
      ·
        by_cases hc107 : m ≤ 1601/5120
        · exact Cell0117.accepted_cell m (by linarith [(lt_of_not_ge hc106).le]) hc107
        ·
          by_cases hc108 : m ≤ 401/1280
          · exact Cell0118.accepted_cell m (by linarith [(lt_of_not_ge hc107).le]) hc108
          ·
            by_cases hc109 : m ≤ 1607/5120
            · exact Cell0119.accepted_cell m (by linarith [(lt_of_not_ge hc108).le]) hc109
            ·
              by_cases hc110 : m ≤ 161/512
              · exact Cell0120.accepted_cell m (by linarith [(lt_of_not_ge hc109).le]) hc110
              ·
                exact Cell0121.accepted_cell m (by linarith [(lt_of_not_ge hc110).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


