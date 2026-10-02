-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v047
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v047
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:43:41.03003+00:00
-- url     : https://prove2.me/theorems/4fc40bf3-2bcd-40d8-8cf8-346542a2701a
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0386__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0391__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v047 (m : ℝ) (hL : 991/2560 ≤ m) (hU : m ≤ 497/1280) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc376 : m ≤ 7931/20480
  · exact Cell0386.accepted_cell m (by linarith [hL]) hc376
  ·
    by_cases hc377 : m ≤ 3967/10240
    · exact Cell0387.accepted_cell m (by linarith [(lt_of_not_ge hc376).le]) hc377
    ·
      by_cases hc378 : m ≤ 7937/20480
      · exact Cell0388.accepted_cell m (by linarith [(lt_of_not_ge hc377).le]) hc378
      ·
        by_cases hc379 : m ≤ 397/1024
        · exact Cell0389.accepted_cell m (by linarith [(lt_of_not_ge hc378).le]) hc379
        ·
          by_cases hc380 : m ≤ 7943/20480
          · exact Cell0390.accepted_cell m (by linarith [(lt_of_not_ge hc379).le]) hc380
          ·
            by_cases hc381 : m ≤ 3973/10240
            · exact Cell0391.accepted_cell m (by linarith [(lt_of_not_ge hc380).le]) hc381
            ·
              by_cases hc382 : m ≤ 7949/20480
              · exact Cell0392.accepted_cell m (by linarith [(lt_of_not_ge hc381).le]) hc382
              ·
                exact Cell0393.accepted_cell m (by linarith [(lt_of_not_ge hc382).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


