-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v050
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v050
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:46:45.173987+00:00
-- url     : https://prove2.me/theorems/a7ca6ec0-536a-4fc9-bc4c-381634f85788
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0407__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0412__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0416__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v050 (m : ℝ) (hL : 25/64 ≤ m) (hU : m ≤ 1003/2560) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc400 : m ≤ 8003/20480
  · exact Cell0410.accepted_cell m (by linarith [hL]) hc400
  ·
    by_cases hc401 : m ≤ 4003/10240
    · exact Cell0411.accepted_cell m (by linarith [(lt_of_not_ge hc400).le]) hc401
    ·
      by_cases hc402 : m ≤ 8009/20480
      · exact Cell0412.accepted_cell m (by linarith [(lt_of_not_ge hc401).le]) hc402
      ·
        by_cases hc403 : m ≤ 2003/5120
        · exact Cell0413.accepted_cell m (by linarith [(lt_of_not_ge hc402).le]) hc403
        ·
          by_cases hc404 : m ≤ 1603/4096
          · exact Cell0414.accepted_cell m (by linarith [(lt_of_not_ge hc403).le]) hc404
          ·
            by_cases hc405 : m ≤ 4009/10240
            · exact Cell0415.accepted_cell m (by linarith [(lt_of_not_ge hc404).le]) hc405
            ·
              by_cases hc406 : m ≤ 8021/20480
              · exact Cell0416.accepted_cell m (by linarith [(lt_of_not_ge hc405).le]) hc406
              ·
                exact Cell0417.accepted_cell m (by linarith [(lt_of_not_ge hc406).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


