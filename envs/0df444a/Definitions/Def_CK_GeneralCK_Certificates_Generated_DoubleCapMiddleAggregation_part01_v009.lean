-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v009
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v009
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:14:12.625783+00:00
-- url     : https://prove2.me/theorems/c52ff492-4a40-466e-aa32-d04f27382775
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0077__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0083__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0088__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v009 (m : ℝ) (hL : 1493/5120 ≤ m) (hU : m ≤ 1517/5120) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc72 : m ≤ 187/640
  · exact Cell0082.accepted_cell m (by linarith [hL]) hc72
  ·
    by_cases hc73 : m ≤ 1499/5120
    · exact Cell0083.accepted_cell m (by linarith [(lt_of_not_ge hc72).le]) hc73
    ·
      by_cases hc74 : m ≤ 751/2560
      · exact Cell0084.accepted_cell m (by linarith [(lt_of_not_ge hc73).le]) hc74
      ·
        by_cases hc75 : m ≤ 301/1024
        · exact Cell0085.accepted_cell m (by linarith [(lt_of_not_ge hc74).le]) hc75
        ·
          by_cases hc76 : m ≤ 377/1280
          · exact Cell0086.accepted_cell m (by linarith [(lt_of_not_ge hc75).le]) hc76
          ·
            by_cases hc77 : m ≤ 1511/5120
            · exact Cell0087.accepted_cell m (by linarith [(lt_of_not_ge hc76).le]) hc77
            ·
              by_cases hc78 : m ≤ 757/2560
              · exact Cell0088.accepted_cell m (by linarith [(lt_of_not_ge hc77).le]) hc78
              ·
                exact Cell0089.accepted_cell m (by linarith [(lt_of_not_ge hc78).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


