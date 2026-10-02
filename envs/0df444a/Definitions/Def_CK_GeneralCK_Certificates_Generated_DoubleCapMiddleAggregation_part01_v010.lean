-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v010
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v010
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:05:10.221751+00:00
-- url     : https://prove2.me/theorems/de920aa9-600d-4c0e-90dd-f1ef5369085c
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0088__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0092__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0097__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v010 (m : ℝ) (hL : 1517/5120 ≤ m) (hU : m ≤ 1541/5120) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc80 : m ≤ 19/64
  · exact Cell0090.accepted_cell m (by linarith [hL]) hc80
  ·
    by_cases hc81 : m ≤ 1523/5120
    · exact Cell0091.accepted_cell m (by linarith [(lt_of_not_ge hc80).le]) hc81
    ·
      by_cases hc82 : m ≤ 763/2560
      · exact Cell0092.accepted_cell m (by linarith [(lt_of_not_ge hc81).le]) hc82
      ·
        by_cases hc83 : m ≤ 1529/5120
        · exact Cell0093.accepted_cell m (by linarith [(lt_of_not_ge hc82).le]) hc83
        ·
          by_cases hc84 : m ≤ 383/1280
          · exact Cell0094.accepted_cell m (by linarith [(lt_of_not_ge hc83).le]) hc84
          ·
            by_cases hc85 : m ≤ 307/1024
            · exact Cell0095.accepted_cell m (by linarith [(lt_of_not_ge hc84).le]) hc85
            ·
              by_cases hc86 : m ≤ 769/2560
              · exact Cell0096.accepted_cell m (by linarith [(lt_of_not_ge hc85).le]) hc86
              ·
                exact Cell0097.accepted_cell m (by linarith [(lt_of_not_ge hc86).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


