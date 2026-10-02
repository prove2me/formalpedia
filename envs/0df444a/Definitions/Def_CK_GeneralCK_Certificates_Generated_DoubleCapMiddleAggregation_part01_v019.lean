-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v019
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v019
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T23:18:14.450298+00:00
-- url     : https://prove2.me/theorems/1798c587-82f7-4034-a8b4-c28f215551c0
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0159__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0165__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0169__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v019 (m : ℝ) (hL : 431/1280 ≤ m) (hU : m ≤ 217/640) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc152 : m ≤ 3451/10240
  · exact Cell0162.accepted_cell m (by linarith [hL]) hc152
  ·
    by_cases hc153 : m ≤ 1727/5120
    · exact Cell0163.accepted_cell m (by linarith [(lt_of_not_ge hc152).le]) hc153
    ·
      by_cases hc154 : m ≤ 3457/10240
      · exact Cell0164.accepted_cell m (by linarith [(lt_of_not_ge hc153).le]) hc154
      ·
        by_cases hc155 : m ≤ 173/512
        · exact Cell0165.accepted_cell m (by linarith [(lt_of_not_ge hc154).le]) hc155
        ·
          by_cases hc156 : m ≤ 3463/10240
          · exact Cell0166.accepted_cell m (by linarith [(lt_of_not_ge hc155).le]) hc156
          ·
            by_cases hc157 : m ≤ 1733/5120
            · exact Cell0167.accepted_cell m (by linarith [(lt_of_not_ge hc156).le]) hc157
            ·
              by_cases hc158 : m ≤ 3469/10240
              · exact Cell0168.accepted_cell m (by linarith [(lt_of_not_ge hc157).le]) hc158
              ·
                exact Cell0169.accepted_cell m (by linarith [(lt_of_not_ge hc158).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


