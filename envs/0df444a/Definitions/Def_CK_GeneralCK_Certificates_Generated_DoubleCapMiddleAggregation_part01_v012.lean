-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v012
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v012
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:59:20.092273+00:00
-- url     : https://prove2.me/theorems/5f90da71-2562-4323-aeca-24714a10c465
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0102__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0107__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0113__7
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v012 (m : ℝ) (hL : 313/1024 ≤ m) (hU : m ≤ 1589/5120) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc96 : m ≤ 49/160
  · exact Cell0106.accepted_cell m (by linarith [hL]) hc96
  ·
    by_cases hc97 : m ≤ 1571/5120
    · exact Cell0107.accepted_cell m (by linarith [(lt_of_not_ge hc96).le]) hc97
    ·
      by_cases hc98 : m ≤ 787/2560
      · exact Cell0108.accepted_cell m (by linarith [(lt_of_not_ge hc97).le]) hc98
      ·
        by_cases hc99 : m ≤ 1577/5120
        · exact Cell0109.accepted_cell m (by linarith [(lt_of_not_ge hc98).le]) hc99
        ·
          by_cases hc100 : m ≤ 79/256
          · exact Cell0110.accepted_cell m (by linarith [(lt_of_not_ge hc99).le]) hc100
          ·
            by_cases hc101 : m ≤ 1583/5120
            · exact Cell0111.accepted_cell m (by linarith [(lt_of_not_ge hc100).le]) hc101
            ·
              by_cases hc102 : m ≤ 793/2560
              · exact Cell0112.accepted_cell m (by linarith [(lt_of_not_ge hc101).le]) hc102
              ·
                exact Cell0113.accepted_cell m (by linarith [(lt_of_not_ge hc102).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


