-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v011
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v011
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:09:35.567071+00:00
-- url     : https://prove2.me/theorems/fc3a3487-b5c1-49cc-8e05-49f462410f94
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0097__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0102__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v011 (m : ℝ) (hL : 1541/5120 ≤ m) (hU : m ≤ 313/1024) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc88 : m ≤ 193/640
  · exact Cell0098.accepted_cell m (by linarith [hL]) hc88
  ·
    by_cases hc89 : m ≤ 1547/5120
    · exact Cell0099.accepted_cell m (by linarith [(lt_of_not_ge hc88).le]) hc89
    ·
      by_cases hc90 : m ≤ 155/512
      · exact Cell0100.accepted_cell m (by linarith [(lt_of_not_ge hc89).le]) hc90
      ·
        by_cases hc91 : m ≤ 1553/5120
        · exact Cell0101.accepted_cell m (by linarith [(lt_of_not_ge hc90).le]) hc91
        ·
          by_cases hc92 : m ≤ 389/1280
          · exact Cell0102.accepted_cell m (by linarith [(lt_of_not_ge hc91).le]) hc92
          ·
            by_cases hc93 : m ≤ 1559/5120
            · exact Cell0103.accepted_cell m (by linarith [(lt_of_not_ge hc92).le]) hc93
            ·
              by_cases hc94 : m ≤ 781/2560
              · exact Cell0104.accepted_cell m (by linarith [(lt_of_not_ge hc93).le]) hc94
              ·
                exact Cell0105.accepted_cell m (by linarith [(lt_of_not_ge hc94).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


