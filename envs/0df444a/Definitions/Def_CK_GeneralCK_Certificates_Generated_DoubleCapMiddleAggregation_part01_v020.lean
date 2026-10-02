-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v020
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v020
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:11:21.755576+00:00
-- url     : https://prove2.me/theorems/355f567f-db36-4002-a8bb-ac6b02fd4806
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0169__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0174__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v020 (m : ℝ) (hL : 217/640 ≤ m) (hU : m ≤ 437/1280) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc160 : m ≤ 695/2048
  · exact Cell0170.accepted_cell m (by linarith [hL]) hc160
  ·
    by_cases hc161 : m ≤ 1739/5120
    · exact Cell0171.accepted_cell m (by linarith [(lt_of_not_ge hc160).le]) hc161
    ·
      by_cases hc162 : m ≤ 3481/10240
      · exact Cell0172.accepted_cell m (by linarith [(lt_of_not_ge hc161).le]) hc162
      ·
        by_cases hc163 : m ≤ 871/2560
        · exact Cell0173.accepted_cell m (by linarith [(lt_of_not_ge hc162).le]) hc163
        ·
          by_cases hc164 : m ≤ 3487/10240
          · exact Cell0174.accepted_cell m (by linarith [(lt_of_not_ge hc163).le]) hc164
          ·
            by_cases hc165 : m ≤ 349/1024
            · exact Cell0175.accepted_cell m (by linarith [(lt_of_not_ge hc164).le]) hc165
            ·
              by_cases hc166 : m ≤ 3493/10240
              · exact Cell0176.accepted_cell m (by linarith [(lt_of_not_ge hc165).le]) hc166
              ·
                exact Cell0177.accepted_cell m (by linarith [(lt_of_not_ge hc166).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


