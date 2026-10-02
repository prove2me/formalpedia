-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v032
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v032
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:30:50.309906+00:00
-- url     : https://prove2.me/theorems/dff59192-25f5-4628-9a0b-ec95bda98442
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0265__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0270__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v032 (m : ℝ) (hL : 47/128 ≤ m) (hU : m ≤ 473/1280) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc256 : m ≤ 3763/10240
  · exact Cell0266.accepted_cell m (by linarith [hL]) hc256
  ·
    by_cases hc257 : m ≤ 1883/5120
    · exact Cell0267.accepted_cell m (by linarith [(lt_of_not_ge hc256).le]) hc257
    ·
      by_cases hc258 : m ≤ 3769/10240
      · exact Cell0268.accepted_cell m (by linarith [(lt_of_not_ge hc257).le]) hc258
      ·
        by_cases hc259 : m ≤ 943/2560
        · exact Cell0269.accepted_cell m (by linarith [(lt_of_not_ge hc258).le]) hc259
        ·
          by_cases hc260 : m ≤ 755/2048
          · exact Cell0270.accepted_cell m (by linarith [(lt_of_not_ge hc259).le]) hc260
          ·
            by_cases hc261 : m ≤ 1889/5120
            · exact Cell0271.accepted_cell m (by linarith [(lt_of_not_ge hc260).le]) hc261
            ·
              by_cases hc262 : m ≤ 3781/10240
              · exact Cell0272.accepted_cell m (by linarith [(lt_of_not_ge hc261).le]) hc262
              ·
                exact Cell0273.accepted_cell m (by linarith [(lt_of_not_ge hc262).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


