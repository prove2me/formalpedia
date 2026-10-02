-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v031
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v031
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:44:23.7662+00:00
-- url     : https://prove2.me/theorems/e741d50f-1902-4604-8284-b9884eca9de6
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0253__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0259__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0265__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v031 (m : ℝ) (hL : 467/1280 ≤ m) (hU : m ≤ 47/128) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc248 : m ≤ 3739/10240
  · exact Cell0258.accepted_cell m (by linarith [hL]) hc248
  ·
    by_cases hc249 : m ≤ 1871/5120
    · exact Cell0259.accepted_cell m (by linarith [(lt_of_not_ge hc248).le]) hc249
    ·
      by_cases hc250 : m ≤ 749/2048
      · exact Cell0260.accepted_cell m (by linarith [(lt_of_not_ge hc249).le]) hc250
      ·
        by_cases hc251 : m ≤ 937/2560
        · exact Cell0261.accepted_cell m (by linarith [(lt_of_not_ge hc250).le]) hc251
        ·
          by_cases hc252 : m ≤ 3751/10240
          · exact Cell0262.accepted_cell m (by linarith [(lt_of_not_ge hc251).le]) hc252
          ·
            by_cases hc253 : m ≤ 1877/5120
            · exact Cell0263.accepted_cell m (by linarith [(lt_of_not_ge hc252).le]) hc253
            ·
              by_cases hc254 : m ≤ 3757/10240
              · exact Cell0264.accepted_cell m (by linarith [(lt_of_not_ge hc253).le]) hc254
              ·
                exact Cell0265.accepted_cell m (by linarith [(lt_of_not_ge hc254).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


