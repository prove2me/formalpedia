-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v014
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v014
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T00:49:18.331042+00:00
-- url     : https://prove2.me/theorems/49cedddc-3d62-4a3a-8267-c216b9da9f08
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0120__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0125__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0129__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v014 (m : ℝ) (hL : 1613/5120 ≤ m) (hU : m ≤ 1637/5120) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc112 : m ≤ 101/320
  · exact Cell0122.accepted_cell m (by linarith [hL]) hc112
  ·
    by_cases hc113 : m ≤ 1619/5120
    · exact Cell0123.accepted_cell m (by linarith [(lt_of_not_ge hc112).le]) hc113
    ·
      by_cases hc114 : m ≤ 811/2560
      · exact Cell0124.accepted_cell m (by linarith [(lt_of_not_ge hc113).le]) hc114
      ·
        by_cases hc115 : m ≤ 325/1024
        · exact Cell0125.accepted_cell m (by linarith [(lt_of_not_ge hc114).le]) hc115
        ·
          by_cases hc116 : m ≤ 407/1280
          · exact Cell0126.accepted_cell m (by linarith [(lt_of_not_ge hc115).le]) hc116
          ·
            by_cases hc117 : m ≤ 1631/5120
            · exact Cell0127.accepted_cell m (by linarith [(lt_of_not_ge hc116).le]) hc117
            ·
              by_cases hc118 : m ≤ 817/2560
              · exact Cell0128.accepted_cell m (by linarith [(lt_of_not_ge hc117).le]) hc118
              ·
                exact Cell0129.accepted_cell m (by linarith [(lt_of_not_ge hc118).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


