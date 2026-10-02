-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v028
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v028
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T23:08:53.863999+00:00
-- url     : https://prove2.me/theorems/a2a6495e-a918-40ca-8be9-1787fce683e3
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0233__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0238__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v028 (m : ℝ) (hL : 229/640 ≤ m) (hU : m ≤ 461/1280) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc224 : m ≤ 3667/10240
  · exact Cell0234.accepted_cell m (by linarith [hL]) hc224
  ·
    by_cases hc225 : m ≤ 367/1024
    · exact Cell0235.accepted_cell m (by linarith [(lt_of_not_ge hc224).le]) hc225
    ·
      by_cases hc226 : m ≤ 3673/10240
      · exact Cell0236.accepted_cell m (by linarith [(lt_of_not_ge hc225).le]) hc226
      ·
        by_cases hc227 : m ≤ 919/2560
        · exact Cell0237.accepted_cell m (by linarith [(lt_of_not_ge hc226).le]) hc227
        ·
          by_cases hc228 : m ≤ 3679/10240
          · exact Cell0238.accepted_cell m (by linarith [(lt_of_not_ge hc227).le]) hc228
          ·
            by_cases hc229 : m ≤ 1841/5120
            · exact Cell0239.accepted_cell m (by linarith [(lt_of_not_ge hc228).le]) hc229
            ·
              by_cases hc230 : m ≤ 737/2048
              · exact Cell0240.accepted_cell m (by linarith [(lt_of_not_ge hc229).le]) hc230
              ·
                exact Cell0241.accepted_cell m (by linarith [(lt_of_not_ge hc230).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


