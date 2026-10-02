-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v038
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v038
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:43:25.04698+00:00
-- url     : https://prove2.me/theorems/b3a3f3c2-638c-406f-8e10-28841530b421
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0312__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0316__6
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v038 (m : ℝ) (hL : 241/640 ≤ m) (hU : m ≤ 967/2560) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc304 : m ≤ 1543/4096
  · exact Cell0314.accepted_cell m (by linarith [hL]) hc304
  ·
    by_cases hc305 : m ≤ 3859/10240
    · exact Cell0315.accepted_cell m (by linarith [(lt_of_not_ge hc304).le]) hc305
    ·
      by_cases hc306 : m ≤ 7721/20480
      · exact Cell0316.accepted_cell m (by linarith [(lt_of_not_ge hc305).le]) hc306
      ·
        by_cases hc307 : m ≤ 1931/5120
        · exact Cell0317.accepted_cell m (by linarith [(lt_of_not_ge hc306).le]) hc307
        ·
          by_cases hc308 : m ≤ 7727/20480
          · exact Cell0318.accepted_cell m (by linarith [(lt_of_not_ge hc307).le]) hc308
          ·
            by_cases hc309 : m ≤ 773/2048
            · exact Cell0319.accepted_cell m (by linarith [(lt_of_not_ge hc308).le]) hc309
            ·
              by_cases hc310 : m ≤ 7733/20480
              · exact Cell0320.accepted_cell m (by linarith [(lt_of_not_ge hc309).le]) hc310
              ·
                exact Cell0321.accepted_cell m (by linarith [(lt_of_not_ge hc310).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


