-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v058
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v058
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T23:11:29.58721+00:00
-- url     : https://prove2.me/theorems/01976c69-21e8-4251-bebe-1f4d30d22677
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0470__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0475__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0479
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v058 (m : ℝ) (hL : 8183/20480 ≤ m) (hU : m ≤ 2/5) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc464 : m ≤ 16369/40960
  · exact Cell0474.accepted_cell m (by linarith [hL]) hc464
  ·
    by_cases hc465 : m ≤ 4093/10240
    · exact Cell0475.accepted_cell m (by linarith [(lt_of_not_ge hc464).le]) hc465
    ·
      by_cases hc466 : m ≤ 3275/8192
      · exact Cell0476.accepted_cell m (by linarith [(lt_of_not_ge hc465).le]) hc466
      ·
        by_cases hc467 : m ≤ 8189/20480
        · exact Cell0477.accepted_cell m (by linarith [(lt_of_not_ge hc466).le]) hc467
        ·
          by_cases hc468 : m ≤ 16381/40960
          · exact Cell0478.accepted_cell m (by linarith [(lt_of_not_ge hc467).le]) hc468
          ·
            exact Cell0479.accepted_cell m (by linarith [(lt_of_not_ge hc468).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


