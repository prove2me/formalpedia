-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v057
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v057
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:08:16.534147+00:00
-- url     : https://prove2.me/theorems/b1db1b49-b55f-448b-8e12-4afe1fa771c6
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0466__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0470__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v057 (m : ℝ) (hL : 1021/2560 ≤ m) (hU : m ≤ 8183/20480) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc456 : m ≤ 8171/20480
  · exact Cell0466.accepted_cell m (by linarith [hL]) hc456
  ·
    by_cases hc457 : m ≤ 4087/10240
    · exact Cell0467.accepted_cell m (by linarith [(lt_of_not_ge hc456).le]) hc457
    ·
      by_cases hc458 : m ≤ 16351/40960
      · exact Cell0468.accepted_cell m (by linarith [(lt_of_not_ge hc457).le]) hc458
      ·
        by_cases hc459 : m ≤ 8177/20480
        · exact Cell0469.accepted_cell m (by linarith [(lt_of_not_ge hc458).le]) hc459
        ·
          by_cases hc460 : m ≤ 16357/40960
          · exact Cell0470.accepted_cell m (by linarith [(lt_of_not_ge hc459).le]) hc460
          ·
            by_cases hc461 : m ≤ 409/1024
            · exact Cell0471.accepted_cell m (by linarith [(lt_of_not_ge hc460).le]) hc461
            ·
              by_cases hc462 : m ≤ 16363/40960
              · exact Cell0472.accepted_cell m (by linarith [(lt_of_not_ge hc461).le]) hc462
              ·
                exact Cell0473.accepted_cell m (by linarith [(lt_of_not_ge hc462).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


