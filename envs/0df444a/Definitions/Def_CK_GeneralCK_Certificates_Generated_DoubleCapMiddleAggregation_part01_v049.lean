-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v049
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v049
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:50:03.066222+00:00
-- url     : https://prove2.me/theorems/3d0669d6-ee35-417c-9b19-0f2756fee0ac
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0400__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0404__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0407__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v049 (m : ℝ) (hL : 997/2560 ≤ m) (hU : m ≤ 25/64) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc392 : m ≤ 7979/20480
  · exact Cell0402.accepted_cell m (by linarith [hL]) hc392
  ·
    by_cases hc393 : m ≤ 3991/10240
    · exact Cell0403.accepted_cell m (by linarith [(lt_of_not_ge hc392).le]) hc393
    ·
      by_cases hc394 : m ≤ 1597/4096
      · exact Cell0404.accepted_cell m (by linarith [(lt_of_not_ge hc393).le]) hc394
      ·
        by_cases hc395 : m ≤ 1997/5120
        · exact Cell0405.accepted_cell m (by linarith [(lt_of_not_ge hc394).le]) hc395
        ·
          by_cases hc396 : m ≤ 7991/20480
          · exact Cell0406.accepted_cell m (by linarith [(lt_of_not_ge hc395).le]) hc396
          ·
            by_cases hc397 : m ≤ 3997/10240
            · exact Cell0407.accepted_cell m (by linarith [(lt_of_not_ge hc396).le]) hc397
            ·
              by_cases hc398 : m ≤ 7997/20480
              · exact Cell0408.accepted_cell m (by linarith [(lt_of_not_ge hc397).le]) hc398
              ·
                exact Cell0409.accepted_cell m (by linarith [(lt_of_not_ge hc398).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


