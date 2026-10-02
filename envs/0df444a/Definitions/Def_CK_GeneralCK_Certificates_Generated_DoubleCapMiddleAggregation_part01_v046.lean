-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v046
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v046
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:11:37.574034+00:00
-- url     : https://prove2.me/theorems/c375fb5d-2256-4ac4-9f7a-47c1ef4e3396
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0378__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0382__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v046 (m : ℝ) (hL : 247/640 ≤ m) (hU : m ≤ 991/2560) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc368 : m ≤ 7907/20480
  · exact Cell0378.accepted_cell m (by linarith [hL]) hc368
  ·
    by_cases hc369 : m ≤ 791/2048
    · exact Cell0379.accepted_cell m (by linarith [(lt_of_not_ge hc368).le]) hc369
    ·
      by_cases hc370 : m ≤ 7913/20480
      · exact Cell0380.accepted_cell m (by linarith [(lt_of_not_ge hc369).le]) hc370
      ·
        by_cases hc371 : m ≤ 1979/5120
        · exact Cell0381.accepted_cell m (by linarith [(lt_of_not_ge hc370).le]) hc371
        ·
          by_cases hc372 : m ≤ 7919/20480
          · exact Cell0382.accepted_cell m (by linarith [(lt_of_not_ge hc371).le]) hc372
          ·
            by_cases hc373 : m ≤ 3961/10240
            · exact Cell0383.accepted_cell m (by linarith [(lt_of_not_ge hc372).le]) hc373
            ·
              by_cases hc374 : m ≤ 1585/4096
              · exact Cell0384.accepted_cell m (by linarith [(lt_of_not_ge hc373).le]) hc374
              ·
                exact Cell0385.accepted_cell m (by linarith [(lt_of_not_ge hc374).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


