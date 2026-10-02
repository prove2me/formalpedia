-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v053
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v053
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:46:05.686528+00:00
-- url     : https://prove2.me/theorems/a7a9e7d7-e521-4617-ae58-616b9be917d8
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0433__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0438__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v053 (m : ℝ) (hL : 1009/2560 ≤ m) (hU : m ≤ 253/640) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc424 : m ≤ 1615/4096
  · exact Cell0434.accepted_cell m (by linarith [hL]) hc424
  ·
    by_cases hc425 : m ≤ 4039/10240
    · exact Cell0435.accepted_cell m (by linarith [(lt_of_not_ge hc424).le]) hc425
    ·
      by_cases hc426 : m ≤ 8081/20480
      · exact Cell0436.accepted_cell m (by linarith [(lt_of_not_ge hc425).le]) hc426
      ·
        by_cases hc427 : m ≤ 2021/5120
        · exact Cell0437.accepted_cell m (by linarith [(lt_of_not_ge hc426).le]) hc427
        ·
          by_cases hc428 : m ≤ 8087/20480
          · exact Cell0438.accepted_cell m (by linarith [(lt_of_not_ge hc427).le]) hc428
          ·
            by_cases hc429 : m ≤ 809/2048
            · exact Cell0439.accepted_cell m (by linarith [(lt_of_not_ge hc428).le]) hc429
            ·
              by_cases hc430 : m ≤ 8093/20480
              · exact Cell0440.accepted_cell m (by linarith [(lt_of_not_ge hc429).le]) hc430
              ·
                exact Cell0441.accepted_cell m (by linarith [(lt_of_not_ge hc430).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


