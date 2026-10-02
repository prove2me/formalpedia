-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v041
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v041
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:32:42.504398+00:00
-- url     : https://prove2.me/theorems/578e6a86-0380-45d5-9367-db700ef580aa
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0336__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0340__6
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v041 (m : ℝ) (hL : 973/2560 ≤ m) (hU : m ≤ 61/160) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc328 : m ≤ 7787/20480
  · exact Cell0338.accepted_cell m (by linarith [hL]) hc328
  ·
    by_cases hc329 : m ≤ 779/2048
    · exact Cell0339.accepted_cell m (by linarith [(lt_of_not_ge hc328).le]) hc329
    ·
      by_cases hc330 : m ≤ 7793/20480
      · exact Cell0340.accepted_cell m (by linarith [(lt_of_not_ge hc329).le]) hc330
      ·
        by_cases hc331 : m ≤ 1949/5120
        · exact Cell0341.accepted_cell m (by linarith [(lt_of_not_ge hc330).le]) hc331
        ·
          by_cases hc332 : m ≤ 7799/20480
          · exact Cell0342.accepted_cell m (by linarith [(lt_of_not_ge hc331).le]) hc332
          ·
            by_cases hc333 : m ≤ 3901/10240
            · exact Cell0343.accepted_cell m (by linarith [(lt_of_not_ge hc332).le]) hc333
            ·
              by_cases hc334 : m ≤ 1561/4096
              · exact Cell0344.accepted_cell m (by linarith [(lt_of_not_ge hc333).le]) hc334
              ·
                exact Cell0345.accepted_cell m (by linarith [(lt_of_not_ge hc334).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


