-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v002
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v002
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:59:22.530334+00:00
-- url     : https://prove2.me/theorems/1526af84-e891-44a7-bbfd-1627d6f9cfa5
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0024__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0029__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0033__3
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v002 (m : ℝ) (hL : 265/1024 ≤ m) (hU : m ≤ 1349/5120) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc16 : m ≤ 83/320
  · exact Cell0026.accepted_cell m (by linarith [hL]) hc16
  ·
    by_cases hc17 : m ≤ 1331/5120
    · exact Cell0027.accepted_cell m (by linarith [(lt_of_not_ge hc16).le]) hc17
    ·
      by_cases hc18 : m ≤ 667/2560
      · exact Cell0028.accepted_cell m (by linarith [(lt_of_not_ge hc17).le]) hc18
      ·
        by_cases hc19 : m ≤ 1337/5120
        · exact Cell0029.accepted_cell m (by linarith [(lt_of_not_ge hc18).le]) hc19
        ·
          by_cases hc20 : m ≤ 67/256
          · exact Cell0030.accepted_cell m (by linarith [(lt_of_not_ge hc19).le]) hc20
          ·
            by_cases hc21 : m ≤ 1343/5120
            · exact Cell0031.accepted_cell m (by linarith [(lt_of_not_ge hc20).le]) hc21
            ·
              by_cases hc22 : m ≤ 673/2560
              · exact Cell0032.accepted_cell m (by linarith [(lt_of_not_ge hc21).le]) hc22
              ·
                exact Cell0033.accepted_cell m (by linarith [(lt_of_not_ge hc22).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


