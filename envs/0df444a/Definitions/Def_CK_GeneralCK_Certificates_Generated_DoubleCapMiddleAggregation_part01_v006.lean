-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v006
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v006
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T23:01:09.200998+00:00
-- url     : https://prove2.me/theorems/90575711-1f71-4dc2-ab00-06abdb6fbc3d
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0057__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0062__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v006 (m : ℝ) (hL : 1421/5120 ≤ m) (hU : m ≤ 289/1024) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc48 : m ≤ 89/320
  · exact Cell0058.accepted_cell m (by linarith [hL]) hc48
  ·
    by_cases hc49 : m ≤ 1427/5120
    · exact Cell0059.accepted_cell m (by linarith [(lt_of_not_ge hc48).le]) hc49
    ·
      by_cases hc50 : m ≤ 143/512
      · exact Cell0060.accepted_cell m (by linarith [(lt_of_not_ge hc49).le]) hc50
      ·
        by_cases hc51 : m ≤ 1433/5120
        · exact Cell0061.accepted_cell m (by linarith [(lt_of_not_ge hc50).le]) hc51
        ·
          by_cases hc52 : m ≤ 359/1280
          · exact Cell0062.accepted_cell m (by linarith [(lt_of_not_ge hc51).le]) hc52
          ·
            by_cases hc53 : m ≤ 1439/5120
            · exact Cell0063.accepted_cell m (by linarith [(lt_of_not_ge hc52).le]) hc53
            ·
              by_cases hc54 : m ≤ 721/2560
              · exact Cell0064.accepted_cell m (by linarith [(lt_of_not_ge hc53).le]) hc54
              ·
                exact Cell0065.accepted_cell m (by linarith [(lt_of_not_ge hc54).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


