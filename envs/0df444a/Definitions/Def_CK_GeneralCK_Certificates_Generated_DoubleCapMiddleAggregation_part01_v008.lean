-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v008
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v008
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:35:14.258101+00:00
-- url     : https://prove2.me/theorems/031f048f-6980-4e77-823f-d966f8cab7a8
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0071__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0077__6
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v008 (m : ℝ) (hL : 1469/5120 ≤ m) (hU : m ≤ 1493/5120) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc64 : m ≤ 23/80
  · exact Cell0074.accepted_cell m (by linarith [hL]) hc64
  ·
    by_cases hc65 : m ≤ 295/1024
    · exact Cell0075.accepted_cell m (by linarith [(lt_of_not_ge hc64).le]) hc65
    ·
      by_cases hc66 : m ≤ 739/2560
      · exact Cell0076.accepted_cell m (by linarith [(lt_of_not_ge hc65).le]) hc66
      ·
        by_cases hc67 : m ≤ 1481/5120
        · exact Cell0077.accepted_cell m (by linarith [(lt_of_not_ge hc66).le]) hc67
        ·
          by_cases hc68 : m ≤ 371/1280
          · exact Cell0078.accepted_cell m (by linarith [(lt_of_not_ge hc67).le]) hc68
          ·
            by_cases hc69 : m ≤ 1487/5120
            · exact Cell0079.accepted_cell m (by linarith [(lt_of_not_ge hc68).le]) hc69
            ·
              by_cases hc70 : m ≤ 149/512
              · exact Cell0080.accepted_cell m (by linarith [(lt_of_not_ge hc69).le]) hc70
              ·
                exact Cell0081.accepted_cell m (by linarith [(lt_of_not_ge hc70).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


