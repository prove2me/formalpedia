-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v036
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v036
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:47:17.26426+00:00
-- url     : https://prove2.me/theorems/6c49e6e8-0728-445f-862e-c0747b220514
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0298__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0302__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v036 (m : ℝ) (hL : 479/1280 ≤ m) (hU : m ≤ 961/2560) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc288 : m ≤ 7667/20480
  · exact Cell0298.accepted_cell m (by linarith [hL]) hc288
  ·
    by_cases hc289 : m ≤ 767/2048
    · exact Cell0299.accepted_cell m (by linarith [(lt_of_not_ge hc288).le]) hc289
    ·
      by_cases hc290 : m ≤ 7673/20480
      · exact Cell0300.accepted_cell m (by linarith [(lt_of_not_ge hc289).le]) hc290
      ·
        by_cases hc291 : m ≤ 1919/5120
        · exact Cell0301.accepted_cell m (by linarith [(lt_of_not_ge hc290).le]) hc291
        ·
          by_cases hc292 : m ≤ 7679/20480
          · exact Cell0302.accepted_cell m (by linarith [(lt_of_not_ge hc291).le]) hc292
          ·
            by_cases hc293 : m ≤ 3841/10240
            · exact Cell0303.accepted_cell m (by linarith [(lt_of_not_ge hc292).le]) hc293
            ·
              by_cases hc294 : m ≤ 1537/4096
              · exact Cell0304.accepted_cell m (by linarith [(lt_of_not_ge hc293).le]) hc294
              ·
                exact Cell0305.accepted_cell m (by linarith [(lt_of_not_ge hc294).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


