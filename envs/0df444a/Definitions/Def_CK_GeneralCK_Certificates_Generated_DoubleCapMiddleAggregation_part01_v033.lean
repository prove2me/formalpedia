-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v033
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v033
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:48:36.698454+00:00
-- url     : https://prove2.me/theorems/267869b3-4208-4ffd-a80e-1da135e68eb5
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0270__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0275__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0279__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v033 (m : ℝ) (hL : 473/1280 ≤ m) (hU : m ≤ 119/320) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc264 : m ≤ 3787/10240
  · exact Cell0274.accepted_cell m (by linarith [hL]) hc264
  ·
    by_cases hc265 : m ≤ 379/1024
    · exact Cell0275.accepted_cell m (by linarith [(lt_of_not_ge hc264).le]) hc265
    ·
      by_cases hc266 : m ≤ 3793/10240
      · exact Cell0276.accepted_cell m (by linarith [(lt_of_not_ge hc265).le]) hc266
      ·
        by_cases hc267 : m ≤ 949/2560
        · exact Cell0277.accepted_cell m (by linarith [(lt_of_not_ge hc266).le]) hc267
        ·
          by_cases hc268 : m ≤ 3799/10240
          · exact Cell0278.accepted_cell m (by linarith [(lt_of_not_ge hc267).le]) hc268
          ·
            by_cases hc269 : m ≤ 1901/5120
            · exact Cell0279.accepted_cell m (by linarith [(lt_of_not_ge hc268).le]) hc269
            ·
              by_cases hc270 : m ≤ 761/2048
              · exact Cell0280.accepted_cell m (by linarith [(lt_of_not_ge hc269).le]) hc270
              ·
                exact Cell0281.accepted_cell m (by linarith [(lt_of_not_ge hc270).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


