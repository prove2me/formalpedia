-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v043
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v043
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:00:48.928125+00:00
-- url     : https://prove2.me/theorems/4a9a97e0-c55d-4c7b-999f-38a5913f818d
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0352__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0355__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0357__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0361__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v043 (m : ℝ) (hL : 979/2560 ≤ m) (hU : m ≤ 491/1280) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc344 : m ≤ 1567/4096
  · exact Cell0354.accepted_cell m (by linarith [hL]) hc344
  ·
    by_cases hc345 : m ≤ 3919/10240
    · exact Cell0355.accepted_cell m (by linarith [(lt_of_not_ge hc344).le]) hc345
    ·
      by_cases hc346 : m ≤ 7841/20480
      · exact Cell0356.accepted_cell m (by linarith [(lt_of_not_ge hc345).le]) hc346
      ·
        by_cases hc347 : m ≤ 1961/5120
        · exact Cell0357.accepted_cell m (by linarith [(lt_of_not_ge hc346).le]) hc347
        ·
          by_cases hc348 : m ≤ 7847/20480
          · exact Cell0358.accepted_cell m (by linarith [(lt_of_not_ge hc347).le]) hc348
          ·
            by_cases hc349 : m ≤ 785/2048
            · exact Cell0359.accepted_cell m (by linarith [(lt_of_not_ge hc348).le]) hc349
            ·
              by_cases hc350 : m ≤ 7853/20480
              · exact Cell0360.accepted_cell m (by linarith [(lt_of_not_ge hc349).le]) hc350
              ·
                exact Cell0361.accepted_cell m (by linarith [(lt_of_not_ge hc350).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


