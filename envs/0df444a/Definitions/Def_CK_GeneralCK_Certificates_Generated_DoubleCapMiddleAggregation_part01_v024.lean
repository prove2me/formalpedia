-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v024
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v024
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:40:56.885903+00:00
-- url     : https://prove2.me/theorems/bfe95370-ee8c-4998-acf0-b3ab57093ca0
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0201__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0207__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v024 (m : ℝ) (hL : 223/640 ≤ m) (hU : m ≤ 449/1280) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc192 : m ≤ 3571/10240
  · exact Cell0202.accepted_cell m (by linarith [hL]) hc192
  ·
    by_cases hc193 : m ≤ 1787/5120
    · exact Cell0203.accepted_cell m (by linarith [(lt_of_not_ge hc192).le]) hc193
    ·
      by_cases hc194 : m ≤ 3577/10240
      · exact Cell0204.accepted_cell m (by linarith [(lt_of_not_ge hc193).le]) hc194
      ·
        by_cases hc195 : m ≤ 179/512
        · exact Cell0205.accepted_cell m (by linarith [(lt_of_not_ge hc194).le]) hc195
        ·
          by_cases hc196 : m ≤ 3583/10240
          · exact Cell0206.accepted_cell m (by linarith [(lt_of_not_ge hc195).le]) hc196
          ·
            by_cases hc197 : m ≤ 1793/5120
            · exact Cell0207.accepted_cell m (by linarith [(lt_of_not_ge hc196).le]) hc197
            ·
              by_cases hc198 : m ≤ 3589/10240
              · exact Cell0208.accepted_cell m (by linarith [(lt_of_not_ge hc197).le]) hc198
              ·
                exact Cell0209.accepted_cell m (by linarith [(lt_of_not_ge hc198).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


