-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v025
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v025
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:17:00.852985+00:00
-- url     : https://prove2.me/theorems/106ab376-b47a-4e51-a97b-92815631ff1e
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0207__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0211__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0215__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v025 (m : ℝ) (hL : 449/1280 ≤ m) (hU : m ≤ 113/320) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc200 : m ≤ 719/2048
  · exact Cell0210.accepted_cell m (by linarith [hL]) hc200
  ·
    by_cases hc201 : m ≤ 1799/5120
    · exact Cell0211.accepted_cell m (by linarith [(lt_of_not_ge hc200).le]) hc201
    ·
      by_cases hc202 : m ≤ 3601/10240
      · exact Cell0212.accepted_cell m (by linarith [(lt_of_not_ge hc201).le]) hc202
      ·
        by_cases hc203 : m ≤ 901/2560
        · exact Cell0213.accepted_cell m (by linarith [(lt_of_not_ge hc202).le]) hc203
        ·
          by_cases hc204 : m ≤ 3607/10240
          · exact Cell0214.accepted_cell m (by linarith [(lt_of_not_ge hc203).le]) hc204
          ·
            by_cases hc205 : m ≤ 361/1024
            · exact Cell0215.accepted_cell m (by linarith [(lt_of_not_ge hc204).le]) hc205
            ·
              by_cases hc206 : m ≤ 3613/10240
              · exact Cell0216.accepted_cell m (by linarith [(lt_of_not_ge hc205).le]) hc206
              ·
                exact Cell0217.accepted_cell m (by linarith [(lt_of_not_ge hc206).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


