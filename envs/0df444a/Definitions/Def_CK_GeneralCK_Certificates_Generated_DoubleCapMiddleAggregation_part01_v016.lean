-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v016
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v016
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:55:59.716531+00:00
-- url     : https://prove2.me/theorems/7aa105eb-88fe-4582-927a-6b673009433b
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0138__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0142__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v016 (m : ℝ) (hL : 1661/5120 ≤ m) (hU : m ≤ 337/1024) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc128 : m ≤ 13/40
  · exact Cell0138.accepted_cell m (by linarith [hL]) hc128
  ·
    by_cases hc129 : m ≤ 1667/5120
    · exact Cell0139.accepted_cell m (by linarith [(lt_of_not_ge hc128).le]) hc129
    ·
      by_cases hc130 : m ≤ 167/512
      · exact Cell0140.accepted_cell m (by linarith [(lt_of_not_ge hc129).le]) hc130
      ·
        by_cases hc131 : m ≤ 1673/5120
        · exact Cell0141.accepted_cell m (by linarith [(lt_of_not_ge hc130).le]) hc131
        ·
          by_cases hc132 : m ≤ 419/1280
          · exact Cell0142.accepted_cell m (by linarith [(lt_of_not_ge hc131).le]) hc132
          ·
            by_cases hc133 : m ≤ 1679/5120
            · exact Cell0143.accepted_cell m (by linarith [(lt_of_not_ge hc132).le]) hc133
            ·
              by_cases hc134 : m ≤ 841/2560
              · exact Cell0144.accepted_cell m (by linarith [(lt_of_not_ge hc133).le]) hc134
              ·
                exact Cell0145.accepted_cell m (by linarith [(lt_of_not_ge hc134).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


