-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v018
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v018
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T23:13:46.734554+00:00
-- url     : https://prove2.me/theorems/34dfab8c-5aba-4288-8f9b-f0b4d3b8aa32
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0154__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0159__6
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v018 (m : ℝ) (hL : 1709/5120 ≤ m) (hU : m ≤ 431/1280) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc144 : m ≤ 107/320
  · exact Cell0154.accepted_cell m (by linarith [hL]) hc144
  ·
    by_cases hc145 : m ≤ 343/1024
    · exact Cell0155.accepted_cell m (by linarith [(lt_of_not_ge hc144).le]) hc145
    ·
      by_cases hc146 : m ≤ 3433/10240
      · exact Cell0156.accepted_cell m (by linarith [(lt_of_not_ge hc145).le]) hc146
      ·
        by_cases hc147 : m ≤ 859/2560
        · exact Cell0157.accepted_cell m (by linarith [(lt_of_not_ge hc146).le]) hc147
        ·
          by_cases hc148 : m ≤ 3439/10240
          · exact Cell0158.accepted_cell m (by linarith [(lt_of_not_ge hc147).le]) hc148
          ·
            by_cases hc149 : m ≤ 1721/5120
            · exact Cell0159.accepted_cell m (by linarith [(lt_of_not_ge hc148).le]) hc149
            ·
              by_cases hc150 : m ≤ 689/2048
              · exact Cell0160.accepted_cell m (by linarith [(lt_of_not_ge hc149).le]) hc150
              ·
                exact Cell0161.accepted_cell m (by linarith [(lt_of_not_ge hc150).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


