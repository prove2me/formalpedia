-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v000
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v000
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T23:34:19.781991+00:00
-- url     : https://prove2.me/theorems/afb68529-c76f-4cac-be56-f79b2b862a45
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0009__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0012__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0016__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v000 (m : ℝ) (hL : 1/4 ≤ m) (hU : m ≤ 1301/5120) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc0 : m ≤ 2563/10240
  · exact Cell0010.accepted_cell m (by linarith [hL]) hc0
  ·
    by_cases hc1 : m ≤ 1283/5120
    · exact Cell0011.accepted_cell m (by linarith [(lt_of_not_ge hc0).le]) hc1
    ·
      by_cases hc2 : m ≤ 643/2560
      · exact Cell0012.accepted_cell m (by linarith [(lt_of_not_ge hc1).le]) hc2
      ·
        by_cases hc3 : m ≤ 1289/5120
        · exact Cell0013.accepted_cell m (by linarith [(lt_of_not_ge hc2).le]) hc3
        ·
          by_cases hc4 : m ≤ 323/1280
          · exact Cell0014.accepted_cell m (by linarith [(lt_of_not_ge hc3).le]) hc4
          ·
            by_cases hc5 : m ≤ 259/1024
            · exact Cell0015.accepted_cell m (by linarith [(lt_of_not_ge hc4).le]) hc5
            ·
              by_cases hc6 : m ≤ 649/2560
              · exact Cell0016.accepted_cell m (by linarith [(lt_of_not_ge hc5).le]) hc6
              ·
                exact Cell0017.accepted_cell m (by linarith [(lt_of_not_ge hc6).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


