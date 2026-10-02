-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v007
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v007
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T23:37:42.949412+00:00
-- url     : https://prove2.me/theorems/e34b8eb8-4dcd-46c4-b996-2aa907c73cfc
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0062__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0067__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0071__6
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v007 (m : ℝ) (hL : 289/1024 ≤ m) (hU : m ≤ 1469/5120) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc56 : m ≤ 181/640
  · exact Cell0066.accepted_cell m (by linarith [hL]) hc56
  ·
    by_cases hc57 : m ≤ 1451/5120
    · exact Cell0067.accepted_cell m (by linarith [(lt_of_not_ge hc56).le]) hc57
    ·
      by_cases hc58 : m ≤ 727/2560
      · exact Cell0068.accepted_cell m (by linarith [(lt_of_not_ge hc57).le]) hc58
      ·
        by_cases hc59 : m ≤ 1457/5120
        · exact Cell0069.accepted_cell m (by linarith [(lt_of_not_ge hc58).le]) hc59
        ·
          by_cases hc60 : m ≤ 73/256
          · exact Cell0070.accepted_cell m (by linarith [(lt_of_not_ge hc59).le]) hc60
          ·
            by_cases hc61 : m ≤ 1463/5120
            · exact Cell0071.accepted_cell m (by linarith [(lt_of_not_ge hc60).le]) hc61
            ·
              by_cases hc62 : m ≤ 733/2560
              · exact Cell0072.accepted_cell m (by linarith [(lt_of_not_ge hc61).le]) hc62
              ·
                exact Cell0073.accepted_cell m (by linarith [(lt_of_not_ge hc62).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


