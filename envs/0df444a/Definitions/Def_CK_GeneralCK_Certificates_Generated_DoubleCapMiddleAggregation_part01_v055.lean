-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v055
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v055
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:41:14.494127+00:00
-- url     : https://prove2.me/theorems/bd7910d6-042d-464a-a6ca-bb314ca7eed0
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0447__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0451__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0455__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v055 (m : ℝ) (hL : 203/512 ≤ m) (hU : m ≤ 509/1280) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc440 : m ≤ 8123/20480
  · exact Cell0450.accepted_cell m (by linarith [hL]) hc440
  ·
    by_cases hc441 : m ≤ 4063/10240
    · exact Cell0451.accepted_cell m (by linarith [(lt_of_not_ge hc440).le]) hc441
    ·
      by_cases hc442 : m ≤ 8129/20480
      · exact Cell0452.accepted_cell m (by linarith [(lt_of_not_ge hc441).le]) hc442
      ·
        by_cases hc443 : m ≤ 2033/5120
        · exact Cell0453.accepted_cell m (by linarith [(lt_of_not_ge hc442).le]) hc443
        ·
          by_cases hc444 : m ≤ 1627/4096
          · exact Cell0454.accepted_cell m (by linarith [(lt_of_not_ge hc443).le]) hc444
          ·
            by_cases hc445 : m ≤ 4069/10240
            · exact Cell0455.accepted_cell m (by linarith [(lt_of_not_ge hc444).le]) hc445
            ·
              by_cases hc446 : m ≤ 8141/20480
              · exact Cell0456.accepted_cell m (by linarith [(lt_of_not_ge hc445).le]) hc446
              ·
                exact Cell0457.accepted_cell m (by linarith [(lt_of_not_ge hc446).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


