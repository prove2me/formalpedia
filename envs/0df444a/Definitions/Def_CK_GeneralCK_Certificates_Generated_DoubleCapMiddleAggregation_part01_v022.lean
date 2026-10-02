-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v022
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v022
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T23:22:11.101642+00:00
-- url     : https://prove2.me/theorems/0cac01b0-94c7-42ba-8427-d61b8be5d39a
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0184__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0190__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v022 (m : ℝ) (hL : 11/32 ≤ m) (hU : m ≤ 443/1280) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc176 : m ≤ 3523/10240
  · exact Cell0186.accepted_cell m (by linarith [hL]) hc176
  ·
    by_cases hc177 : m ≤ 1763/5120
    · exact Cell0187.accepted_cell m (by linarith [(lt_of_not_ge hc176).le]) hc177
    ·
      by_cases hc178 : m ≤ 3529/10240
      · exact Cell0188.accepted_cell m (by linarith [(lt_of_not_ge hc177).le]) hc178
      ·
        by_cases hc179 : m ≤ 883/2560
        · exact Cell0189.accepted_cell m (by linarith [(lt_of_not_ge hc178).le]) hc179
        ·
          by_cases hc180 : m ≤ 707/2048
          · exact Cell0190.accepted_cell m (by linarith [(lt_of_not_ge hc179).le]) hc180
          ·
            by_cases hc181 : m ≤ 1769/5120
            · exact Cell0191.accepted_cell m (by linarith [(lt_of_not_ge hc180).le]) hc181
            ·
              by_cases hc182 : m ≤ 3541/10240
              · exact Cell0192.accepted_cell m (by linarith [(lt_of_not_ge hc181).le]) hc182
              ·
                exact Cell0193.accepted_cell m (by linarith [(lt_of_not_ge hc182).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


