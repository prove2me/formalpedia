-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v027
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v027
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T23:11:48.220951+00:00
-- url     : https://prove2.me/theorems/f39b3ae7-b96e-450c-b287-b69ef525696b
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0224__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0228__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0233__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v027 (m : ℝ) (hL : 91/256 ≤ m) (hU : m ≤ 229/640) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc216 : m ≤ 3643/10240
  · exact Cell0226.accepted_cell m (by linarith [hL]) hc216
  ·
    by_cases hc217 : m ≤ 1823/5120
    · exact Cell0227.accepted_cell m (by linarith [(lt_of_not_ge hc216).le]) hc217
    ·
      by_cases hc218 : m ≤ 3649/10240
      · exact Cell0228.accepted_cell m (by linarith [(lt_of_not_ge hc217).le]) hc218
      ·
        by_cases hc219 : m ≤ 913/2560
        · exact Cell0229.accepted_cell m (by linarith [(lt_of_not_ge hc218).le]) hc219
        ·
          by_cases hc220 : m ≤ 731/2048
          · exact Cell0230.accepted_cell m (by linarith [(lt_of_not_ge hc219).le]) hc220
          ·
            by_cases hc221 : m ≤ 1829/5120
            · exact Cell0231.accepted_cell m (by linarith [(lt_of_not_ge hc220).le]) hc221
            ·
              by_cases hc222 : m ≤ 3661/10240
              · exact Cell0232.accepted_cell m (by linarith [(lt_of_not_ge hc221).le]) hc222
              ·
                exact Cell0233.accepted_cell m (by linarith [(lt_of_not_ge hc222).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


