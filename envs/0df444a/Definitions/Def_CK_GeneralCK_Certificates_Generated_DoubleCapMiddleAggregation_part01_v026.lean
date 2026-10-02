-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v026
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v026
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:12:26.220458+00:00
-- url     : https://prove2.me/theorems/0289a75f-37b9-4825-ba6e-d54830f27623
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0215__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0220__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0224__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v026 (m : ℝ) (hL : 113/320 ≤ m) (hU : m ≤ 91/256) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc208 : m ≤ 3619/10240
  · exact Cell0218.accepted_cell m (by linarith [hL]) hc208
  ·
    by_cases hc209 : m ≤ 1811/5120
    · exact Cell0219.accepted_cell m (by linarith [(lt_of_not_ge hc208).le]) hc209
    ·
      by_cases hc210 : m ≤ 725/2048
      · exact Cell0220.accepted_cell m (by linarith [(lt_of_not_ge hc209).le]) hc210
      ·
        by_cases hc211 : m ≤ 907/2560
        · exact Cell0221.accepted_cell m (by linarith [(lt_of_not_ge hc210).le]) hc211
        ·
          by_cases hc212 : m ≤ 3631/10240
          · exact Cell0222.accepted_cell m (by linarith [(lt_of_not_ge hc211).le]) hc212
          ·
            by_cases hc213 : m ≤ 1817/5120
            · exact Cell0223.accepted_cell m (by linarith [(lt_of_not_ge hc212).le]) hc213
            ·
              by_cases hc214 : m ≤ 3637/10240
              · exact Cell0224.accepted_cell m (by linarith [(lt_of_not_ge hc213).le]) hc214
              ·
                exact Cell0225.accepted_cell m (by linarith [(lt_of_not_ge hc214).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


