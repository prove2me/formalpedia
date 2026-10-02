-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v005
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v005
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:30:37.808566+00:00
-- url     : https://prove2.me/theorems/d9d66304-3672-40b0-be94-31e9685f3b60
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0046__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0052__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0057__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v005 (m : ℝ) (hL : 1397/5120 ≤ m) (hU : m ≤ 1421/5120) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc40 : m ≤ 35/128
  · exact Cell0050.accepted_cell m (by linarith [hL]) hc40
  ·
    by_cases hc41 : m ≤ 1403/5120
    · exact Cell0051.accepted_cell m (by linarith [(lt_of_not_ge hc40).le]) hc41
    ·
      by_cases hc42 : m ≤ 703/2560
      · exact Cell0052.accepted_cell m (by linarith [(lt_of_not_ge hc41).le]) hc42
      ·
        by_cases hc43 : m ≤ 1409/5120
        · exact Cell0053.accepted_cell m (by linarith [(lt_of_not_ge hc42).le]) hc43
        ·
          by_cases hc44 : m ≤ 353/1280
          · exact Cell0054.accepted_cell m (by linarith [(lt_of_not_ge hc43).le]) hc44
          ·
            by_cases hc45 : m ≤ 283/1024
            · exact Cell0055.accepted_cell m (by linarith [(lt_of_not_ge hc44).le]) hc45
            ·
              by_cases hc46 : m ≤ 709/2560
              · exact Cell0056.accepted_cell m (by linarith [(lt_of_not_ge hc45).le]) hc46
              ·
                exact Cell0057.accepted_cell m (by linarith [(lt_of_not_ge hc46).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


