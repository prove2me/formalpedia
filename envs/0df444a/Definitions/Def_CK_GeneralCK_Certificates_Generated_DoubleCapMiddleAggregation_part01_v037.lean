-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v037
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v037
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:42:52.967926+00:00
-- url     : https://prove2.me/theorems/f917197e-5570-4d9b-9685-30a2feaa6829
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0306__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0310__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0312__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v037 (m : ℝ) (hL : 961/2560 ≤ m) (hU : m ≤ 241/640) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc296 : m ≤ 7691/20480
  · exact Cell0306.accepted_cell m (by linarith [hL]) hc296
  ·
    by_cases hc297 : m ≤ 3847/10240
    · exact Cell0307.accepted_cell m (by linarith [(lt_of_not_ge hc296).le]) hc297
    ·
      by_cases hc298 : m ≤ 7697/20480
      · exact Cell0308.accepted_cell m (by linarith [(lt_of_not_ge hc297).le]) hc298
      ·
        by_cases hc299 : m ≤ 385/1024
        · exact Cell0309.accepted_cell m (by linarith [(lt_of_not_ge hc298).le]) hc299
        ·
          by_cases hc300 : m ≤ 7703/20480
          · exact Cell0310.accepted_cell m (by linarith [(lt_of_not_ge hc299).le]) hc300
          ·
            by_cases hc301 : m ≤ 3853/10240
            · exact Cell0311.accepted_cell m (by linarith [(lt_of_not_ge hc300).le]) hc301
            ·
              by_cases hc302 : m ≤ 7709/20480
              · exact Cell0312.accepted_cell m (by linarith [(lt_of_not_ge hc301).le]) hc302
              ·
                exact Cell0313.accepted_cell m (by linarith [(lt_of_not_ge hc302).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


