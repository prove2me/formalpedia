-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v039
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v039
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:48:53.507104+00:00
-- url     : https://prove2.me/theorems/868c3df4-4fce-418e-8d4c-be72703246de
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0322__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0326__4
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v039 (m : ℝ) (hL : 967/2560 ≤ m) (hU : m ≤ 97/256) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc312 : m ≤ 7739/20480
  · exact Cell0322.accepted_cell m (by linarith [hL]) hc312
  ·
    by_cases hc313 : m ≤ 3871/10240
    · exact Cell0323.accepted_cell m (by linarith [(lt_of_not_ge hc312).le]) hc313
    ·
      by_cases hc314 : m ≤ 1549/4096
      · exact Cell0324.accepted_cell m (by linarith [(lt_of_not_ge hc313).le]) hc314
      ·
        by_cases hc315 : m ≤ 1937/5120
        · exact Cell0325.accepted_cell m (by linarith [(lt_of_not_ge hc314).le]) hc315
        ·
          by_cases hc316 : m ≤ 7751/20480
          · exact Cell0326.accepted_cell m (by linarith [(lt_of_not_ge hc315).le]) hc316
          ·
            by_cases hc317 : m ≤ 3877/10240
            · exact Cell0327.accepted_cell m (by linarith [(lt_of_not_ge hc316).le]) hc317
            ·
              by_cases hc318 : m ≤ 7757/20480
              · exact Cell0328.accepted_cell m (by linarith [(lt_of_not_ge hc317).le]) hc318
              ·
                exact Cell0329.accepted_cell m (by linarith [(lt_of_not_ge hc318).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


