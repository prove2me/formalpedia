-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v044
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v044
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T00:29:49.204645+00:00
-- url     : https://prove2.me/theorems/3f97cb05-2eb0-4b4c-a55b-8ce953ff9fb2
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0361__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0365__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0369__3
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v044 (m : ℝ) (hL : 491/1280 ≤ m) (hU : m ≤ 197/512) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc352 : m ≤ 7859/20480
  · exact Cell0362.accepted_cell m (by linarith [hL]) hc352
  ·
    by_cases hc353 : m ≤ 3931/10240
    · exact Cell0363.accepted_cell m (by linarith [(lt_of_not_ge hc352).le]) hc353
    ·
      by_cases hc354 : m ≤ 1573/4096
      · exact Cell0364.accepted_cell m (by linarith [(lt_of_not_ge hc353).le]) hc354
      ·
        by_cases hc355 : m ≤ 1967/5120
        · exact Cell0365.accepted_cell m (by linarith [(lt_of_not_ge hc354).le]) hc355
        ·
          by_cases hc356 : m ≤ 7871/20480
          · exact Cell0366.accepted_cell m (by linarith [(lt_of_not_ge hc355).le]) hc356
          ·
            by_cases hc357 : m ≤ 3937/10240
            · exact Cell0367.accepted_cell m (by linarith [(lt_of_not_ge hc356).le]) hc357
            ·
              by_cases hc358 : m ≤ 7877/20480
              · exact Cell0368.accepted_cell m (by linarith [(lt_of_not_ge hc357).le]) hc358
              ·
                exact Cell0369.accepted_cell m (by linarith [(lt_of_not_ge hc358).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


