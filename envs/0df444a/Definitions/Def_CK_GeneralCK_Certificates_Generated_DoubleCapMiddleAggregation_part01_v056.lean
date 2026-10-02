-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v056
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v056
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T23:04:00.458594+00:00
-- url     : https://prove2.me/theorems/aafab9c5-e6c0-4053-8483-1344985bde32
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0455__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0460__6
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v056 (m : ℝ) (hL : 509/1280 ≤ m) (hU : m ≤ 1021/2560) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc448 : m ≤ 8147/20480
  · exact Cell0458.accepted_cell m (by linarith [hL]) hc448
  ·
    by_cases hc449 : m ≤ 815/2048
    · exact Cell0459.accepted_cell m (by linarith [(lt_of_not_ge hc448).le]) hc449
    ·
      by_cases hc450 : m ≤ 8153/20480
      · exact Cell0460.accepted_cell m (by linarith [(lt_of_not_ge hc449).le]) hc450
      ·
        by_cases hc451 : m ≤ 2039/5120
        · exact Cell0461.accepted_cell m (by linarith [(lt_of_not_ge hc450).le]) hc451
        ·
          by_cases hc452 : m ≤ 8159/20480
          · exact Cell0462.accepted_cell m (by linarith [(lt_of_not_ge hc451).le]) hc452
          ·
            by_cases hc453 : m ≤ 4081/10240
            · exact Cell0463.accepted_cell m (by linarith [(lt_of_not_ge hc452).le]) hc453
            ·
              by_cases hc454 : m ≤ 1633/4096
              · exact Cell0464.accepted_cell m (by linarith [(lt_of_not_ge hc453).le]) hc454
              ·
                exact Cell0465.accepted_cell m (by linarith [(lt_of_not_ge hc454).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


