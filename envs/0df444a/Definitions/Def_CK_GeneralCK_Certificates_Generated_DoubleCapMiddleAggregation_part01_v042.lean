-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v042
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v042
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T23:03:54.880926+00:00
-- url     : https://prove2.me/theorems/4f795a3f-bebe-40f5-a7e9-fe7c2df2f5d1
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0346__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0352__3
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v042 (m : ℝ) (hL : 61/160 ≤ m) (hU : m ≤ 979/2560) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc336 : m ≤ 7811/20480
  · exact Cell0346.accepted_cell m (by linarith [hL]) hc336
  ·
    by_cases hc337 : m ≤ 3907/10240
    · exact Cell0347.accepted_cell m (by linarith [(lt_of_not_ge hc336).le]) hc337
    ·
      by_cases hc338 : m ≤ 7817/20480
      · exact Cell0348.accepted_cell m (by linarith [(lt_of_not_ge hc337).le]) hc338
      ·
        by_cases hc339 : m ≤ 391/1024
        · exact Cell0349.accepted_cell m (by linarith [(lt_of_not_ge hc338).le]) hc339
        ·
          by_cases hc340 : m ≤ 7823/20480
          · exact Cell0350.accepted_cell m (by linarith [(lt_of_not_ge hc339).le]) hc340
          ·
            by_cases hc341 : m ≤ 3913/10240
            · exact Cell0351.accepted_cell m (by linarith [(lt_of_not_ge hc340).le]) hc341
            ·
              by_cases hc342 : m ≤ 7829/20480
              · exact Cell0352.accepted_cell m (by linarith [(lt_of_not_ge hc341).le]) hc342
              ·
                exact Cell0353.accepted_cell m (by linarith [(lt_of_not_ge hc342).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


