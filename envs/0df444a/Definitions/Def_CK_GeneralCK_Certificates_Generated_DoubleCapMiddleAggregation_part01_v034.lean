-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v034
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01_v034
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:45:52.662008+00:00
-- url     : https://prove2.me/theorems/8dfc3e69-1b37-4b9e-893a-e1e795b37b18
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

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0279__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0283__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0288__5
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapHighResidual_middle_v034 (m : ℝ) (hL : 119/320 ≤ m) (hU : m ≤ 191/512) : 0 ≤ doubleCapHighResidual m := by
  by_cases hc272 : m ≤ 7619/20480
  · exact Cell0282.accepted_cell m (by linarith [hL]) hc272
  ·
    by_cases hc273 : m ≤ 3811/10240
    · exact Cell0283.accepted_cell m (by linarith [(lt_of_not_ge hc272).le]) hc273
    ·
      by_cases hc274 : m ≤ 1525/4096
      · exact Cell0284.accepted_cell m (by linarith [(lt_of_not_ge hc273).le]) hc274
      ·
        by_cases hc275 : m ≤ 1907/5120
        · exact Cell0285.accepted_cell m (by linarith [(lt_of_not_ge hc274).le]) hc275
        ·
          by_cases hc276 : m ≤ 7631/20480
          · exact Cell0286.accepted_cell m (by linarith [(lt_of_not_ge hc275).le]) hc276
          ·
            by_cases hc277 : m ≤ 3817/10240
            · exact Cell0287.accepted_cell m (by linarith [(lt_of_not_ge hc276).le]) hc277
            ·
              by_cases hc278 : m ≤ 7637/20480
              · exact Cell0288.accepted_cell m (by linarith [(lt_of_not_ge hc277).le]) hc278
              ·
                exact Cell0289.accepted_cell m (by linarith [(lt_of_not_ge hc278).le]) hU

end GeneralCK.Certificates.DoubleCapMiddle


