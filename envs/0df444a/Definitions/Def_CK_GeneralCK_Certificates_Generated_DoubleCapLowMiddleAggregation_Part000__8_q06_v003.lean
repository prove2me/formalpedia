-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q06_v003
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q06_v003
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T07:06:08.83024+00:00
-- url     : https://prove2.me/theorems/ee311ebe-cf4b-4dc6-b4b6-fa4cc448a5d8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (proof segment of cover)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (proof segment of cover)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (proof segment of cover)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (proof segment of cover) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part000 (proof segment of cover).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0214__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0218__6

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part006
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000


theorem cover_v003 (m : ℝ) (hL : (919 / 6400 : ℝ) ≤ m) (hU : m ≤ 141 / 800) : 0 ≤ doubleCapLowResidual m := by
  by_cases hc24 : m ≤ (469 / 3200 : ℝ)
  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0216.accepted_cell m (by linarith [hL]) hc24
  ·
    by_cases hc25 : m ≤ (957 / 6400 : ℝ)
    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0217.accepted_cell m (by linarith [(lt_of_not_ge hc24).le]) hc25
    ·
      by_cases hc26 : m ≤ (61 / 400 : ℝ)
      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0218.accepted_cell m (by linarith [(lt_of_not_ge hc25).le]) hc26
      ·
        by_cases hc27 : m ≤ (199 / 1280 : ℝ)
        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0219.accepted_cell m (by linarith [(lt_of_not_ge hc26).le]) hc27
        ·
          by_cases hc28 : m ≤ (507 / 3200 : ℝ)
          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0220.accepted_cell m (by linarith [(lt_of_not_ge hc27).le]) hc28
          ·
            by_cases hc29 : m ≤ (263 / 1600 : ℝ)
            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0221.accepted_cell m (by linarith [(lt_of_not_ge hc28).le]) hc29
            ·
              by_cases hc30 : m ≤ (109 / 640 : ℝ)
              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0222.accepted_cell m (by linarith [(lt_of_not_ge hc29).le]) hc30
              ·
                exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0223.accepted_cell m (by linarith [(lt_of_not_ge hc30).le]) hU

end GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part006


