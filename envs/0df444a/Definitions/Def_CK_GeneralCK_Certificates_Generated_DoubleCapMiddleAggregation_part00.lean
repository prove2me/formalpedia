-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part00
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T01:58:38.028165+00:00
-- url     : https://prove2.me/theorems/e9099725-2d6d-4b8b-8bd5-5ce1fbe2195e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddleAggregation (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0000__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0005__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0009__3
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapLowResidual_middle : ∀ m, 1/5 ≤ m → m ≤ 1/4 → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  by_cases h0000 : m ≤ 33/160
  · exact Cell0000.accepted_cell m (by linarith [hmLo]) h0000
  ·
    by_cases h0001 : m ≤ 17/80
    · exact Cell0001.accepted_cell m (by linarith [(lt_of_not_ge h0000).le]) h0001
    ·
      by_cases h0002 : m ≤ 7/32
      · exact Cell0002.accepted_cell m (by linarith [(lt_of_not_ge h0001).le]) h0002
      ·
        by_cases h0003 : m ≤ 9/40
        · exact Cell0003.accepted_cell m (by linarith [(lt_of_not_ge h0002).le]) h0003
        ·
          by_cases h0004 : m ≤ 37/160
          · exact Cell0004.accepted_cell m (by linarith [(lt_of_not_ge h0003).le]) h0004
          ·
            by_cases h0005 : m ≤ 19/80
            · exact Cell0005.accepted_cell m (by linarith [(lt_of_not_ge h0004).le]) h0005
            ·
              by_cases h0006 : m ≤ 77/320
              · exact Cell0006.accepted_cell m (by linarith [(lt_of_not_ge h0005).le]) h0006
              ·
                by_cases h0007 : m ≤ 39/160
                · exact Cell0007.accepted_cell m (by linarith [(lt_of_not_ge h0006).le]) h0007
                ·
                  by_cases h0008 : m ≤ 79/320
                  · exact Cell0008.accepted_cell m (by linarith [(lt_of_not_ge h0007).le]) h0008
                  ·
                    exact Cell0009.accepted_cell m (by linarith [(lt_of_not_ge h0008).le]) hmHi

end GeneralCK.Certificates.DoubleCapMiddle


