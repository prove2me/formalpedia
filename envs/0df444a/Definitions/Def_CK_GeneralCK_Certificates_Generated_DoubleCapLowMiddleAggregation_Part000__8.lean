-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T08:17:10.629782+00:00
-- url     : https://prove2.me/theorems/0d841bf9-d85e-4967-8e80-0a3653870a3d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, Ge…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000 (+7 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006, GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part000 (+7 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part001, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part002, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part003, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part004, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part005, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part006, GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/Part007).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8_q06
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0224__4

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007 =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part007
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem cover : ∀ m : ℝ, 141 / 800 ≤ m → m ≤ 1 / 5 →
    0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  by_cases h0224 : m ≤ (583 / 3200 : ℝ)
  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0224.accepted_cell m (by linarith [hmLo]) h0224
  ·
    by_cases h0225 : m ≤ (301 / 1600 : ℝ)
    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0225.accepted_cell m (by linarith [(lt_of_not_ge h0224).le]) h0225
    ·
      by_cases h0226 : m ≤ (621 / 3200 : ℝ)
      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0226.accepted_cell m (by linarith [(lt_of_not_ge h0225).le]) h0226
      ·
        exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0227.accepted_cell m (by linarith [(lt_of_not_ge h0226).le]) hmHi

#print axioms cover
end GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part007

end


