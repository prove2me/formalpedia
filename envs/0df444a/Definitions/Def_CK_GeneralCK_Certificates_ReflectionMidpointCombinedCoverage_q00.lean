-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionMidpointCombinedCoverage_q00
-- name    : CK_GeneralCK_Certificates_ReflectionMidpointCombinedCoverage_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T00:02:53.108402+00:00
-- url     : https://prove2.me/theorems/0be48c9b-c154-4b79-83ab-43ba0ffbfae1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionMidpointCombinedCoverage (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionMidpointCombinedCoverage (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionMidpointCombinedCoverage (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionMidpointCombinedCoverage (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionMidpointCombinedCoverage (piece 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionMidpointCombinedCoverage_q00_lo
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionMidpointCombinedCoverage_q00_hi

namespace GeneralCK.Certificates.ReflectionMidpointCombinedCoverage

open GeneralCK.Reflection GeneralCK.Certificates.Reflection

/-- The five completed midpoint families give one contiguous certified strip. -/
theorem full_midpoint_through_post_next_band {a z : ℝ}
    (ha : Bounds (3 / 20) (999 / 1000) a)
    (hz : Bounds (1 / 1000) (43 / 500) z) :
    0 < curvature a (a * z) := by
  by_cases h1 : z ≤ (1 / 20 : ℝ)
  · exact midpoint_low ha ⟨hz.1, h1⟩
  · exact midpoint_high ha ⟨le_of_lt (lt_of_not_ge h1), hz.2⟩

end GeneralCK.Certificates.ReflectionMidpointCombinedCoverage


