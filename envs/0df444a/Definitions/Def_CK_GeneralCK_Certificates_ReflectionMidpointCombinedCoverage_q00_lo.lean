-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionMidpointCombinedCoverage_q00_lo
-- name    : CK_GeneralCK_Certificates_ReflectionMidpointCombinedCoverage_q00_lo
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T20:44:37.089707+00:00
-- url     : https://prove2.me/theorems/a7a7881a-cb98-466a-8ac1-d65e16a6d815
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionMidpointCombinedCoverage (low z families)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionMidpointCombinedCoverage (low z families)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionMidpointCombinedCoverage (low z families)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionMidpointCombinedCoverage (low z families) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionMidpointCombinedCoverage (low z families).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_FullCertificate
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_FullCertificate

namespace GeneralCK.Certificates.ReflectionMidpointCombinedCoverage

open GeneralCK.Reflection GeneralCK.Certificates.Reflection

theorem midpoint_low {a z : ℝ}
    (ha : Bounds (3 / 20) (999 / 1000) a)
    (hz : Bounds (1 / 1000) (1 / 20) z) :
    0 < curvature a (a * z) := by
  by_cases h0 : z ≤ (1 / 100 : ℝ)
  · exact ReflectionMidpointFamily.full_midpoint_strip ha ⟨hz.1, h0⟩
  · exact ReflectionMidpointNextFamily.full_midpoint_next_strip ha
      ⟨le_of_lt (lt_of_not_ge h0), hz.2⟩

end GeneralCK.Certificates.ReflectionMidpointCombinedCoverage


