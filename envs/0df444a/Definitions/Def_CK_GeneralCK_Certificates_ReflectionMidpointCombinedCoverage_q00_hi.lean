-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionMidpointCombinedCoverage_q00_hi
-- name    : CK_GeneralCK_Certificates_ReflectionMidpointCombinedCoverage_q00_hi
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T20:15:56.563903+00:00
-- url     : https://prove2.me/theorems/056ff679-072f-412a-9e22-30372410c4fa
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionMidpointCombinedCoverage (high z families)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionMidpointCombinedCoverage (high z families)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionMidpointCombinedCoverage (high z families)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionMidpointCombinedCoverage (high z families) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionMidpointCombinedCoverage (high z families).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_FullCertificate
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_FullCertificate
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_FullCertificate

namespace GeneralCK.Certificates.ReflectionMidpointCombinedCoverage

open GeneralCK.Reflection GeneralCK.Certificates.Reflection

theorem midpoint_high {a z : ℝ}
    (ha : Bounds (3 / 20) (999 / 1000) a)
    (hz : Bounds (1 / 20) (43 / 500) z) :
    0 < curvature a (a * z) := by
  by_cases h2 : z ≤ (406621 / 5000000 : ℝ)
  · exact ReflectionMidpointExtensionFamily.full_midpoint_extension ha ⟨hz.1, h2⟩
  by_cases h3 : z ≤ (17 / 200 : ℝ)
  · exact ReflectionMidpointNextBandFamily.full_midpoint_next_band ha
      ⟨le_of_lt (lt_of_not_ge h2), h3⟩
  · exact ReflectionMidpointPostNextBandFamily.full_midpoint_post_next_band ha
      ⟨le_of_lt (lt_of_not_ge h3), hz.2⟩

end GeneralCK.Certificates.ReflectionMidpointCombinedCoverage


