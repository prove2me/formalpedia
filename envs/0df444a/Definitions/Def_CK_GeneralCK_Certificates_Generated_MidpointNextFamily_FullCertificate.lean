-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_FullCertificate
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_FullCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T02:02:14.235356+00:00
-- url     : https://prove2.me/theorems/23391ed3-8cac-44a1-ad43-ff6b2159c504
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.FullCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.FullCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.FullCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.FullCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/FullCertificate.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_FullCertificate_t00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_FullCertificate_t01
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_FullCertificate_t02
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_FullCertificate_t03

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.FullCertificate =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem full_midpoint_next_strip {a z : ℝ} (ha : Bounds (3/20) (999/1000) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(291/1000:ℝ)
  · by_cases h1 : a≤(479/2500:ℝ)
    · exact full_midpoint_next_strip_t00 ha hz h0 h1
    · exact full_midpoint_next_strip_t01 ha hz h0 h1
  · by_cases h27 : a≤(49/100:ℝ)
    · exact full_midpoint_next_strip_t02 ha hz h0 h27
    · exact full_midpoint_next_strip_t03 ha hz h0 h27
end GeneralCK.Certificates.ReflectionMidpointNextFamily

end


