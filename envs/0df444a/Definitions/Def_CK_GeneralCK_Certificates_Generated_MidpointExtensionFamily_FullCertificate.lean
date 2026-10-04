-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_FullCertificate
-- name    : CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_FullCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T23:14:34.94173+00:00
-- url     : https://prove2.me/theorems/c52c96a1-fee0-445c-a87a-ceaff184c686
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.FullCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.FullCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.FullCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointExtensionFamily.FullCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointExtensionFamily/FullCertificate.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_BandCertificate000__3

-- ===== source module GeneralCK.Certificates.Generated.MidpointExtensionFamily.FullCertificate =====
section
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem full_midpoint_extension {a z : ℝ} (ha : Bounds (3/20) (999/1000) a)
    (hz : Bounds (1/20) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : z ≤ (81/1000:ℝ)
  · exact bandcertificate000 ha ⟨hz.1,h0⟩
  · by_cases h1 : z ≤ (2033/25000:ℝ)
    · exact bandcertificate001 ha ⟨le_of_lt (lt_of_not_ge h0),h1⟩
    · exact bandcertificate002 ha ⟨le_of_lt (lt_of_not_ge h1),hz.2⟩
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

end


