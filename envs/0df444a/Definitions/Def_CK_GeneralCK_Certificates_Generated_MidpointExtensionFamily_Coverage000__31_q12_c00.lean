-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage000__31_q12_c00
-- name    : CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage000__31_q12_c00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T19:44:12.688729+00:00
-- url     : https://prove2.me/theorems/471c7b2e-ba0a-457c-9975-40ef9f9d94b3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (proof part of coverage012)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (proof part of coverage012)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (proof part of coverage012)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (proof part of coverage012) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage000 (proof part of coverage012).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0190__4

namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage012_part_00 {a z : ℝ} (ha : Bounds (459/2000) (127/500) a)
    (hz : Bounds (1/20) (81/1000) z) (h0 : a ≤ (241/1000:ℝ)) (h1 : a ≤ (47/200:ℝ)) (h2 : a ≤ (29/125:ℝ)) :
    0 < curvature a (a*z) := by
  by_cases h3 : a ≤ (461/2000:ℝ)
  · exact Cell0192.curvature_pos ⟨ha.1,h3⟩ hz
  · exact Cell0193.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz

end GeneralCK.Certificates.ReflectionMidpointExtensionFamily


