-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage000__31_q28_c02
-- name    : CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage000__31_q28_c02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T15:55:10.216558+00:00
-- url     : https://prove2.me/theorems/86956f5c-0df6-4340-a722-5f9f3fdade8b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (proof part of coverage028)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (proof part of coverage028)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (proof part of coverage028)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (proof part of coverage028) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage000 (proof part of coverage028).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0442__3

namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage028_part_02 {a z : ℝ} (ha : Bounds (401/2000) (421/2000) a)
    (hz : Bounds (81/1000) (2033/25000) z) (h0 : a ≤ (409/2000:ℝ)) (h1 : ¬ (a ≤ (81/400:ℝ))) (h5 : a ≤ (407/2000:ℝ)) :
    0 < curvature a (a*z) := by
  by_cases h6 : a ≤ (203/1000:ℝ)
  · exact Cell0442.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
  · exact Cell0443.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz

end GeneralCK.Certificates.ReflectionMidpointExtensionFamily


