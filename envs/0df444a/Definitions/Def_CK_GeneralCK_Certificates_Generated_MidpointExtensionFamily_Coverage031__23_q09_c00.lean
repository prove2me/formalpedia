-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23_q09_c00
-- name    : CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23_q09_c00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T20:46:15.438702+00:00
-- url     : https://prove2.me/theorems/d46b7e60-a710-4c33-85f1-eef6dcec1787
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (proof part of coverage040)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (proof part of coverage040)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (proof part of coverage040)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (proof part of coverage040) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage031 (proof part of coverage040).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0620__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0624__3

namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage040_part_00 {a z : ℝ} (ha : Bounds (811/5000) (827/5000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) (h0 : a ≤ (819/5000:ℝ)) (h1 : a ≤ (163/1000:ℝ)) (h2 : a ≤ (813/5000:ℝ)) :
    0 < curvature a (a*z) := by
  by_cases h3 : a ≤ (203/1250:ℝ)
  · exact Cell0623.curvature_pos ⟨ha.1,h3⟩ hz
  · exact Cell0624.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz

end GeneralCK.Certificates.ReflectionMidpointExtensionFamily


