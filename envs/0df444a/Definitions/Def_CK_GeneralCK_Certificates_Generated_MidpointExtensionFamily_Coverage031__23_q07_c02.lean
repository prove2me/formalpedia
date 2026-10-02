-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23_q07_c02
-- name    : CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23_q07_c02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T19:14:22.443728+00:00
-- url     : https://prove2.me/theorems/68c0d3b5-852d-41e0-abf2-ef402c65244e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (proof part of coverage038)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (proof part of coverage038)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (proof part of coverage038)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (proof part of coverage038) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage031 (proof part of coverage038).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0595__4

namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage038_part_02 {a z : ℝ} (ha : Bounds (779/5000) (159/1000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) (h0 : a ≤ (787/5000:ℝ)) (h1 : ¬ (a ≤ (783/5000:ℝ))) (h5 : a ≤ (157/1000:ℝ)) :
    0 < curvature a (a*z) := by
  by_cases h6 : a ≤ (98/625:ℝ)
  · exact Cell0595.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
  · exact Cell0596.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz

end GeneralCK.Certificates.ReflectionMidpointExtensionFamily


