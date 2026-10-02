-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q09_c05
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q09_c05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T02:40:13.376778+00:00
-- url     : https://prove2.me/theorems/a9f60f91-2292-42c9-8cf5-870b9d61b8b5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (proof part of coverage009)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (proof part of coverage009)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (proof part of coverage009)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (proof part of coverage009) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage000 (proof part of coverage009).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0151__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0155__4

namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage009_part_05 {a z : ℝ} (ha : Bounds (447/2500) (91/500) a)
    (hz : Bounds (1/100) (1/20) z) (h0 : ¬ (a≤(451/2500:ℝ))) (h8 : a≤(453/2500:ℝ)) (h9 : ¬ (a≤(113/625:ℝ))) :
    0<curvature a (a*z) := by
  by_cases h11 : a≤(181/1000:ℝ)
  · exact Cell0154.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
  · exact Cell0155.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz

end GeneralCK.Certificates.ReflectionMidpointNextFamily


