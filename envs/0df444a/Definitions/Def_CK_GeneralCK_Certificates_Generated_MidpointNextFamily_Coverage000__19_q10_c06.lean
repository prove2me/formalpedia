-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q10_c06
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q10_c06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T04:13:55.691796+00:00
-- url     : https://prove2.me/theorems/3a016d4d-093b-4794-8f28-66f14519e7fb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (proof part of coverage010)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (proof part of coverage010)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (proof part of coverage010)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (proof part of coverage010) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage000 (proof part of coverage010).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0171__4

namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage010_part_06 {a z : ℝ} (ha : Bounds (91/500) (463/2500) a)
    (hz : Bounds (1/100) (1/20) z) (h0 : ¬ (a≤(459/2500:ℝ))) (h8 : ¬ (a≤(461/2500:ℝ))) (h12 : a≤(231/1250:ℝ)) :
    0<curvature a (a*z) := by
  by_cases h13 : a≤(923/5000:ℝ)
  · exact Cell0172.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
  · exact Cell0173.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz

end GeneralCK.Certificates.ReflectionMidpointNextFamily


