-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_q17_c00
-- name    : CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_q17_c00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T11:34:14.68134+00:00
-- url     : https://prove2.me/theorems/1ce0247d-d4ca-4dc9-8b82-7fede2cb9937
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage017)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage017)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage017)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage017) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointFamily/Coverage000 (proof part of coverage017).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0270__4

namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage017_part_00 {a z : ℝ} (ha : Bounds (211/1000) (219/1000) a)
    (hz : Bounds (1/1000) (1/100) z) (h0 : a≤(43/200:ℝ)) (h1 : a≤(213/1000:ℝ)) (h2 : a≤(53/250:ℝ)) :
    0<curvature a (a*z) := by
  by_cases h3 : a≤(423/2000:ℝ)
  · exact Cell0272.curvature_pos ⟨ha.1,h3⟩ hz
  · exact Cell0273.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz

end GeneralCK.Certificates.ReflectionMidpointFamily


