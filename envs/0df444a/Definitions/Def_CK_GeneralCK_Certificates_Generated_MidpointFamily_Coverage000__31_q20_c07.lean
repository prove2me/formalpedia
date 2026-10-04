-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_q20_c07
-- name    : CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_q20_c07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T17:25:31.630121+00:00
-- url     : https://prove2.me/theorems/a0d5c0d2-617e-4525-bc03-2894789935cf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage020)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage020)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage020)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (proof part of coverage020) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointFamily/Coverage000 (proof part of coverage020).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0332__4

namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage020_part_07 {a z : ℝ} (ha : Bounds (47/200) (243/1000) a)
    (hz : Bounds (1/1000) (1/100) z) (h0 : ¬ (a≤(239/1000:ℝ))) (h8 : ¬ (a≤(241/1000:ℝ))) (h12 : ¬ (a≤(121/500:ℝ))) :
    0<curvature a (a*z) := by
  by_cases h14 : a≤(97/400:ℝ)
  · exact Cell0334.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
  · exact Cell0335.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz

end GeneralCK.Certificates.ReflectionMidpointFamily


