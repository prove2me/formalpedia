-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q10_c07
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q10_c07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T03:05:14.082986+00:00
-- url     : https://prove2.me/theorems/f6e9108b-d3ed-41bb-89f6-fe839d28607d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (proof part of coverage029)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (proof part of coverage029)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (proof part of coverage029)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (proof part of coverage029) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage019 (proof part of coverage029).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0478__4

namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage029_part_07 {a z : ℝ} (ha : Bounds (157/500) (33/100) a)
    (hz : Bounds (1/100) (1/20) z) (h0 : ¬ (a≤(161/500:ℝ))) (h8 : ¬ (a≤(163/500:ℝ))) (h12 : ¬ (a≤(41/125:ℝ))) :
    0<curvature a (a*z) := by
  by_cases h14 : a≤(329/1000:ℝ)
  · exact Cell0478.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
  · exact Cell0479.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz

end GeneralCK.Certificates.ReflectionMidpointNextFamily


