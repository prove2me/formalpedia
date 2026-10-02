-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q03_c04
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q03_c04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T20:53:36.172221+00:00
-- url     : https://prove2.me/theorems/db05303f-f2fd-4380-93eb-8f6b0a302f30
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (proof part of coverage022)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (proof part of coverage022)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (proof part of coverage022)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (proof part of coverage022) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage019 (proof part of coverage022).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0359__4

namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000

theorem coverage022_part_04 {a z : ℝ} (ha : Bounds (251/1000) (259/1000) a)
    (hz : Bounds (1/100) (1/20) z) (h0 : ¬ (a≤(51/200:ℝ))) (h8 : a≤(257/1000:ℝ)) (h9 : a≤(32/125:ℝ)) :
    0<curvature a (a*z) := by
  by_cases h10 : a≤(511/2000:ℝ)
  · exact Cell0360.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
  · exact Cell0361.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz

end GeneralCK.Certificates.ReflectionMidpointNextFamily


