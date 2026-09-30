-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage053
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage053
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:20:15.456782+00:00
-- url     : https://prove2.me/theorems/a32260c4-7a99-4c9e-95ba-2f7ebaa0c3d5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage053` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage053` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage053` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage053 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage053.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0846__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0849__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0852__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0855__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0857__2

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage053 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage053 {a z : ℝ} (ha : Bounds (493/500) (999/1000) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(993/1000:ℝ)
  · by_cases h1 : a≤(99/100:ℝ)
    · by_cases h2 : a≤(247/250:ℝ)
      · exact Cell0848.curvature_pos ⟨ha.1,h2⟩ hz
      · exact Cell0849.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h1⟩ hz
    · by_cases h3 : a≤(991/1000:ℝ)
      · exact Cell0850.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h3⟩ hz
      · by_cases h4 : a≤(124/125:ℝ)
        · exact Cell0851.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h4⟩ hz
        · exact Cell0852.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h0⟩ hz
  · by_cases h5 : a≤(249/250:ℝ)
    · by_cases h6 : a≤(497/500:ℝ)
      · exact Cell0853.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h6⟩ hz
      · by_cases h7 : a≤(199/200:ℝ)
        · exact Cell0854.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h7⟩ hz
        · exact Cell0855.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h5⟩ hz
    · by_cases h8 : a≤(997/1000:ℝ)
      · exact Cell0856.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h8⟩ hz
      · by_cases h9 : a≤(499/500:ℝ)
        · exact Cell0857.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h9⟩ hz
        · exact Cell0858.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

end


