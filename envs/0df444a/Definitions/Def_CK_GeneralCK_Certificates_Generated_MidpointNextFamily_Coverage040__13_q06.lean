-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage040__13_q06
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage040__13_q06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:58:47.108989+00:00
-- url     : https://prove2.me/theorems/1077e1b6-49e4-4f20-93c3-9f7313bec35c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage040 (+12 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage041, GeneralCK.Certi…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage040 (+12 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage052) (piece 7 of 13)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage040 (+12 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage052) (piece 7 of 13)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage040 (+12 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage052) (piece 7 of 13) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage040 (+12 modules: GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage041, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage042, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage043, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage044, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage045, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage046, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage047, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage048, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage049, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage050, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage051, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage052) (piece 7 of 13).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage040__13_q05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0733__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0737__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0740__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0744__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0748__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0751__3

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage046 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage046 {a z : ℝ} (ha : Bounds (84/125) (88/125) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(86/125:ℝ)
  · by_cases h1 : a≤(17/25:ℝ)
    · by_cases h2 : a≤(169/250:ℝ)
      · by_cases h3 : a≤(337/500:ℝ)
        · exact Cell0736.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0737.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(339/500:ℝ)
        · exact Cell0738.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0739.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(171/250:ℝ)
      · by_cases h6 : a≤(341/500:ℝ)
        · exact Cell0740.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0741.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(343/500:ℝ)
        · exact Cell0742.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0743.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(87/125:ℝ)
    · by_cases h9 : a≤(173/250:ℝ)
      · by_cases h10 : a≤(69/100:ℝ)
        · exact Cell0744.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0745.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(347/500:ℝ)
        · exact Cell0746.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0747.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(7/10:ℝ)
      · by_cases h13 : a≤(349/500:ℝ)
        · exact Cell0748.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0749.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(351/500:ℝ)
        · exact Cell0750.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0751.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

end


