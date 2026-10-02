-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage040__13_q07
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage040__13_q07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T23:29:43.363309+00:00
-- url     : https://prove2.me/theorems/656a39aa-30ba-446f-967e-47dc444e3e8d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage040 (+12 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage041, GeneralCK.Certi…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage040 (+12 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage052) (piece 8 of 13)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage040 (+12 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage052) (piece 8 of 13)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage040 (+12 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage052) (piece 8 of 13) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage040 (+12 modules: GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage041, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage042, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage043, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage044, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage045, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage046, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage047, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage048, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage049, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage050, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage051, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage052) (piece 8 of 13).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage040__13_q06
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0751__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0754__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0758__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0762__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0766__4

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage047 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage047 {a z : ℝ} (ha : Bounds (88/125) (92/125) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(18/25:ℝ)
  · by_cases h1 : a≤(89/125:ℝ)
    · by_cases h2 : a≤(177/250:ℝ)
      · by_cases h3 : a≤(353/500:ℝ)
        · exact Cell0752.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0753.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(71/100:ℝ)
        · exact Cell0754.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0755.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(179/250:ℝ)
      · by_cases h6 : a≤(357/500:ℝ)
        · exact Cell0756.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0757.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(359/500:ℝ)
        · exact Cell0758.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0759.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(91/125:ℝ)
    · by_cases h9 : a≤(181/250:ℝ)
      · by_cases h10 : a≤(361/500:ℝ)
        · exact Cell0760.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0761.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(363/500:ℝ)
        · exact Cell0762.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0763.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(183/250:ℝ)
      · by_cases h13 : a≤(73/100:ℝ)
        · exact Cell0764.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0765.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(367/500:ℝ)
        · exact Cell0766.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0767.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

end


