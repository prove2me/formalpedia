-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage040__13_q04
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage040__13_q04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:07:20.735879+00:00
-- url     : https://prove2.me/theorems/5d6d10ff-24e2-4cbe-8bbf-d129a7780560
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage040 (+12 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage041, GeneralCK.Certi…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage040 (+12 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage052) (piece 5 of 13)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage040 (+12 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage052) (piece 5 of 13)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage040 (+12 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage052) (piece 5 of 13) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage040 (+12 modules: GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage041, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage042, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage043, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage044, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage045, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage046, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage047, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage048, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage049, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage050, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage051, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage052) (piece 5 of 13).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage040__13_q03
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0701__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0705__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0709__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0712__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0715__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0718__3

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage044 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage044 {a z : ℝ} (ha : Bounds (76/125) (16/25) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(78/125:ℝ)
  · by_cases h1 : a≤(77/125:ℝ)
    · by_cases h2 : a≤(153/250:ℝ)
      · by_cases h3 : a≤(61/100:ℝ)
        · exact Cell0704.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0705.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(307/500:ℝ)
        · exact Cell0706.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0707.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(31/50:ℝ)
      · by_cases h6 : a≤(309/500:ℝ)
        · exact Cell0708.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0709.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(311/500:ℝ)
        · exact Cell0710.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0711.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(79/125:ℝ)
    · by_cases h9 : a≤(157/250:ℝ)
      · by_cases h10 : a≤(313/500:ℝ)
        · exact Cell0712.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0713.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(63/100:ℝ)
        · exact Cell0714.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0715.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(159/250:ℝ)
      · by_cases h13 : a≤(317/500:ℝ)
        · exact Cell0716.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0717.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(319/500:ℝ)
        · exact Cell0718.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0719.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

end


