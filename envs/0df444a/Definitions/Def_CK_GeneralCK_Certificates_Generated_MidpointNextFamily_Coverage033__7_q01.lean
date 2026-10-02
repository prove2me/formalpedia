-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage033__7_q01
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage033__7_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T19:04:18.772465+00:00
-- url     : https://prove2.me/theorems/27860074-ba61-4de4-9053-49ec40d2e01b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certif…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage039) (piece 2 of 7)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage039) (piece 2 of 7)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage033 (+6 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage039) (piece 2 of 7) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage033 (+6 modules: GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage034, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage035, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage036, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage037, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage038, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage039) (piece 2 of 7).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage033__7_q00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0543__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0546__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0549__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0553__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0556__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0559__3

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage034 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage034 {a z : ℝ} (ha : Bounds (197/500) (41/100) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(201/500:ℝ)
  · by_cases h1 : a≤(199/500:ℝ)
    · by_cases h2 : a≤(99/250:ℝ)
      · by_cases h3 : a≤(79/200:ℝ)
        · exact Cell0544.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0545.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(397/1000:ℝ)
        · exact Cell0546.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0547.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(2/5:ℝ)
      · by_cases h6 : a≤(399/1000:ℝ)
        · exact Cell0548.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0549.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(401/1000:ℝ)
        · exact Cell0550.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0551.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(203/500:ℝ)
    · by_cases h9 : a≤(101/250:ℝ)
      · by_cases h10 : a≤(403/1000:ℝ)
        · exact Cell0552.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0553.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(81/200:ℝ)
        · exact Cell0554.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0555.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(51/125:ℝ)
      · by_cases h13 : a≤(407/1000:ℝ)
        · exact Cell0556.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0557.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(409/1000:ℝ)
        · exact Cell0558.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0559.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

end


