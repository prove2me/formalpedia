-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage031__23_q03
-- name    : CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage031__23_q03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:41:07.829542+00:00
-- url     : https://prove2.me/theorems/5be53687-de71-4cbf-9854-c0e07de0c433
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage032, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage032, GeneralCK.Certificates.Generated.MidpointFamily.Coverage033, GeneralCK.Certificates.Generated.MidpointFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointFamily.Coverage039, GeneralCK.Certificates.Generated.MidpointFamily.Coverage040, GeneralCK.Certificates.Generated.MidpointFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointFamily.Coverage052, GeneralCK.Certificates.Generated.MidpointFamily.Coverage053) (piece 4 of 23)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage032, GeneralCK.Certificates.Generated.MidpointFamily.Coverage033, GeneralCK.Certificates.Generated.MidpointFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointFamily.Coverage039, GeneralCK.Certificates.Generated.MidpointFamily.Coverage040, GeneralCK.Certificates.Generated.MidpointFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointFamily.Coverage052, GeneralCK.Certificates.Generated.MidpointFamily.Coverage053) (piece 4 of 23)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage032, GeneralCK.Certificates.Generated.MidpointFamily.Coverage033, GeneralCK.Certificates.Generated.MidpointFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointFamily.Coverage039, GeneralCK.Certificates.Generated.MidpointFamily.Coverage040, GeneralCK.Certificates.Generated.MidpointFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointFamily.Coverage052, GeneralCK.Certificates.Generated.MidpointFamily.Coverage053) (piece 4 of 23) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointFamily/Coverage031 (+22 modules: GeneralCK/Certificates/Generated/MidpointFamily/Coverage032, GeneralCK/Certificates/Generated/MidpointFamily/Coverage033, GeneralCK/Certificates/Generated/MidpointFamily/Coverage034, GeneralCK/Certificates/Generated/MidpointFamily/Coverage035, GeneralCK/Certificates/Generated/MidpointFamily/Coverage036, GeneralCK/Certificates/Generated/MidpointFamily/Coverage037, GeneralCK/Certificates/Generated/MidpointFamily/Coverage038, GeneralCK/Certificates/Generated/MidpointFamily/Coverage039, GeneralCK/Certificates/Generated/MidpointFamily/Coverage040, GeneralCK/Certificates/Generated/MidpointFamily/Coverage041, GeneralCK/Certificates/Generated/MidpointFamily/Coverage042, GeneralCK/Certificates/Generated/MidpointFamily/Coverage043, GeneralCK/Certificates/Generated/MidpointFamily/Coverage044, GeneralCK/Certificates/Generated/MidpointFamily/Coverage045, GeneralCK/Certificates/Generated/MidpointFamily/Coverage046, GeneralCK/Certificates/Generated/MidpointFamily/Coverage047, GeneralCK/Certificates/Generated/MidpointFamily/Coverage048, GeneralCK/Certificates/Generated/MidpointFamily/Coverage049, GeneralCK/Certificates/Generated/MidpointFamily/Coverage050, GeneralCK/Certificates/Generated/MidpointFamily/Coverage051, GeneralCK/Certificates/Generated/MidpointFamily/Coverage052, GeneralCK/Certificates/Generated/MidpointFamily/Coverage053) (piece 4 of 23).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage031__23_q02
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0543__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0547__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0551__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0555__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0558__4

-- ===== source module GeneralCK.Certificates.Generated.MidpointFamily.Coverage034 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage034 {a z : ℝ} (ha : Bounds (197/500) (41/100) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
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
end GeneralCK.Certificates.ReflectionMidpointFamily

end


