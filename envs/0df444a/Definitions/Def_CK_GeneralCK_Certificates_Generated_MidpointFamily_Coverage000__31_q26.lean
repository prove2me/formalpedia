-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_q26
-- name    : CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_q26
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T02:58:42.789615+00:00
-- url     : https://prove2.me/theorems/c73f77f0-4dd1-44d3-ada9-070e1792be33
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage001, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointFamily.Coverage030) (piece 27 of 31)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointFamily.Coverage030) (piece 27 of 31)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointFamily.Coverage030) (piece 27 of 31) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointFamily/Coverage000 (+30 modules: GeneralCK/Certificates/Generated/MidpointFamily/Coverage001, GeneralCK/Certificates/Generated/MidpointFamily/Coverage002, GeneralCK/Certificates/Generated/MidpointFamily/Coverage003, GeneralCK/Certificates/Generated/MidpointFamily/Coverage004, GeneralCK/Certificates/Generated/MidpointFamily/Coverage005, GeneralCK/Certificates/Generated/MidpointFamily/Coverage006, GeneralCK/Certificates/Generated/MidpointFamily/Coverage007, GeneralCK/Certificates/Generated/MidpointFamily/Coverage008, GeneralCK/Certificates/Generated/MidpointFamily/Coverage009, GeneralCK/Certificates/Generated/MidpointFamily/Coverage010, GeneralCK/Certificates/Generated/MidpointFamily/Coverage011, GeneralCK/Certificates/Generated/MidpointFamily/Coverage012, GeneralCK/Certificates/Generated/MidpointFamily/Coverage013, GeneralCK/Certificates/Generated/MidpointFamily/Coverage014, GeneralCK/Certificates/Generated/MidpointFamily/Coverage015, GeneralCK/Certificates/Generated/MidpointFamily/Coverage016, GeneralCK/Certificates/Generated/MidpointFamily/Coverage017, GeneralCK/Certificates/Generated/MidpointFamily/Coverage018, GeneralCK/Certificates/Generated/MidpointFamily/Coverage019, GeneralCK/Certificates/Generated/MidpointFamily/Coverage020, GeneralCK/Certificates/Generated/MidpointFamily/Coverage021, GeneralCK/Certificates/Generated/MidpointFamily/Coverage022, GeneralCK/Certificates/Generated/MidpointFamily/Coverage023, GeneralCK/Certificates/Generated/MidpointFamily/Coverage024, GeneralCK/Certificates/Generated/MidpointFamily/Coverage025, GeneralCK/Certificates/Generated/MidpointFamily/Coverage026, GeneralCK/Certificates/Generated/MidpointFamily/Coverage027, GeneralCK/Certificates/Generated/MidpointFamily/Coverage028, GeneralCK/Certificates/Generated/MidpointFamily/Coverage029, GeneralCK/Certificates/Generated/MidpointFamily/Coverage030) (piece 27 of 31).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_q25
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0413__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0417__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0421__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0424__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0427__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0430__4

-- ===== source module GeneralCK.Certificates.Generated.MidpointFamily.Coverage026 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage026 {a z : ℝ} (ha : Bounds (283/1000) (291/1000) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(287/1000:ℝ)
  · by_cases h1 : a≤(57/200:ℝ)
    · by_cases h2 : a≤(71/250:ℝ)
      · by_cases h3 : a≤(567/2000:ℝ)
        · exact Cell0416.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0417.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(569/2000:ℝ)
        · exact Cell0418.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0419.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(143/500:ℝ)
      · by_cases h6 : a≤(571/2000:ℝ)
        · exact Cell0420.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0421.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(573/2000:ℝ)
        · exact Cell0422.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0423.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(289/1000:ℝ)
    · by_cases h9 : a≤(36/125:ℝ)
      · by_cases h10 : a≤(23/80:ℝ)
        · exact Cell0424.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0425.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(577/2000:ℝ)
        · exact Cell0426.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0427.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(29/100:ℝ)
      · by_cases h13 : a≤(579/2000:ℝ)
        · exact Cell0428.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0429.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(581/2000:ℝ)
        · exact Cell0430.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0431.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

end


