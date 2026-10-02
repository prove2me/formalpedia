-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_q04
-- name    : CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_q04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:24:08.090272+00:00
-- url     : https://prove2.me/theorems/593c1458-41ff-4794-b6c7-8ed82ca8058c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage001, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointFamily.Coverage030) (piece 5 of 31)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointFamily.Coverage030) (piece 5 of 31)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointFamily.Coverage030) (piece 5 of 31) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointFamily/Coverage000 (+30 modules: GeneralCK/Certificates/Generated/MidpointFamily/Coverage001, GeneralCK/Certificates/Generated/MidpointFamily/Coverage002, GeneralCK/Certificates/Generated/MidpointFamily/Coverage003, GeneralCK/Certificates/Generated/MidpointFamily/Coverage004, GeneralCK/Certificates/Generated/MidpointFamily/Coverage005, GeneralCK/Certificates/Generated/MidpointFamily/Coverage006, GeneralCK/Certificates/Generated/MidpointFamily/Coverage007, GeneralCK/Certificates/Generated/MidpointFamily/Coverage008, GeneralCK/Certificates/Generated/MidpointFamily/Coverage009, GeneralCK/Certificates/Generated/MidpointFamily/Coverage010, GeneralCK/Certificates/Generated/MidpointFamily/Coverage011, GeneralCK/Certificates/Generated/MidpointFamily/Coverage012, GeneralCK/Certificates/Generated/MidpointFamily/Coverage013, GeneralCK/Certificates/Generated/MidpointFamily/Coverage014, GeneralCK/Certificates/Generated/MidpointFamily/Coverage015, GeneralCK/Certificates/Generated/MidpointFamily/Coverage016, GeneralCK/Certificates/Generated/MidpointFamily/Coverage017, GeneralCK/Certificates/Generated/MidpointFamily/Coverage018, GeneralCK/Certificates/Generated/MidpointFamily/Coverage019, GeneralCK/Certificates/Generated/MidpointFamily/Coverage020, GeneralCK/Certificates/Generated/MidpointFamily/Coverage021, GeneralCK/Certificates/Generated/MidpointFamily/Coverage022, GeneralCK/Certificates/Generated/MidpointFamily/Coverage023, GeneralCK/Certificates/Generated/MidpointFamily/Coverage024, GeneralCK/Certificates/Generated/MidpointFamily/Coverage025, GeneralCK/Certificates/Generated/MidpointFamily/Coverage026, GeneralCK/Certificates/Generated/MidpointFamily/Coverage027, GeneralCK/Certificates/Generated/MidpointFamily/Coverage028, GeneralCK/Certificates/Generated/MidpointFamily/Coverage029, GeneralCK/Certificates/Generated/MidpointFamily/Coverage030) (piece 5 of 31).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_q03
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0061__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0065__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0069__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0073__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0075__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0079__3

-- ===== source module GeneralCK.Certificates.Generated.MidpointFamily.Coverage004 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage004 {a z : ℝ} (ha : Bounds (407/2500) (83/500) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(411/2500:ℝ)
  · by_cases h1 : a≤(409/2500:ℝ)
    · by_cases h2 : a≤(102/625:ℝ)
      · by_cases h3 : a≤(163/1000:ℝ)
        · exact Cell0064.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0065.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(817/5000:ℝ)
        · exact Cell0066.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0067.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(41/250:ℝ)
      · by_cases h6 : a≤(819/5000:ℝ)
        · exact Cell0068.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0069.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(821/5000:ℝ)
        · exact Cell0070.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0071.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(413/2500:ℝ)
    · by_cases h9 : a≤(103/625:ℝ)
      · by_cases h10 : a≤(823/5000:ℝ)
        · exact Cell0072.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0073.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(33/200:ℝ)
        · exact Cell0074.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0075.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(207/1250:ℝ)
      · by_cases h13 : a≤(827/5000:ℝ)
        · exact Cell0076.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0077.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(829/5000:ℝ)
        · exact Cell0078.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0079.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

end


