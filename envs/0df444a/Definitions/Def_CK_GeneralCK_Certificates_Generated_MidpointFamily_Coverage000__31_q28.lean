-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_q28
-- name    : CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_q28
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T03:47:15.452493+00:00
-- url     : https://prove2.me/theorems/b7c71782-986f-44b5-9e29-9c8b26e7b56b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage001, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointFamily.Coverage030) (piece 29 of 31)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointFamily.Coverage030) (piece 29 of 31)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointFamily.Coverage030) (piece 29 of 31) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointFamily/Coverage000 (+30 modules: GeneralCK/Certificates/Generated/MidpointFamily/Coverage001, GeneralCK/Certificates/Generated/MidpointFamily/Coverage002, GeneralCK/Certificates/Generated/MidpointFamily/Coverage003, GeneralCK/Certificates/Generated/MidpointFamily/Coverage004, GeneralCK/Certificates/Generated/MidpointFamily/Coverage005, GeneralCK/Certificates/Generated/MidpointFamily/Coverage006, GeneralCK/Certificates/Generated/MidpointFamily/Coverage007, GeneralCK/Certificates/Generated/MidpointFamily/Coverage008, GeneralCK/Certificates/Generated/MidpointFamily/Coverage009, GeneralCK/Certificates/Generated/MidpointFamily/Coverage010, GeneralCK/Certificates/Generated/MidpointFamily/Coverage011, GeneralCK/Certificates/Generated/MidpointFamily/Coverage012, GeneralCK/Certificates/Generated/MidpointFamily/Coverage013, GeneralCK/Certificates/Generated/MidpointFamily/Coverage014, GeneralCK/Certificates/Generated/MidpointFamily/Coverage015, GeneralCK/Certificates/Generated/MidpointFamily/Coverage016, GeneralCK/Certificates/Generated/MidpointFamily/Coverage017, GeneralCK/Certificates/Generated/MidpointFamily/Coverage018, GeneralCK/Certificates/Generated/MidpointFamily/Coverage019, GeneralCK/Certificates/Generated/MidpointFamily/Coverage020, GeneralCK/Certificates/Generated/MidpointFamily/Coverage021, GeneralCK/Certificates/Generated/MidpointFamily/Coverage022, GeneralCK/Certificates/Generated/MidpointFamily/Coverage023, GeneralCK/Certificates/Generated/MidpointFamily/Coverage024, GeneralCK/Certificates/Generated/MidpointFamily/Coverage025, GeneralCK/Certificates/Generated/MidpointFamily/Coverage026, GeneralCK/Certificates/Generated/MidpointFamily/Coverage027, GeneralCK/Certificates/Generated/MidpointFamily/Coverage028, GeneralCK/Certificates/Generated/MidpointFamily/Coverage029, GeneralCK/Certificates/Generated/MidpointFamily/Coverage030) (piece 29 of 31).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage000__31_q27
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0445__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0449__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0452__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0455__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0459__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0463__3

-- ===== source module GeneralCK.Certificates.Generated.MidpointFamily.Coverage028 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage028 {a z : ℝ} (ha : Bounds (299/1000) (157/500) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(153/500:ℝ)
  · by_cases h1 : a≤(151/500:ℝ)
    · by_cases h2 : a≤(3/10:ℝ)
      · by_cases h3 : a≤(599/2000:ℝ)
        · exact Cell0448.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0449.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(301/1000:ℝ)
        · exact Cell0450.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0451.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(38/125:ℝ)
      · by_cases h6 : a≤(303/1000:ℝ)
        · exact Cell0452.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0453.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(61/200:ℝ)
        · exact Cell0454.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0455.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(31/100:ℝ)
    · by_cases h9 : a≤(77/250:ℝ)
      · by_cases h10 : a≤(307/1000:ℝ)
        · exact Cell0456.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0457.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(309/1000:ℝ)
        · exact Cell0458.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0459.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(39/125:ℝ)
      · by_cases h13 : a≤(311/1000:ℝ)
        · exact Cell0460.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0461.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(313/1000:ℝ)
        · exact Cell0462.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0463.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

end


