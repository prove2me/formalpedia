-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage000__31_q15
-- name    : CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage000__31_q15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T20:58:03.874261+00:00
-- url     : https://prove2.me/theorems/c65989cb-53ea-4de4-9664-55d156726492
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage001, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage030) (piece 16 of 31)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage030) (piece 16 of 31)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage030) (piece 16 of 31) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage000 (+30 modules: GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage001, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage002, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage003, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage004, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage005, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage006, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage007, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage008, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage009, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage010, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage011, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage012, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage013, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage014, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage015, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage016, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage017, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage018, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage019, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage020, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage021, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage022, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage023, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage024, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage025, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage026, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage027, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage028, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage029, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage030) (piece 16 of 31).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage000__31_q14
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0240__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0244__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0248__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0251__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0255__4

-- ===== source module GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage015 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage015 {a z : ℝ} (ha : Bounds (44/125) (239/500) a)
    (hz : Bounds (1/20) (81/1000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (401/1000:ℝ)
  · by_cases h1 : a ≤ (187/500:ℝ)
    · by_cases h2 : a ≤ (181/500:ℝ)
      · by_cases h3 : a ≤ (357/1000:ℝ)
        · exact Cell0240.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0241.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (46/125:ℝ)
        · exact Cell0242.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0243.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (387/1000:ℝ)
      · by_cases h6 : a ≤ (19/50:ℝ)
        · exact Cell0244.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0245.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (197/500:ℝ)
        · exact Cell0246.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0247.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (87/200:ℝ)
    · by_cases h9 : a ≤ (417/1000:ℝ)
      · by_cases h10 : a ≤ (409/1000:ℝ)
        · exact Cell0248.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0249.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (213/500:ℝ)
        · exact Cell0250.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0251.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (91/200:ℝ)
      · by_cases h13 : a ≤ (89/200:ℝ)
        · exact Cell0252.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0253.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (233/500:ℝ)
        · exact Cell0254.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0255.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

end


