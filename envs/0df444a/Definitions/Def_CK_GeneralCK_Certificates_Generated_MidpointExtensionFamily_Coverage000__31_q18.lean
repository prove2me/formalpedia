-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage000__31_q18
-- name    : CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage000__31_q18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:41:31.006263+00:00
-- url     : https://prove2.me/theorems/21a547b7-15c4-4883-8eb0-18823738a8ae
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage001, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage030) (piece 19 of 31)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage030) (piece 19 of 31)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000 (+30 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage030) (piece 19 of 31) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage000 (+30 modules: GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage001, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage002, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage003, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage004, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage005, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage006, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage007, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage008, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage009, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage010, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage011, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage012, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage013, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage014, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage015, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage016, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage017, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage018, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage019, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage020, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage021, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage022, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage023, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage024, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage025, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage026, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage027, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage028, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage029, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage030) (piece 19 of 31).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage000__31_q17
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0275__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0279__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0283__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0287__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0291__4

-- ===== source module GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage018 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage018 {a z : ℝ} (ha : Bounds (3/20) (763/5000) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (151/1000:ℝ)
  · by_cases h1 : a ≤ (94/625:ℝ)
    · by_cases h2 : a ≤ (751/5000:ℝ)
      · by_cases h3 : a ≤ (1501/10000:ℝ)
        · exact Cell0278.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0279.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (1503/10000:ℝ)
        · exact Cell0280.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0281.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (753/5000:ℝ)
      · by_cases h6 : a ≤ (301/2000:ℝ)
        · exact Cell0282.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0283.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (377/2500:ℝ)
        · exact Cell0284.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0285.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (759/5000:ℝ)
    · by_cases h9 : a ≤ (757/5000:ℝ)
      · by_cases h10 : a ≤ (189/1250:ℝ)
        · exact Cell0286.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0287.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (379/2500:ℝ)
        · exact Cell0288.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0289.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (761/5000:ℝ)
      · by_cases h13 : a ≤ (19/125:ℝ)
        · exact Cell0290.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0291.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (381/2500:ℝ)
        · exact Cell0292.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0293.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

end


