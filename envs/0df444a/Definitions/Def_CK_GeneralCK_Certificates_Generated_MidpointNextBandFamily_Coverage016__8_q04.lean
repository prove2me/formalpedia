-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q04
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T01:46:38.888624+00:00
-- url     : https://prove2.me/theorems/d1400516-59f6-45db-98a5-4d1a3694a401
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralC…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage023) (piece 5 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage023) (piece 5 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage023) (piece 5 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage016 (+7 modules: GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage017, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage018, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage019, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage020, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage021, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage022, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage023) (piece 5 of 8).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q03
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0317__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0321__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0325__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0328__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0331__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0335__3

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage020 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage020 {a z : ℝ} (ha : Bounds (79/250) (393/1000) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (87/250:ℝ)
  · by_cases h1 : a ≤ (331/1000:ℝ)
    · by_cases h2 : a ≤ (323/1000:ℝ)
      · by_cases h3 : a ≤ (319/1000:ℝ)
        · exact Cell0320.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0321.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (327/1000:ℝ)
        · exact Cell0322.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0323.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (339/1000:ℝ)
      · by_cases h6 : a ≤ (67/200:ℝ)
        · exact Cell0324.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0325.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (343/1000:ℝ)
        · exact Cell0326.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0327.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (46/125:ℝ)
    · by_cases h9 : a ≤ (179/500:ℝ)
      · by_cases h10 : a ≤ (353/1000:ℝ)
        · exact Cell0328.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0329.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (363/1000:ℝ)
        · exact Cell0330.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0331.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (19/50:ℝ)
      · by_cases h13 : a ≤ (187/500:ℝ)
        · exact Cell0332.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0333.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (193/500:ℝ)
        · exact Cell0334.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0335.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

end


