-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q06
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T23:11:24.176822+00:00
-- url     : https://prove2.me/theorems/c38dbc35-7874-4da6-bd93-d74c2a0f3d5d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (+15 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage001, General…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (+15 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage015) (piece 7 of 16)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (+15 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage015) (piece 7 of 16)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (+15 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage015) (piece 7 of 16) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage000 (+15 modules: GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage001, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage002, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage003, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage004, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage005, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage006, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage007, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage008, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage009, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage010, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage011, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage012, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage013, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage014, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage015) (piece 7 of 16).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0094__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0098__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0101__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0105__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0109__4

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage006 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage006 {a z : ℝ} (ha : Bounds (399/2500) (407/2500) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (403/2500:ℝ)
  · by_cases h1 : a ≤ (401/2500:ℝ)
    · by_cases h2 : a ≤ (4/25:ℝ)
      · by_cases h3 : a ≤ (799/5000:ℝ)
        · exact Cell0096.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0097.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (801/5000:ℝ)
        · exact Cell0098.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0099.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (201/1250:ℝ)
      · by_cases h6 : a ≤ (803/5000:ℝ)
        · exact Cell0100.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0101.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (161/1000:ℝ)
        · exact Cell0102.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0103.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (81/500:ℝ)
    · by_cases h9 : a ≤ (101/625:ℝ)
      · by_cases h10 : a ≤ (807/5000:ℝ)
        · exact Cell0104.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0105.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (809/5000:ℝ)
        · exact Cell0106.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0107.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (203/1250:ℝ)
      · by_cases h13 : a ≤ (811/5000:ℝ)
        · exact Cell0108.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0109.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (813/5000:ℝ)
        · exact Cell0110.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0111.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

end


