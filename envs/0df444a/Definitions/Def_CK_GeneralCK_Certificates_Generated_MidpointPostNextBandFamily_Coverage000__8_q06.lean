-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q06
-- name    : CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T12:57:41.897987+00:00
-- url     : https://prove2.me/theorems/483fe6bf-3b5a-4f47-b70b-89dcee7e3b47
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, …
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage007) (piece 7 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage007) (piece 7 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage007) (piece 7 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage000 (+7 modules: GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage001, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage002, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage003, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage004, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage005, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage006, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage007) (piece 7 of 8).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0096__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0098__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0101__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0104__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0108__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0110__2

-- ===== source module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage006 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage006 {a z : ℝ} (ha : Bounds (1579/10000) (319/2000) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (1587/10000:ℝ)
  · by_cases h1 : a ≤ (1583/10000:ℝ)
    · by_cases h2 : a ≤ (1581/10000:ℝ)
      · by_cases h3 : a ≤ (79/500:ℝ)
        · exact Cell0096.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0097.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (791/5000:ℝ)
        · exact Cell0098.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0099.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (317/2000:ℝ)
      · by_cases h6 : a ≤ (99/625:ℝ)
        · exact Cell0100.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0101.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (793/5000:ℝ)
        · exact Cell0102.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0103.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (1591/10000:ℝ)
    · by_cases h9 : a ≤ (1589/10000:ℝ)
      · by_cases h10 : a ≤ (397/2500:ℝ)
        · exact Cell0104.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0105.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (159/1000:ℝ)
        · exact Cell0106.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0107.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (1593/10000:ℝ)
      · by_cases h13 : a ≤ (199/1250:ℝ)
        · exact Cell0108.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0109.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (797/5000:ℝ)
        · exact Cell0110.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0111.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

end


