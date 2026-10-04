-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8
-- name    : CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T13:16:02.217491+00:00
-- url     : https://prove2.me/theorems/dccf40a5-c9ef-4ceb-8722-91fa77110231
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, …
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage007)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage007)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage007) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage000 (+7 modules: GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage001, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage002, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage003, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage004, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage005, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage006, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage007).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q06
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0112__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0114__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0116__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0118__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0122__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0126
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0127

-- ===== source module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage007 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage007 {a z : ℝ} (ha : Bounds (319/2000) (1611/10000) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (1603/10000:ℝ)
  · by_cases h1 : a ≤ (1599/10000:ℝ)
    · by_cases h2 : a ≤ (1597/10000:ℝ)
      · by_cases h3 : a ≤ (399/2500:ℝ)
        · exact Cell0112.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0113.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (799/5000:ℝ)
        · exact Cell0114.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0115.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (1601/10000:ℝ)
      · by_cases h6 : a ≤ (4/25:ℝ)
        · exact Cell0116.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0117.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (801/5000:ℝ)
        · exact Cell0118.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0119.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (1607/10000:ℝ)
    · by_cases h9 : a ≤ (321/2000:ℝ)
      · by_cases h10 : a ≤ (401/2500:ℝ)
        · exact Cell0120.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0121.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (803/5000:ℝ)
        · exact Cell0122.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0123.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (1609/10000:ℝ)
      · by_cases h13 : a ≤ (201/1250:ℝ)
        · exact Cell0124.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0125.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (161/1000:ℝ)
        · exact Cell0126.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0127.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

end


