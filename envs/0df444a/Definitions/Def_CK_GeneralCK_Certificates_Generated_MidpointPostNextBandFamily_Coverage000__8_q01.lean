-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q01
-- name    : CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T09:18:48.861285+00:00
-- url     : https://prove2.me/theorems/21bcada2-f5c4-4900-ad08-7e53c8dcbf68
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, …
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage007) (piece 2 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage007) (piece 2 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage007) (piece 2 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage000 (+7 modules: GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage001, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage002, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage003, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage004, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage005, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage006, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage007) (piece 2 of 8).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0014__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0018__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0022__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0026__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0029__4

-- ===== source module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage001 {a z : ℝ} (ha : Bounds (377/2500) (379/2500) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (189/1250:ℝ)
  · by_cases h1 : a ≤ (151/1000:ℝ)
    · by_cases h2 : a ≤ (1509/10000:ℝ)
      · by_cases h3 : a ≤ (3017/20000:ℝ)
        · exact Cell0016.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0017.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (3019/20000:ℝ)
        · exact Cell0018.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0019.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (1511/10000:ℝ)
      · by_cases h6 : a ≤ (3021/20000:ℝ)
        · exact Cell0020.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0021.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (3023/20000:ℝ)
        · exact Cell0022.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0023.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (757/5000:ℝ)
    · by_cases h9 : a ≤ (1513/10000:ℝ)
      · by_cases h10 : a ≤ (121/800:ℝ)
        · exact Cell0024.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0025.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (3027/20000:ℝ)
        · exact Cell0026.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0027.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (303/2000:ℝ)
      · by_cases h13 : a ≤ (3029/20000:ℝ)
        · exact Cell0028.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0029.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (3031/20000:ℝ)
        · exact Cell0030.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0031.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

end


