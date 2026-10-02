-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q00
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T18:46:55.253982+00:00
-- url     : https://prove2.me/theorems/0488836d-8bb4-4169-b9f8-ea469a771532
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (+18 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage001, GeneralCK.Certi…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (+18 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage018) (piece 1 of 19)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (+18 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage018) (piece 1 of 19)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (+18 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage018) (piece 1 of 19) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage000 (+18 modules: GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage001, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage002, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage003, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage004, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage005, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage006, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage007, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage008, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage009, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage010, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage011, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage012, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage013, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage014, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage015, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage016, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage017, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage018) (piece 1 of 19).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0000__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0004__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0008__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0012__4

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage000 {a z : ℝ} (ha : Bounds (3/20) (383/2500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(379/2500:ℝ)
  · by_cases h1 : a≤(377/2500:ℝ)
    · by_cases h2 : a≤(94/625:ℝ)
      · by_cases h3 : a≤(751/5000:ℝ)
        · exact Cell0000.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0001.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a≤(753/5000:ℝ)
        · exact Cell0002.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0003.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a≤(189/1250:ℝ)
      · by_cases h6 : a≤(151/1000:ℝ)
        · exact Cell0004.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0005.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a≤(757/5000:ℝ)
        · exact Cell0006.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0007.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a≤(381/2500:ℝ)
    · by_cases h9 : a≤(19/125:ℝ)
      · by_cases h10 : a≤(759/5000:ℝ)
        · exact Cell0008.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0009.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a≤(761/5000:ℝ)
        · exact Cell0010.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0011.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a≤(191/1250:ℝ)
      · by_cases h13 : a≤(763/5000:ℝ)
        · exact Cell0012.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0013.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a≤(153/1000:ℝ)
        · exact Cell0014.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0015.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextFamily

end


