-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q10
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T05:14:15.672473+00:00
-- url     : https://prove2.me/theorems/fd290801-0d16-424c-bcca-7d6bca2315e5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (+18 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage001, GeneralCK.Certi…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (+18 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage018) (piece 11 of 19)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (+18 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage018) (piece 11 of 19)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage000 (+18 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage018) (piece 11 of 19) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage000 (+18 modules: GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage001, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage002, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage003, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage004, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage005, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage006, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage007, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage008, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage009, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage010, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage011, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage012, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage013, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage014, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage015, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage016, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage017, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage018) (piece 11 of 19).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q09
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q10_c00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q10_c01
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q10_c02
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q10_c03
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q10_c04
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q10_c05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q10_c06
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage000__19_q10_c07

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage010 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage010 {a z : ℝ} (ha : Bounds (91/500) (463/2500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(459/2500:ℝ)
  · by_cases h1 : a≤(457/2500:ℝ)
    · by_cases h2 : a≤(114/625:ℝ)
      · exact coverage010_part_00 ha hz h0 h1 h2
      · exact coverage010_part_01 ha hz h0 h1 h2
    · by_cases h5 : a≤(229/1250:ℝ)
      · exact coverage010_part_02 ha hz h0 h1 h5
      · exact coverage010_part_03 ha hz h0 h1 h5
  · by_cases h8 : a≤(461/2500:ℝ)
    · by_cases h9 : a≤(23/125:ℝ)
      · exact coverage010_part_04 ha hz h0 h8 h9
      · exact coverage010_part_05 ha hz h0 h8 h9
    · by_cases h12 : a≤(231/1250:ℝ)
      · exact coverage010_part_06 ha hz h0 h8 h12
      · exact coverage010_part_07 ha hz h0 h8 h12
end GeneralCK.Certificates.ReflectionMidpointNextFamily

end


