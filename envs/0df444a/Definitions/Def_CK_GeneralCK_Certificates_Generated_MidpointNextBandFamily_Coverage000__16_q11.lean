-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q11
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T05:29:54.458877+00:00
-- url     : https://prove2.me/theorems/e8aed57c-9658-4ae7-992c-41771e1093eb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (+15 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage001, General…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (+15 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage015) (piece 12 of 16)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (+15 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage015) (piece 12 of 16)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000 (+15 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage007, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage008, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage015) (piece 12 of 16) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage000 (+15 modules: GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage001, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage002, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage003, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage004, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage005, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage006, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage007, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage008, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage009, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage010, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage011, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage012, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage013, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage014, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage015) (piece 12 of 16).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q10
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q11_c00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q11_c01
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q11_c02
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q11_c03
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q11_c04
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q11_c05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q11_c06
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage000__16_q11_c07

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage011 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage011 {a z : ℝ} (ha : Bounds (439/2500) (113/625) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (111/625:ℝ)
  · by_cases h1 : a ≤ (441/2500:ℝ)
    · by_cases h2 : a ≤ (22/125:ℝ)
      · exact coverage011_part_00 ha hz h0 h1 h2
      · exact coverage011_part_01 ha hz h0 h1 h2
    · by_cases h5 : a ≤ (221/1250:ℝ)
      · exact coverage011_part_02 ha hz h0 h1 h5
      · exact coverage011_part_03 ha hz h0 h1 h5
  · by_cases h8 : a ≤ (112/625:ℝ)
    · by_cases h9 : a ≤ (223/1250:ℝ)
      · exact coverage011_part_04 ha hz h0 h8 h9
      · exact coverage011_part_05 ha hz h0 h8 h9
    · by_cases h12 : a ≤ (9/50:ℝ)
      · exact coverage011_part_06 ha hz h0 h8 h12
      · exact coverage011_part_07 ha hz h0 h8 h12
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

end


