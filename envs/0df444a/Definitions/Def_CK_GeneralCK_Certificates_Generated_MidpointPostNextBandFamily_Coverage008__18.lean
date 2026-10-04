-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18
-- name    : CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T00:59:05.45841+00:00
-- url     : https://prove2.me/theorems/37f3a3b6-59d7-4705-8de5-558f1c360ad3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (+17 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage009,…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (+17 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage025)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (+17 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage025)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (+17 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage025) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage008 (+17 modules: GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage009, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage010, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage011, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage012, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage013, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage014, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage015, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage016, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage017, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage018, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage019, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage020, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage021, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage022, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage023, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage024, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage025).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q16
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_c00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_c01
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_c02
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_c03
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_c04
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_c05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_c06
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_c07

-- ===== source module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage025 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage025 {a z : ℝ} (ha : Bounds (82/125) (999/1000) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (83/100:ℝ)
  · by_cases h1 : a ≤ (367/500:ℝ)
    · by_cases h2 : a ≤ (17/25:ℝ)
      · exact coverage025_part_00 ha hz h0 h1 h2
      · exact coverage025_part_01 ha hz h0 h1 h2
    · by_cases h4 : a ≤ (191/250:ℝ)
      · exact coverage025_part_02 ha hz h0 h1 h4
      · exact coverage025_part_03 ha hz h0 h1 h4
  · by_cases h6 : a ≤ (47/50:ℝ)
    · by_cases h7 : a ≤ (173/200:ℝ)
      · exact coverage025_part_04 ha hz h0 h6 h7
      · exact coverage025_part_05 ha hz h0 h6 h7
    · by_cases h9 : a ≤ (489/500:ℝ)
      · exact coverage025_part_06 ha hz h0 h6 h9
      · exact coverage025_part_07 ha hz h0 h6 h9
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

end


