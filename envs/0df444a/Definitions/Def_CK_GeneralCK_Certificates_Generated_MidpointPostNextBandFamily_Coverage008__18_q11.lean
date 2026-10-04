-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q11
-- name    : CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T15:03:33.946767+00:00
-- url     : https://prove2.me/theorems/c0a17da3-b192-4f95-9c95-9aa6f75fbd13
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (+17 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage009,…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (+17 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage025) (piece 12 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (+17 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage025) (piece 12 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage008 (+17 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage009, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage010, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage011, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage012, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage013, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage014, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage015, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage016, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage025) (piece 12 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage008 (+17 modules: GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage009, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage010, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage011, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage012, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage013, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage014, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage015, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage016, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage017, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage018, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage019, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage020, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage021, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage022, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage023, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage024, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage025) (piece 12 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q10
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q11_c00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q11_c01
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q11_c02
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q11_c03
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q11_c04
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q11_c05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q11_c06
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage008__18_q11_c07

-- ===== source module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage019 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage019 {a z : ℝ} (ha : Bounds (109/500) (117/500) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (113/500:ℝ)
  · by_cases h1 : a ≤ (111/500:ℝ)
    · by_cases h2 : a ≤ (11/50:ℝ)
      · exact coverage019_part_00 ha hz h0 h1 h2
      · exact coverage019_part_01 ha hz h0 h1 h2
    · by_cases h5 : a ≤ (28/125:ℝ)
      · exact coverage019_part_02 ha hz h0 h1 h5
      · exact coverage019_part_03 ha hz h0 h1 h5
  · by_cases h8 : a ≤ (23/100:ℝ)
    · by_cases h9 : a ≤ (57/250:ℝ)
      · exact coverage019_part_04 ha hz h0 h8 h9
      · exact coverage019_part_05 ha hz h0 h8 h9
    · by_cases h12 : a ≤ (29/125:ℝ)
      · exact coverage019_part_06 ha hz h0 h8 h12
      · exact coverage019_part_07 ha hz h0 h8 h12
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

end


