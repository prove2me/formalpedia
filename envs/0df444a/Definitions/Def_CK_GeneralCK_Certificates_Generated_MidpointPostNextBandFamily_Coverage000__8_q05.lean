-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q05
-- name    : CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T12:43:18.944296+00:00
-- url     : https://prove2.me/theorems/da9f96dd-1217-4475-abd2-2078803e769f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, …
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage007) (piece 6 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage007) (piece 6 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage000 (+7 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage001, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage002, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage003, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage004, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage005, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage006, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage007) (piece 6 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage000 (+7 modules: GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage001, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage002, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage003, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage004, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage005, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage006, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Coverage007) (piece 6 of 8).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q04
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q05_c00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q05_c01
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q05_c02
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q05_c03
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q05_c04
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q05_c05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q05_c06
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Coverage000__8_q05_c07

-- ===== source module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Coverage005 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage005 {a z : ℝ} (ha : Bounds (1563/10000) (1579/10000) a)
    (hz : Bounds (17/200) (43/500) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (1571/10000:ℝ)
  · by_cases h1 : a ≤ (1567/10000:ℝ)
    · by_cases h2 : a ≤ (313/2000:ℝ)
      · exact coverage005_part_00 ha hz h0 h1 h2
      · exact coverage005_part_01 ha hz h0 h1 h2
    · by_cases h5 : a ≤ (1569/10000:ℝ)
      · exact coverage005_part_02 ha hz h0 h1 h5
      · exact coverage005_part_03 ha hz h0 h1 h5
  · by_cases h8 : a ≤ (63/400:ℝ)
    · by_cases h9 : a ≤ (1573/10000:ℝ)
      · exact coverage005_part_04 ha hz h0 h8 h9
      · exact coverage005_part_05 ha hz h0 h8 h9
    · by_cases h12 : a ≤ (1577/10000:ℝ)
      · exact coverage005_part_06 ha hz h0 h8 h12
      · exact coverage005_part_07 ha hz h0 h8 h12
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily

end


