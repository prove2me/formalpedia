-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q06
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T04:33:34.154272+00:00
-- url     : https://prove2.me/theorems/0522576c-f546-43cf-b4fa-8af3f8ccd28e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralC…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage023) (piece 7 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage023) (piece 7 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016 (+7 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage018, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage019, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage023) (piece 7 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage016 (+7 modules: GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage017, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage018, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage019, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage020, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage021, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage022, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Coverage023) (piece 7 of 8).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q06_c00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q06_c01
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q06_c02
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q06_c03
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q06_c04
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q06_c05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q06_c06
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Coverage016__8_q06_c07

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage022 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage022 {a z : ℝ} (ha : Bounds (141/250) (499/500) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (369/500:ℝ)
  · by_cases h1 : a ≤ (319/500:ℝ)
    · by_cases h2 : a ≤ (299/500:ℝ)
      · exact coverage022_part_00 ha hz h0 h1 h2
      · exact coverage022_part_01 ha hz h0 h1 h2
    · by_cases h5 : a ≤ (171/250:ℝ)
      · exact coverage022_part_02 ha hz h0 h1 h5
      · exact coverage022_part_03 ha hz h0 h1 h5
  · by_cases h8 : a ≤ (87/100:ℝ)
    · by_cases h9 : a ≤ (4/5:ℝ)
      · exact coverage022_part_04 ha hz h0 h8 h9
      · exact coverage022_part_05 ha hz h0 h8 h9
    · by_cases h12 : a ≤ (189/200:ℝ)
      · exact coverage022_part_06 ha hz h0 h8 h12
      · exact coverage022_part_07 ha hz h0 h8 h12
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

end


