-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q09
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q09
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T01:53:05.539496+00:00
-- url     : https://prove2.me/theorems/3fc79f3d-e008-4ab5-a0d1-90395c2fd14f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (+13 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage020, GeneralCK.Certi…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (+13 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage030, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage031, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage032) (piece 10 of 14)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (+13 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage030, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage031, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage032) (piece 10 of 14)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage019 (+13 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage020, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage021, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage022, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage023, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage024, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage025, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage026, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage027, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage028, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage029, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage030, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage031, GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage032) (piece 10 of 14) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage019 (+13 modules: GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage020, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage021, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage022, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage023, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage024, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage025, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage026, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage027, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage028, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage029, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage030, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage031, GeneralCK/Certificates/Generated/MidpointNextFamily/Coverage032) (piece 10 of 14).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q08
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q09_c00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q09_c01
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q09_c02
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q09_c03
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q09_c04
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q09_c05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q09_c06
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Coverage019__14_q09_c07

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.Coverage028 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointNextFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage028 {a z : ℝ} (ha : Bounds (299/1000) (157/500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(153/500:ℝ)
  · by_cases h1 : a≤(151/500:ℝ)
    · by_cases h2 : a≤(3/10:ℝ)
      · exact coverage028_part_00 ha hz h0 h1 h2
      · exact coverage028_part_01 ha hz h0 h1 h2
    · by_cases h5 : a≤(38/125:ℝ)
      · exact coverage028_part_02 ha hz h0 h1 h5
      · exact coverage028_part_03 ha hz h0 h1 h5
  · by_cases h8 : a≤(31/100:ℝ)
    · by_cases h9 : a≤(77/250:ℝ)
      · exact coverage028_part_04 ha hz h0 h8 h9
      · exact coverage028_part_05 ha hz h0 h8 h9
    · by_cases h12 : a≤(39/125:ℝ)
      · exact coverage028_part_06 ha hz h0 h8 h12
      · exact coverage028_part_07 ha hz h0 h8 h12
end GeneralCK.Certificates.ReflectionMidpointNextFamily

end


