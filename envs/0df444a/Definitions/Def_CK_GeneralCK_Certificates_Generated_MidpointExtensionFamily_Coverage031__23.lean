-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23
-- name    : CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T15:59:46.183077+00:00
-- url     : https://prove2.me/theorems/9bc115e5-faf5-4039-a080-9061fbbac1da
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage032, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage032, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage033, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage039, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage040, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage052, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage053)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage032, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage033, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage039, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage040, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage052, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage053)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage032, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage033, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage039, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage040, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage052, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage053) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage031 (+22 modules: GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage032, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage033, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage034, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage035, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage036, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage037, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage038, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage039, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage040, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage041, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage042, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage043, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage044, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage045, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage046, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage047, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage048, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage049, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage050, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage051, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage052, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage053).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23_q21
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23_c00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23_c01
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23_c02
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23_c03
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23_c04
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23_c05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23_c06
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23_c07

-- ===== source module GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage053 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage053 {a z : ℝ} (ha : Bounds (361/500) (999/1000) a)
    (hz : Bounds (2033/25000) (406621/5000000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (17/20:ℝ)
  · by_cases h1 : a ≤ (98/125:ℝ)
    · by_cases h2 : a ≤ (94/125:ℝ)
      · exact coverage053_part_00 ha hz h0 h1 h2
      · exact coverage053_part_01 ha hz h0 h1 h2
    · by_cases h3 : a ≤ (163/200:ℝ)
      · exact coverage053_part_02 ha hz h0 h1 h3
      · exact coverage053_part_03 ha hz h0 h1 h3
  · by_cases h4 : a ≤ (93/100:ℝ)
    · by_cases h5 : a ≤ (89/100:ℝ)
      · exact coverage053_part_04 ha hz h0 h4 h5
      · exact coverage053_part_05 ha hz h0 h4 h5
    · by_cases h6 : a ≤ (97/100:ℝ)
      · exact coverage053_part_06 ha hz h0 h4 h6
      · exact coverage053_part_07 ha hz h0 h4 h6
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

end


