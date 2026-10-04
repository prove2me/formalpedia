-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage031__23
-- name    : CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage031__23
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T16:09:14.052325+00:00
-- url     : https://prove2.me/theorems/0d80088a-5cf2-4e8a-bc82-7dabd1aac073
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage032, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage032, GeneralCK.Certificates.Generated.MidpointFamily.Coverage033, GeneralCK.Certificates.Generated.MidpointFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointFamily.Coverage039, GeneralCK.Certificates.Generated.MidpointFamily.Coverage040, GeneralCK.Certificates.Generated.MidpointFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointFamily.Coverage052, GeneralCK.Certificates.Generated.MidpointFamily.Coverage053)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage032, GeneralCK.Certificates.Generated.MidpointFamily.Coverage033, GeneralCK.Certificates.Generated.MidpointFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointFamily.Coverage039, GeneralCK.Certificates.Generated.MidpointFamily.Coverage040, GeneralCK.Certificates.Generated.MidpointFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointFamily.Coverage052, GeneralCK.Certificates.Generated.MidpointFamily.Coverage053)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointFamily.Coverage032, GeneralCK.Certificates.Generated.MidpointFamily.Coverage033, GeneralCK.Certificates.Generated.MidpointFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointFamily.Coverage039, GeneralCK.Certificates.Generated.MidpointFamily.Coverage040, GeneralCK.Certificates.Generated.MidpointFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointFamily.Coverage052, GeneralCK.Certificates.Generated.MidpointFamily.Coverage053) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointFamily/Coverage031 (+22 modules: GeneralCK/Certificates/Generated/MidpointFamily/Coverage032, GeneralCK/Certificates/Generated/MidpointFamily/Coverage033, GeneralCK/Certificates/Generated/MidpointFamily/Coverage034, GeneralCK/Certificates/Generated/MidpointFamily/Coverage035, GeneralCK/Certificates/Generated/MidpointFamily/Coverage036, GeneralCK/Certificates/Generated/MidpointFamily/Coverage037, GeneralCK/Certificates/Generated/MidpointFamily/Coverage038, GeneralCK/Certificates/Generated/MidpointFamily/Coverage039, GeneralCK/Certificates/Generated/MidpointFamily/Coverage040, GeneralCK/Certificates/Generated/MidpointFamily/Coverage041, GeneralCK/Certificates/Generated/MidpointFamily/Coverage042, GeneralCK/Certificates/Generated/MidpointFamily/Coverage043, GeneralCK/Certificates/Generated/MidpointFamily/Coverage044, GeneralCK/Certificates/Generated/MidpointFamily/Coverage045, GeneralCK/Certificates/Generated/MidpointFamily/Coverage046, GeneralCK/Certificates/Generated/MidpointFamily/Coverage047, GeneralCK/Certificates/Generated/MidpointFamily/Coverage048, GeneralCK/Certificates/Generated/MidpointFamily/Coverage049, GeneralCK/Certificates/Generated/MidpointFamily/Coverage050, GeneralCK/Certificates/Generated/MidpointFamily/Coverage051, GeneralCK/Certificates/Generated/MidpointFamily/Coverage052, GeneralCK/Certificates/Generated/MidpointFamily/Coverage053).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Coverage031__23_q21
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0846__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0850__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0854__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0857__2

-- ===== source module GeneralCK.Certificates.Generated.MidpointFamily.Coverage053 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage053 {a z : ℝ} (ha : Bounds (493/500) (999/1000) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
  by_cases h0 : a≤(993/1000:ℝ)
  · by_cases h1 : a≤(99/100:ℝ)
    · by_cases h2 : a≤(247/250:ℝ)
      · exact Cell0848.curvature_pos ⟨ha.1,h2⟩ hz
      · exact Cell0849.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h1⟩ hz
    · by_cases h3 : a≤(991/1000:ℝ)
      · exact Cell0850.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h3⟩ hz
      · by_cases h4 : a≤(124/125:ℝ)
        · exact Cell0851.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h4⟩ hz
        · exact Cell0852.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h0⟩ hz
  · by_cases h5 : a≤(249/250:ℝ)
    · by_cases h6 : a≤(497/500:ℝ)
      · exact Cell0853.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h6⟩ hz
      · by_cases h7 : a≤(199/200:ℝ)
        · exact Cell0854.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h7⟩ hz
        · exact Cell0855.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h5⟩ hz
    · by_cases h8 : a≤(997/1000:ℝ)
      · exact Cell0856.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h8⟩ hz
      · by_cases h9 : a≤(499/500:ℝ)
        · exact Cell0857.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h9⟩ hz
        · exact Cell0858.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointFamily

end


