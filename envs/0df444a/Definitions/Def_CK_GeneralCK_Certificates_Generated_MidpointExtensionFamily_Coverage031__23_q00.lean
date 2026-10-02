-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23_q00
-- name    : CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Coverage031__23_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T12:59:30.559863+00:00
-- url     : https://prove2.me/theorems/dee75c26-f6da-4f85-b467-b2d7a47f1a79
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage032, Gener…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage032, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage033, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage039, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage040, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage052, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage053) (piece 1 of 23)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage032, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage033, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage039, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage040, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage052, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage053) (piece 1 of 23)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 (+22 modules: GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage032, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage033, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage034, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage035, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage036, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage037, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage038, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage039, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage040, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage041, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage042, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage043, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage044, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage045, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage046, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage047, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage048, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage049, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage050, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage051, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage052, GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage053) (piece 1 of 23) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage031 (+22 modules: GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage032, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage033, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage034, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage035, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage036, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage037, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage038, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage039, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage040, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage041, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage042, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage043, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage044, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage045, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage046, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage047, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage048, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage049, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage050, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage051, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage052, GeneralCK/Certificates/Generated/MidpointExtensionFamily/Coverage053) (piece 1 of 23).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0485__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0489__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0493__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0497__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointExtensionFamily_Cell0501__4

-- ===== source module GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage031 =====
section
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem coverage031 {a z : ℝ} (ha : Bounds (497/2000) (283/1000) a)
    (hz : Bounds (81/1000) (2033/25000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (33/125:ℝ)
  · by_cases h1 : a ≤ (32/125:ℝ)
    · by_cases h2 : a ≤ (63/250:ℝ)
      · by_cases h3 : a ≤ (1/4:ℝ)
        · exact Cell0486.curvature_pos ⟨ha.1,h3⟩ hz
        · exact Cell0487.curvature_pos ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (127/500:ℝ)
        · exact Cell0488.curvature_pos ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact Cell0489.curvature_pos ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (13/50:ℝ)
      · by_cases h6 : a ≤ (129/500:ℝ)
        · exact Cell0490.curvature_pos ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact Cell0491.curvature_pos ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (131/500:ℝ)
        · exact Cell0492.curvature_pos ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · exact Cell0493.curvature_pos ⟨(le_of_lt (lt_of_not_ge h7)),h0⟩ hz
  · by_cases h8 : a ≤ (273/1000:ℝ)
    · by_cases h9 : a ≤ (67/250:ℝ)
      · by_cases h10 : a ≤ (133/500:ℝ)
        · exact Cell0494.curvature_pos ⟨(le_of_lt (lt_of_not_ge h0)),h10⟩ hz
        · exact Cell0495.curvature_pos ⟨(le_of_lt (lt_of_not_ge h10)),h9⟩ hz
      · by_cases h11 : a ≤ (541/2000:ℝ)
        · exact Cell0496.curvature_pos ⟨(le_of_lt (lt_of_not_ge h9)),h11⟩ hz
        · exact Cell0497.curvature_pos ⟨(le_of_lt (lt_of_not_ge h11)),h8⟩ hz
    · by_cases h12 : a ≤ (139/500:ℝ)
      · by_cases h13 : a ≤ (551/2000:ℝ)
        · exact Cell0498.curvature_pos ⟨(le_of_lt (lt_of_not_ge h8)),h13⟩ hz
        · exact Cell0499.curvature_pos ⟨(le_of_lt (lt_of_not_ge h13)),h12⟩ hz
      · by_cases h14 : a ≤ (561/2000:ℝ)
        · exact Cell0500.curvature_pos ⟨(le_of_lt (lt_of_not_ge h12)),h14⟩ hz
        · exact Cell0501.curvature_pos ⟨(le_of_lt (lt_of_not_ge h14)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

end


