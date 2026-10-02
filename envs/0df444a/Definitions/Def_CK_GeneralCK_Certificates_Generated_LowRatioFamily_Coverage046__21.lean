-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T03:17:31.349801+00:00
-- url     : https://prove2.me/theorems/990843a7-b137-494c-937b-f24d092d02be
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q19
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1053__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1059__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1065__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1070__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1056_1057 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 250) (479 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((957 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1056 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1057 ⟨hr,ha.2⟩ hz
theorem cover_1058_1059 {a z : ℝ} (ha : a ∈ Set.Icc (479 / 500) (24 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((959 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1058 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1059 ⟨hr,ha.2⟩ hz
theorem cover_1056_1059 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 250) (24 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((479 / 500):ℝ) with hl | hr
  · exact cover_1056_1057 ⟨ha.1,hl⟩ hz
  · exact cover_1058_1059 ⟨hr,ha.2⟩ hz
theorem cover_1060_1061 {a z : ℝ} (ha : a ∈ Set.Icc (24 / 25) (481 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((961 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1060 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1061 ⟨hr,ha.2⟩ hz
theorem cover_1062_1063 {a z : ℝ} (ha : a ∈ Set.Icc (481 / 500) (241 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((963 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1062 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1063 ⟨hr,ha.2⟩ hz
theorem cover_1060_1063 {a z : ℝ} (ha : a ∈ Set.Icc (24 / 25) (241 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((481 / 500):ℝ) with hl | hr
  · exact cover_1060_1061 ⟨ha.1,hl⟩ hz
  · exact cover_1062_1063 ⟨hr,ha.2⟩ hz
theorem cover_1056_1063 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 250) (241 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((24 / 25):ℝ) with hl | hr
  · exact cover_1056_1059 ⟨ha.1,hl⟩ hz
  · exact cover_1060_1063 ⟨hr,ha.2⟩ hz
theorem cover_1064_1065 {a z : ℝ} (ha : a ∈ Set.Icc (241 / 250) (483 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((193 / 200):ℝ) with hl | hr
  · exact curvature_leaf_1064 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1065 ⟨hr,ha.2⟩ hz
theorem cover_1066_1067 {a z : ℝ} (ha : a ∈ Set.Icc (483 / 500) (121 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((967 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1066 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1067 ⟨hr,ha.2⟩ hz
theorem cover_1064_1067 {a z : ℝ} (ha : a ∈ Set.Icc (241 / 250) (121 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((483 / 500):ℝ) with hl | hr
  · exact cover_1064_1065 ⟨ha.1,hl⟩ hz
  · exact cover_1066_1067 ⟨hr,ha.2⟩ hz
theorem cover_1068_1069 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 125) (97 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((969 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1068 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1069 ⟨hr,ha.2⟩ hz
theorem cover_1070_1071 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 100) (243 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((971 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1070 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1071 ⟨hr,ha.2⟩ hz
theorem cover_1068_1071 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 125) (243 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((97 / 100):ℝ) with hl | hr
  · exact cover_1068_1069 ⟨ha.1,hl⟩ hz
  · exact cover_1070_1071 ⟨hr,ha.2⟩ hz
theorem cover_1064_1071 {a z : ℝ} (ha : a ∈ Set.Icc (241 / 250) (243 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((121 / 125):ℝ) with hl | hr
  · exact cover_1064_1067 ⟨ha.1,hl⟩ hz
  · exact cover_1068_1071 ⟨hr,ha.2⟩ hz
theorem cover_1056_1071 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 250) (243 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((241 / 250):ℝ) with hl | hr
  · exact cover_1056_1063 ⟨ha.1,hl⟩ hz
  · exact cover_1064_1071 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


