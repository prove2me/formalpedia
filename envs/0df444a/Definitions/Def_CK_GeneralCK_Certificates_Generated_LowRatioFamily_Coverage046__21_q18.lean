-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q18
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:23:05.892873+00:00
-- url     : https://prove2.me/theorems/4e796fb4-2aeb-4bc9-8e0c-e7cd24c4b338
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 19 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 19 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 19 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 19 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q17
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1023__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1028__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1034__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1024_1025 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 125) (439 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((7 / 8):ℝ) with hl | hr
  · exact curvature_leaf_1024 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1025 ⟨hr,ha.2⟩ hz
theorem cover_1026_1027 {a z : ℝ} (ha : a ∈ Set.Icc (439 / 500) (221 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((881 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1026 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1027 ⟨hr,ha.2⟩ hz
theorem cover_1024_1027 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 125) (221 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((439 / 500):ℝ) with hl | hr
  · exact cover_1024_1025 ⟨ha.1,hl⟩ hz
  · exact cover_1026_1027 ⟨hr,ha.2⟩ hz
theorem cover_1028_1029 {a z : ℝ} (ha : a ∈ Set.Icc (221 / 250) (89 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((887 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1028 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1029 ⟨hr,ha.2⟩ hz
theorem cover_1030_1031 {a z : ℝ} (ha : a ∈ Set.Icc (89 / 100) (112 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((893 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1030 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1031 ⟨hr,ha.2⟩ hz
theorem cover_1028_1031 {a z : ℝ} (ha : a ∈ Set.Icc (221 / 250) (112 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((89 / 100):ℝ) with hl | hr
  · exact cover_1028_1029 ⟨ha.1,hl⟩ hz
  · exact cover_1030_1031 ⟨hr,ha.2⟩ hz
theorem cover_1024_1031 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 125) (112 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((221 / 250):ℝ) with hl | hr
  · exact cover_1024_1027 ⟨ha.1,hl⟩ hz
  · exact cover_1028_1031 ⟨hr,ha.2⟩ hz
theorem cover_1032_1033 {a z : ℝ} (ha : a ∈ Set.Icc (112 / 125) (451 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((899 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1032 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1033 ⟨hr,ha.2⟩ hz
theorem cover_1034_1035 {a z : ℝ} (ha : a ∈ Set.Icc (451 / 500) (227 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((181 / 200):ℝ) with hl | hr
  · exact curvature_leaf_1034 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1035 ⟨hr,ha.2⟩ hz
theorem cover_1032_1035 {a z : ℝ} (ha : a ∈ Set.Icc (112 / 125) (227 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((451 / 500):ℝ) with hl | hr
  · exact cover_1032_1033 ⟨ha.1,hl⟩ hz
  · exact cover_1034_1035 ⟨hr,ha.2⟩ hz
theorem cover_1036_1037 {a z : ℝ} (ha : a ∈ Set.Icc (227 / 250) (457 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((911 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1036 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1037 ⟨hr,ha.2⟩ hz
theorem cover_1038_1039 {a z : ℝ} (ha : a ∈ Set.Icc (457 / 500) (23 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((917 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1038 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1039 ⟨hr,ha.2⟩ hz
theorem cover_1036_1039 {a z : ℝ} (ha : a ∈ Set.Icc (227 / 250) (23 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((457 / 500):ℝ) with hl | hr
  · exact cover_1036_1037 ⟨ha.1,hl⟩ hz
  · exact cover_1038_1039 ⟨hr,ha.2⟩ hz
theorem cover_1032_1039 {a z : ℝ} (ha : a ∈ Set.Icc (112 / 125) (23 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((227 / 250):ℝ) with hl | hr
  · exact cover_1032_1035 ⟨ha.1,hl⟩ hz
  · exact cover_1036_1039 ⟨hr,ha.2⟩ hz
theorem cover_1024_1039 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 125) (23 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((112 / 125):ℝ) with hl | hr
  · exact cover_1024_1031 ⟨ha.1,hl⟩ hz
  · exact cover_1032_1039 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


