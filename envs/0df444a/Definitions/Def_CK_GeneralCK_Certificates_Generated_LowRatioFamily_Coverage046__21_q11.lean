-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q11
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:42:50.418037+00:00
-- url     : https://prove2.me/theorems/fe5ede08-777a-44b6-90be-60d69099975a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 12 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 12 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 12 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 12 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q10
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0907__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0913__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0919__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0924__5

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_912_913 {a z : ℝ} (ha : a ∈ Set.Icc (67 / 125) (271 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((539 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_912 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_913 ⟨hr,ha.2⟩ hz
theorem cover_914_915 {a z : ℝ} (ha : a ∈ Set.Icc (271 / 500) (137 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((109 / 200):ℝ) with hl | hr
  · exact curvature_leaf_914 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_915 ⟨hr,ha.2⟩ hz
theorem cover_912_915 {a z : ℝ} (ha : a ∈ Set.Icc (67 / 125) (137 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((271 / 500):ℝ) with hl | hr
  · exact cover_912_913 ⟨ha.1,hl⟩ hz
  · exact cover_914_915 ⟨hr,ha.2⟩ hz
theorem cover_916_917 {a z : ℝ} (ha : a ∈ Set.Icc (137 / 250) (277 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((551 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_916 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_917 ⟨hr,ha.2⟩ hz
theorem cover_918_919 {a z : ℝ} (ha : a ∈ Set.Icc (277 / 500) (14 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((557 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_918 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_919 ⟨hr,ha.2⟩ hz
theorem cover_916_919 {a z : ℝ} (ha : a ∈ Set.Icc (137 / 250) (14 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((277 / 500):ℝ) with hl | hr
  · exact cover_916_917 ⟨ha.1,hl⟩ hz
  · exact cover_918_919 ⟨hr,ha.2⟩ hz
theorem cover_912_919 {a z : ℝ} (ha : a ∈ Set.Icc (67 / 125) (14 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((137 / 250):ℝ) with hl | hr
  · exact cover_912_915 ⟨ha.1,hl⟩ hz
  · exact cover_916_919 ⟨hr,ha.2⟩ hz
theorem cover_920_921 {a z : ℝ} (ha : a ∈ Set.Icc (14 / 25) (283 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((563 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_920 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_921 ⟨hr,ha.2⟩ hz
theorem cover_922_923 {a z : ℝ} (ha : a ∈ Set.Icc (283 / 500) (143 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((569 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_922 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_923 ⟨hr,ha.2⟩ hz
theorem cover_920_923 {a z : ℝ} (ha : a ∈ Set.Icc (14 / 25) (143 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((283 / 500):ℝ) with hl | hr
  · exact cover_920_921 ⟨ha.1,hl⟩ hz
  · exact cover_922_923 ⟨hr,ha.2⟩ hz
theorem cover_924_925 {a z : ℝ} (ha : a ∈ Set.Icc (143 / 250) (289 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((23 / 40):ℝ) with hl | hr
  · exact curvature_leaf_924 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_925 ⟨hr,ha.2⟩ hz
theorem cover_926_927 {a z : ℝ} (ha : a ∈ Set.Icc (289 / 500) (73 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((581 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_926 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_927 ⟨hr,ha.2⟩ hz
theorem cover_924_927 {a z : ℝ} (ha : a ∈ Set.Icc (143 / 250) (73 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((289 / 500):ℝ) with hl | hr
  · exact cover_924_925 ⟨ha.1,hl⟩ hz
  · exact cover_926_927 ⟨hr,ha.2⟩ hz
theorem cover_920_927 {a z : ℝ} (ha : a ∈ Set.Icc (14 / 25) (73 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((143 / 250):ℝ) with hl | hr
  · exact cover_920_923 ⟨ha.1,hl⟩ hz
  · exact cover_924_927 ⟨hr,ha.2⟩ hz
theorem cover_912_927 {a z : ℝ} (ha : a ∈ Set.Icc (67 / 125) (73 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((14 / 25):ℝ) with hl | hr
  · exact cover_912_919 ⟨ha.1,hl⟩ hz
  · exact cover_920_927 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


