-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q07
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T14:21:39.508057+00:00
-- url     : https://prove2.me/theorems/b974a811-030b-428a-ab6f-8040532111d3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 8 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 8 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 8 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 8 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q06
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0846__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0851__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0858__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_848_849 {a z : ℝ} (ha : a ∈ Set.Icc (56 / 125) (9 / 20))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((449 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_848 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_849 ⟨hr,ha.2⟩ hz
theorem cover_850_851 {a z : ℝ} (ha : a ∈ Set.Icc (9 / 20) (113 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((451 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_850 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_851 ⟨hr,ha.2⟩ hz
theorem cover_848_851 {a z : ℝ} (ha : a ∈ Set.Icc (56 / 125) (113 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((9 / 20):ℝ) with hl | hr
  · exact cover_848_849 ⟨ha.1,hl⟩ hz
  · exact cover_850_851 ⟨hr,ha.2⟩ hz
theorem cover_852_853 {a z : ℝ} (ha : a ∈ Set.Icc (113 / 250) (227 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((453 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_852 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_853 ⟨hr,ha.2⟩ hz
theorem cover_854_855 {a z : ℝ} (ha : a ∈ Set.Icc (227 / 500) (57 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((91 / 200):ℝ) with hl | hr
  · exact curvature_leaf_854 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_855 ⟨hr,ha.2⟩ hz
theorem cover_852_855 {a z : ℝ} (ha : a ∈ Set.Icc (113 / 250) (57 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((227 / 500):ℝ) with hl | hr
  · exact cover_852_853 ⟨ha.1,hl⟩ hz
  · exact cover_854_855 ⟨hr,ha.2⟩ hz
theorem cover_848_855 {a z : ℝ} (ha : a ∈ Set.Icc (56 / 125) (57 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((113 / 250):ℝ) with hl | hr
  · exact cover_848_851 ⟨ha.1,hl⟩ hz
  · exact cover_852_855 ⟨hr,ha.2⟩ hz
theorem cover_856_857 {a z : ℝ} (ha : a ∈ Set.Icc (57 / 125) (229 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((457 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_856 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_857 ⟨hr,ha.2⟩ hz
theorem cover_858_859 {a z : ℝ} (ha : a ∈ Set.Icc (229 / 500) (23 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((459 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_858 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_859 ⟨hr,ha.2⟩ hz
theorem cover_856_859 {a z : ℝ} (ha : a ∈ Set.Icc (57 / 125) (23 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((229 / 500):ℝ) with hl | hr
  · exact cover_856_857 ⟨ha.1,hl⟩ hz
  · exact cover_858_859 ⟨hr,ha.2⟩ hz
theorem cover_860_861 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 50) (231 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((461 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_860 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_861 ⟨hr,ha.2⟩ hz
theorem cover_862_863 {a z : ℝ} (ha : a ∈ Set.Icc (231 / 500) (58 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((463 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_862 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_863 ⟨hr,ha.2⟩ hz
theorem cover_860_863 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 50) (58 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((231 / 500):ℝ) with hl | hr
  · exact cover_860_861 ⟨ha.1,hl⟩ hz
  · exact cover_862_863 ⟨hr,ha.2⟩ hz
theorem cover_856_863 {a z : ℝ} (ha : a ∈ Set.Icc (57 / 125) (58 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((23 / 50):ℝ) with hl | hr
  · exact cover_856_859 ⟨ha.1,hl⟩ hz
  · exact cover_860_863 ⟨hr,ha.2⟩ hz
theorem cover_848_863 {a z : ℝ} (ha : a ∈ Set.Icc (56 / 125) (58 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((57 / 125):ℝ) with hl | hr
  · exact cover_848_855 ⟨ha.1,hl⟩ hz
  · exact cover_856_863 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


