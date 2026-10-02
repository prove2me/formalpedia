-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q04
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:58:43.795522+00:00
-- url     : https://prove2.me/theorems/a48f8ce6-e175-4d00-b4d1-d3223e7f86c0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 5 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 5 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 5 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 5 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q03
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0796__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0801__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0805__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0809__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0813__5

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_800_801 {a z : ℝ} (ha : a ∈ Set.Icc (2 / 5) (201 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((401 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_800 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_801 ⟨hr,ha.2⟩ hz
theorem cover_802_803 {a z : ℝ} (ha : a ∈ Set.Icc (201 / 500) (101 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((403 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_802 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_803 ⟨hr,ha.2⟩ hz
theorem cover_800_803 {a z : ℝ} (ha : a ∈ Set.Icc (2 / 5) (101 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((201 / 500):ℝ) with hl | hr
  · exact cover_800_801 ⟨ha.1,hl⟩ hz
  · exact cover_802_803 ⟨hr,ha.2⟩ hz
theorem cover_804_805 {a z : ℝ} (ha : a ∈ Set.Icc (101 / 250) (203 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((81 / 200):ℝ) with hl | hr
  · exact curvature_leaf_804 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_805 ⟨hr,ha.2⟩ hz
theorem cover_806_807 {a z : ℝ} (ha : a ∈ Set.Icc (203 / 500) (51 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((407 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_806 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_807 ⟨hr,ha.2⟩ hz
theorem cover_804_807 {a z : ℝ} (ha : a ∈ Set.Icc (101 / 250) (51 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((203 / 500):ℝ) with hl | hr
  · exact cover_804_805 ⟨ha.1,hl⟩ hz
  · exact cover_806_807 ⟨hr,ha.2⟩ hz
theorem cover_800_807 {a z : ℝ} (ha : a ∈ Set.Icc (2 / 5) (51 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((101 / 250):ℝ) with hl | hr
  · exact cover_800_803 ⟨ha.1,hl⟩ hz
  · exact cover_804_807 ⟨hr,ha.2⟩ hz
theorem cover_808_809 {a z : ℝ} (ha : a ∈ Set.Icc (51 / 125) (41 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((409 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_808 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_809 ⟨hr,ha.2⟩ hz
theorem cover_810_811 {a z : ℝ} (ha : a ∈ Set.Icc (41 / 100) (103 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((411 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_810 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_811 ⟨hr,ha.2⟩ hz
theorem cover_808_811 {a z : ℝ} (ha : a ∈ Set.Icc (51 / 125) (103 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((41 / 100):ℝ) with hl | hr
  · exact cover_808_809 ⟨ha.1,hl⟩ hz
  · exact cover_810_811 ⟨hr,ha.2⟩ hz
theorem cover_812_813 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 250) (207 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((413 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_812 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_813 ⟨hr,ha.2⟩ hz
theorem cover_814_815 {a z : ℝ} (ha : a ∈ Set.Icc (207 / 500) (52 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((83 / 200):ℝ) with hl | hr
  · exact curvature_leaf_814 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_815 ⟨hr,ha.2⟩ hz
theorem cover_812_815 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 250) (52 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((207 / 500):ℝ) with hl | hr
  · exact cover_812_813 ⟨ha.1,hl⟩ hz
  · exact cover_814_815 ⟨hr,ha.2⟩ hz
theorem cover_808_815 {a z : ℝ} (ha : a ∈ Set.Icc (51 / 125) (52 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((103 / 250):ℝ) with hl | hr
  · exact cover_808_811 ⟨ha.1,hl⟩ hz
  · exact cover_812_815 ⟨hr,ha.2⟩ hz
theorem cover_800_815 {a z : ℝ} (ha : a ∈ Set.Icc (2 / 5) (52 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((51 / 125):ℝ) with hl | hr
  · exact cover_800_807 ⟨ha.1,hl⟩ hz
  · exact cover_808_815 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


