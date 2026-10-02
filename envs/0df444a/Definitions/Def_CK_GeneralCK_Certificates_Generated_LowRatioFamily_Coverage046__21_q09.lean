-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q09
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q09
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T14:38:47.054718+00:00
-- url     : https://prove2.me/theorems/e1c3cb8c-7f46-4bc9-b7d6-38738bba5cb0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 10 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 10 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 10 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 10 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q08
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0875__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0882__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0889__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0895__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_880_881 {a z : ℝ} (ha : a ∈ Set.Icc (12 / 25) (241 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((481 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_880 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_881 ⟨hr,ha.2⟩ hz
theorem cover_882_883 {a z : ℝ} (ha : a ∈ Set.Icc (241 / 500) (121 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((483 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_882 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_883 ⟨hr,ha.2⟩ hz
theorem cover_880_883 {a z : ℝ} (ha : a ∈ Set.Icc (12 / 25) (121 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((241 / 500):ℝ) with hl | hr
  · exact cover_880_881 ⟨ha.1,hl⟩ hz
  · exact cover_882_883 ⟨hr,ha.2⟩ hz
theorem cover_884_885 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 250) (243 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((97 / 200):ℝ) with hl | hr
  · exact curvature_leaf_884 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_885 ⟨hr,ha.2⟩ hz
theorem cover_886_887 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 500) (61 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((487 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_886 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_887 ⟨hr,ha.2⟩ hz
theorem cover_884_887 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 250) (61 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((243 / 500):ℝ) with hl | hr
  · exact cover_884_885 ⟨ha.1,hl⟩ hz
  · exact cover_886_887 ⟨hr,ha.2⟩ hz
theorem cover_880_887 {a z : ℝ} (ha : a ∈ Set.Icc (12 / 25) (61 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((121 / 250):ℝ) with hl | hr
  · exact cover_880_883 ⟨ha.1,hl⟩ hz
  · exact cover_884_887 ⟨hr,ha.2⟩ hz
theorem cover_888_889 {a z : ℝ} (ha : a ∈ Set.Icc (61 / 125) (49 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((489 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_888 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_889 ⟨hr,ha.2⟩ hz
theorem cover_890_891 {a z : ℝ} (ha : a ∈ Set.Icc (49 / 100) (123 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((491 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_890 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_891 ⟨hr,ha.2⟩ hz
theorem cover_888_891 {a z : ℝ} (ha : a ∈ Set.Icc (61 / 125) (123 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((49 / 100):ℝ) with hl | hr
  · exact cover_888_889 ⟨ha.1,hl⟩ hz
  · exact cover_890_891 ⟨hr,ha.2⟩ hz
theorem cover_892_893 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 250) (247 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((493 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_892 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_893 ⟨hr,ha.2⟩ hz
theorem cover_894_895 {a z : ℝ} (ha : a ∈ Set.Icc (247 / 500) (62 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((99 / 200):ℝ) with hl | hr
  · exact curvature_leaf_894 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_895 ⟨hr,ha.2⟩ hz
theorem cover_892_895 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 250) (62 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((247 / 500):ℝ) with hl | hr
  · exact cover_892_893 ⟨ha.1,hl⟩ hz
  · exact cover_894_895 ⟨hr,ha.2⟩ hz
theorem cover_888_895 {a z : ℝ} (ha : a ∈ Set.Icc (61 / 125) (62 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((123 / 250):ℝ) with hl | hr
  · exact cover_888_891 ⟨ha.1,hl⟩ hz
  · exact cover_892_895 ⟨hr,ha.2⟩ hz
theorem cover_880_895 {a z : ℝ} (ha : a ∈ Set.Icc (12 / 25) (62 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((61 / 125):ℝ) with hl | hr
  · exact cover_880_887 ⟨ha.1,hl⟩ hz
  · exact cover_888_895 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


