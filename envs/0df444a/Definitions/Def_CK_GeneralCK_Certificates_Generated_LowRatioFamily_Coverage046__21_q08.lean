-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q08
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q08
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T14:30:27.946977+00:00
-- url     : https://prove2.me/theorems/4ab58177-ecc6-40e3-899a-9fd5edd3a5ee
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 9 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 9 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 9 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 9 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q07
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0864__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0869__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0875__7

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_864_865 {a z : ℝ} (ha : a ∈ Set.Icc (58 / 125) (233 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((93 / 200):ℝ) with hl | hr
  · exact curvature_leaf_864 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_865 ⟨hr,ha.2⟩ hz
theorem cover_866_867 {a z : ℝ} (ha : a ∈ Set.Icc (233 / 500) (117 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((467 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_866 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_867 ⟨hr,ha.2⟩ hz
theorem cover_864_867 {a z : ℝ} (ha : a ∈ Set.Icc (58 / 125) (117 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((233 / 500):ℝ) with hl | hr
  · exact cover_864_865 ⟨ha.1,hl⟩ hz
  · exact cover_866_867 ⟨hr,ha.2⟩ hz
theorem cover_868_869 {a z : ℝ} (ha : a ∈ Set.Icc (117 / 250) (47 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((469 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_868 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_869 ⟨hr,ha.2⟩ hz
theorem cover_870_871 {a z : ℝ} (ha : a ∈ Set.Icc (47 / 100) (59 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((471 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_870 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_871 ⟨hr,ha.2⟩ hz
theorem cover_868_871 {a z : ℝ} (ha : a ∈ Set.Icc (117 / 250) (59 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((47 / 100):ℝ) with hl | hr
  · exact cover_868_869 ⟨ha.1,hl⟩ hz
  · exact cover_870_871 ⟨hr,ha.2⟩ hz
theorem cover_864_871 {a z : ℝ} (ha : a ∈ Set.Icc (58 / 125) (59 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((117 / 250):ℝ) with hl | hr
  · exact cover_864_867 ⟨ha.1,hl⟩ hz
  · exact cover_868_871 ⟨hr,ha.2⟩ hz
theorem cover_872_873 {a z : ℝ} (ha : a ∈ Set.Icc (59 / 125) (237 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((473 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_872 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_873 ⟨hr,ha.2⟩ hz
theorem cover_874_875 {a z : ℝ} (ha : a ∈ Set.Icc (237 / 500) (119 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((19 / 40):ℝ) with hl | hr
  · exact curvature_leaf_874 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_875 ⟨hr,ha.2⟩ hz
theorem cover_872_875 {a z : ℝ} (ha : a ∈ Set.Icc (59 / 125) (119 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((237 / 500):ℝ) with hl | hr
  · exact cover_872_873 ⟨ha.1,hl⟩ hz
  · exact cover_874_875 ⟨hr,ha.2⟩ hz
theorem cover_876_877 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 250) (239 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((477 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_876 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_877 ⟨hr,ha.2⟩ hz
theorem cover_878_879 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 500) (12 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((479 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_878 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_879 ⟨hr,ha.2⟩ hz
theorem cover_876_879 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 250) (12 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((239 / 500):ℝ) with hl | hr
  · exact cover_876_877 ⟨ha.1,hl⟩ hz
  · exact cover_878_879 ⟨hr,ha.2⟩ hz
theorem cover_872_879 {a z : ℝ} (ha : a ∈ Set.Icc (59 / 125) (12 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((119 / 250):ℝ) with hl | hr
  · exact cover_872_875 ⟨ha.1,hl⟩ hz
  · exact cover_876_879 ⟨hr,ha.2⟩ hz
theorem cover_864_879 {a z : ℝ} (ha : a ∈ Set.Icc (58 / 125) (12 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((59 / 125):ℝ) with hl | hr
  · exact cover_864_871 ⟨ha.1,hl⟩ hz
  · exact cover_872_879 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


