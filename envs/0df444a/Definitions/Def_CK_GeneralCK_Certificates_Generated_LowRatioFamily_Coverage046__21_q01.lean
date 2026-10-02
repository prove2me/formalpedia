-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q01
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:47:28.374057+00:00
-- url     : https://prove2.me/theorems/520f49fb-e84e-4063-b1ee-501fd348d96e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 2 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 2 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 2 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 2 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0748__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0755__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0761__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0767__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_752_753 {a z : ℝ} (ha : a ∈ Set.Icc (44 / 125) (177 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((353 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_752 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_753 ⟨hr,ha.2⟩ hz
theorem cover_754_755 {a z : ℝ} (ha : a ∈ Set.Icc (177 / 500) (89 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((71 / 200):ℝ) with hl | hr
  · exact curvature_leaf_754 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_755 ⟨hr,ha.2⟩ hz
theorem cover_752_755 {a z : ℝ} (ha : a ∈ Set.Icc (44 / 125) (89 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((177 / 500):ℝ) with hl | hr
  · exact cover_752_753 ⟨ha.1,hl⟩ hz
  · exact cover_754_755 ⟨hr,ha.2⟩ hz
theorem cover_756_757 {a z : ℝ} (ha : a ∈ Set.Icc (89 / 250) (179 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((357 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_756 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_757 ⟨hr,ha.2⟩ hz
theorem cover_758_759 {a z : ℝ} (ha : a ∈ Set.Icc (179 / 500) (9 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((359 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_758 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_759 ⟨hr,ha.2⟩ hz
theorem cover_756_759 {a z : ℝ} (ha : a ∈ Set.Icc (89 / 250) (9 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((179 / 500):ℝ) with hl | hr
  · exact cover_756_757 ⟨ha.1,hl⟩ hz
  · exact cover_758_759 ⟨hr,ha.2⟩ hz
theorem cover_752_759 {a z : ℝ} (ha : a ∈ Set.Icc (44 / 125) (9 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((89 / 250):ℝ) with hl | hr
  · exact cover_752_755 ⟨ha.1,hl⟩ hz
  · exact cover_756_759 ⟨hr,ha.2⟩ hz
theorem cover_760_761 {a z : ℝ} (ha : a ∈ Set.Icc (9 / 25) (181 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((361 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_760 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_761 ⟨hr,ha.2⟩ hz
theorem cover_762_763 {a z : ℝ} (ha : a ∈ Set.Icc (181 / 500) (91 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((363 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_762 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_763 ⟨hr,ha.2⟩ hz
theorem cover_760_763 {a z : ℝ} (ha : a ∈ Set.Icc (9 / 25) (91 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((181 / 500):ℝ) with hl | hr
  · exact cover_760_761 ⟨ha.1,hl⟩ hz
  · exact cover_762_763 ⟨hr,ha.2⟩ hz
theorem cover_764_765 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 250) (183 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((73 / 200):ℝ) with hl | hr
  · exact curvature_leaf_764 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_765 ⟨hr,ha.2⟩ hz
theorem cover_766_767 {a z : ℝ} (ha : a ∈ Set.Icc (183 / 500) (46 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((367 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_766 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_767 ⟨hr,ha.2⟩ hz
theorem cover_764_767 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 250) (46 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((183 / 500):ℝ) with hl | hr
  · exact cover_764_765 ⟨ha.1,hl⟩ hz
  · exact cover_766_767 ⟨hr,ha.2⟩ hz
theorem cover_760_767 {a z : ℝ} (ha : a ∈ Set.Icc (9 / 25) (46 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((91 / 250):ℝ) with hl | hr
  · exact cover_760_763 ⟨ha.1,hl⟩ hz
  · exact cover_764_767 ⟨hr,ha.2⟩ hz
theorem cover_752_767 {a z : ℝ} (ha : a ∈ Set.Icc (44 / 125) (46 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((9 / 25):ℝ) with hl | hr
  · exact cover_752_759 ⟨ha.1,hl⟩ hz
  · exact cover_760_767 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


