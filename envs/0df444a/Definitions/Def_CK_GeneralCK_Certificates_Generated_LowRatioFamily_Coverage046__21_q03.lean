-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q03
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:54:35.237663+00:00
-- url     : https://prove2.me/theorems/c8a87d23-3c19-4aa0-9250-b8ded22dcced
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 4 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 4 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 4 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 4 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q02
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0784__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0790__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0796__5

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_784_785 {a z : ℝ} (ha : a ∈ Set.Icc (48 / 125) (193 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((77 / 200):ℝ) with hl | hr
  · exact curvature_leaf_784 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_785 ⟨hr,ha.2⟩ hz
theorem cover_786_787 {a z : ℝ} (ha : a ∈ Set.Icc (193 / 500) (97 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((387 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_786 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_787 ⟨hr,ha.2⟩ hz
theorem cover_784_787 {a z : ℝ} (ha : a ∈ Set.Icc (48 / 125) (97 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((193 / 500):ℝ) with hl | hr
  · exact cover_784_785 ⟨ha.1,hl⟩ hz
  · exact cover_786_787 ⟨hr,ha.2⟩ hz
theorem cover_788_789 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 250) (39 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((389 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_788 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_789 ⟨hr,ha.2⟩ hz
theorem cover_790_791 {a z : ℝ} (ha : a ∈ Set.Icc (39 / 100) (49 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((391 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_790 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_791 ⟨hr,ha.2⟩ hz
theorem cover_788_791 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 250) (49 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((39 / 100):ℝ) with hl | hr
  · exact cover_788_789 ⟨ha.1,hl⟩ hz
  · exact cover_790_791 ⟨hr,ha.2⟩ hz
theorem cover_784_791 {a z : ℝ} (ha : a ∈ Set.Icc (48 / 125) (49 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((97 / 250):ℝ) with hl | hr
  · exact cover_784_787 ⟨ha.1,hl⟩ hz
  · exact cover_788_791 ⟨hr,ha.2⟩ hz
theorem cover_792_793 {a z : ℝ} (ha : a ∈ Set.Icc (49 / 125) (197 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((393 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_792 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_793 ⟨hr,ha.2⟩ hz
theorem cover_794_795 {a z : ℝ} (ha : a ∈ Set.Icc (197 / 500) (99 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((79 / 200):ℝ) with hl | hr
  · exact curvature_leaf_794 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_795 ⟨hr,ha.2⟩ hz
theorem cover_792_795 {a z : ℝ} (ha : a ∈ Set.Icc (49 / 125) (99 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((197 / 500):ℝ) with hl | hr
  · exact cover_792_793 ⟨ha.1,hl⟩ hz
  · exact cover_794_795 ⟨hr,ha.2⟩ hz
theorem cover_796_797 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 250) (199 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((397 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_796 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_797 ⟨hr,ha.2⟩ hz
theorem cover_798_799 {a z : ℝ} (ha : a ∈ Set.Icc (199 / 500) (2 / 5))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((399 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_798 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_799 ⟨hr,ha.2⟩ hz
theorem cover_796_799 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 250) (2 / 5))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((199 / 500):ℝ) with hl | hr
  · exact cover_796_797 ⟨ha.1,hl⟩ hz
  · exact cover_798_799 ⟨hr,ha.2⟩ hz
theorem cover_792_799 {a z : ℝ} (ha : a ∈ Set.Icc (49 / 125) (2 / 5))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((99 / 250):ℝ) with hl | hr
  · exact cover_792_795 ⟨ha.1,hl⟩ hz
  · exact cover_796_799 ⟨hr,ha.2⟩ hz
theorem cover_784_799 {a z : ℝ} (ha : a ∈ Set.Icc (48 / 125) (2 / 5))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((49 / 125):ℝ) with hl | hr
  · exact cover_784_791 ⟨ha.1,hl⟩ hz
  · exact cover_792_799 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


