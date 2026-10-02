-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q02
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:51:03.714026+00:00
-- url     : https://prove2.me/theorems/2b7bcf9f-1cf8-47c8-a75d-c33148d80c22
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 3 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 3 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 3 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 3 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q01
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0767__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0773__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0779__5

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_768_769 {a z : ℝ} (ha : a ∈ Set.Icc (46 / 125) (37 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((369 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_768 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_769 ⟨hr,ha.2⟩ hz
theorem cover_770_771 {a z : ℝ} (ha : a ∈ Set.Icc (37 / 100) (93 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((371 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_770 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_771 ⟨hr,ha.2⟩ hz
theorem cover_768_771 {a z : ℝ} (ha : a ∈ Set.Icc (46 / 125) (93 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((37 / 100):ℝ) with hl | hr
  · exact cover_768_769 ⟨ha.1,hl⟩ hz
  · exact cover_770_771 ⟨hr,ha.2⟩ hz
theorem cover_772_773 {a z : ℝ} (ha : a ∈ Set.Icc (93 / 250) (187 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((373 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_772 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_773 ⟨hr,ha.2⟩ hz
theorem cover_774_775 {a z : ℝ} (ha : a ∈ Set.Icc (187 / 500) (47 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((3 / 8):ℝ) with hl | hr
  · exact curvature_leaf_774 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_775 ⟨hr,ha.2⟩ hz
theorem cover_772_775 {a z : ℝ} (ha : a ∈ Set.Icc (93 / 250) (47 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((187 / 500):ℝ) with hl | hr
  · exact cover_772_773 ⟨ha.1,hl⟩ hz
  · exact cover_774_775 ⟨hr,ha.2⟩ hz
theorem cover_768_775 {a z : ℝ} (ha : a ∈ Set.Icc (46 / 125) (47 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((93 / 250):ℝ) with hl | hr
  · exact cover_768_771 ⟨ha.1,hl⟩ hz
  · exact cover_772_775 ⟨hr,ha.2⟩ hz
theorem cover_776_777 {a z : ℝ} (ha : a ∈ Set.Icc (47 / 125) (189 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((377 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_776 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_777 ⟨hr,ha.2⟩ hz
theorem cover_778_779 {a z : ℝ} (ha : a ∈ Set.Icc (189 / 500) (19 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((379 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_778 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_779 ⟨hr,ha.2⟩ hz
theorem cover_776_779 {a z : ℝ} (ha : a ∈ Set.Icc (47 / 125) (19 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((189 / 500):ℝ) with hl | hr
  · exact cover_776_777 ⟨ha.1,hl⟩ hz
  · exact cover_778_779 ⟨hr,ha.2⟩ hz
theorem cover_780_781 {a z : ℝ} (ha : a ∈ Set.Icc (19 / 50) (191 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((381 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_780 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_781 ⟨hr,ha.2⟩ hz
theorem cover_782_783 {a z : ℝ} (ha : a ∈ Set.Icc (191 / 500) (48 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((383 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_782 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_783 ⟨hr,ha.2⟩ hz
theorem cover_780_783 {a z : ℝ} (ha : a ∈ Set.Icc (19 / 50) (48 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((191 / 500):ℝ) with hl | hr
  · exact cover_780_781 ⟨ha.1,hl⟩ hz
  · exact cover_782_783 ⟨hr,ha.2⟩ hz
theorem cover_776_783 {a z : ℝ} (ha : a ∈ Set.Icc (47 / 125) (48 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((19 / 50):ℝ) with hl | hr
  · exact cover_776_779 ⟨ha.1,hl⟩ hz
  · exact cover_780_783 ⟨hr,ha.2⟩ hz
theorem cover_768_783 {a z : ℝ} (ha : a ∈ Set.Icc (46 / 125) (48 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((47 / 125):ℝ) with hl | hr
  · exact cover_768_775 ⟨ha.1,hl⟩ hz
  · exact cover_776_783 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


