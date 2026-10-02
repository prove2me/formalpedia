-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q16
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:59:48.676983+00:00
-- url     : https://prove2.me/theorems/e953a693-6ab0-4a37-9aae-a166f7e3ba9e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 17 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 17 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 17 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 17 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q15
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0990__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0997__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1002__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_992_993 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 125) (391 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((779 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_992 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_993 ⟨hr,ha.2⟩ hz
theorem cover_994_995 {a z : ℝ} (ha : a ∈ Set.Icc (391 / 500) (197 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((157 / 200):ℝ) with hl | hr
  · exact curvature_leaf_994 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_995 ⟨hr,ha.2⟩ hz
theorem cover_992_995 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 125) (197 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((391 / 500):ℝ) with hl | hr
  · exact cover_992_993 ⟨ha.1,hl⟩ hz
  · exact cover_994_995 ⟨hr,ha.2⟩ hz
theorem cover_996_997 {a z : ℝ} (ha : a ∈ Set.Icc (197 / 250) (397 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((791 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_996 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_997 ⟨hr,ha.2⟩ hz
theorem cover_998_999 {a z : ℝ} (ha : a ∈ Set.Icc (397 / 500) (4 / 5))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((797 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_998 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_999 ⟨hr,ha.2⟩ hz
theorem cover_996_999 {a z : ℝ} (ha : a ∈ Set.Icc (197 / 250) (4 / 5))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((397 / 500):ℝ) with hl | hr
  · exact cover_996_997 ⟨ha.1,hl⟩ hz
  · exact cover_998_999 ⟨hr,ha.2⟩ hz
theorem cover_992_999 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 125) (4 / 5))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((197 / 250):ℝ) with hl | hr
  · exact cover_992_995 ⟨ha.1,hl⟩ hz
  · exact cover_996_999 ⟨hr,ha.2⟩ hz
theorem cover_1000_1001 {a z : ℝ} (ha : a ∈ Set.Icc (4 / 5) (403 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((803 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1000 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1001 ⟨hr,ha.2⟩ hz
theorem cover_1002_1003 {a z : ℝ} (ha : a ∈ Set.Icc (403 / 500) (203 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((809 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1002 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1003 ⟨hr,ha.2⟩ hz
theorem cover_1000_1003 {a z : ℝ} (ha : a ∈ Set.Icc (4 / 5) (203 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((403 / 500):ℝ) with hl | hr
  · exact cover_1000_1001 ⟨ha.1,hl⟩ hz
  · exact cover_1002_1003 ⟨hr,ha.2⟩ hz
theorem cover_1004_1005 {a z : ℝ} (ha : a ∈ Set.Icc (203 / 250) (409 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((163 / 200):ℝ) with hl | hr
  · exact curvature_leaf_1004 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1005 ⟨hr,ha.2⟩ hz
theorem cover_1006_1007 {a z : ℝ} (ha : a ∈ Set.Icc (409 / 500) (103 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((821 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1006 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1007 ⟨hr,ha.2⟩ hz
theorem cover_1004_1007 {a z : ℝ} (ha : a ∈ Set.Icc (203 / 250) (103 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((409 / 500):ℝ) with hl | hr
  · exact cover_1004_1005 ⟨ha.1,hl⟩ hz
  · exact cover_1006_1007 ⟨hr,ha.2⟩ hz
theorem cover_1000_1007 {a z : ℝ} (ha : a ∈ Set.Icc (4 / 5) (103 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((203 / 250):ℝ) with hl | hr
  · exact cover_1000_1003 ⟨ha.1,hl⟩ hz
  · exact cover_1004_1007 ⟨hr,ha.2⟩ hz
theorem cover_992_1007 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 125) (103 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4 / 5):ℝ) with hl | hr
  · exact cover_992_999 ⟨ha.1,hl⟩ hz
  · exact cover_1000_1007 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


