-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q06
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T14:14:45.567989+00:00
-- url     : https://prove2.me/theorems/48cd2612-962a-4438-b9fd-1a2463035689
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 7 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 7 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 7 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 7 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0828__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0834__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0840__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0846__5

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_832_833 {a z : ℝ} (ha : a ∈ Set.Icc (54 / 125) (217 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((433 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_832 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_833 ⟨hr,ha.2⟩ hz
theorem cover_834_835 {a z : ℝ} (ha : a ∈ Set.Icc (217 / 500) (109 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((87 / 200):ℝ) with hl | hr
  · exact curvature_leaf_834 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_835 ⟨hr,ha.2⟩ hz
theorem cover_832_835 {a z : ℝ} (ha : a ∈ Set.Icc (54 / 125) (109 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((217 / 500):ℝ) with hl | hr
  · exact cover_832_833 ⟨ha.1,hl⟩ hz
  · exact cover_834_835 ⟨hr,ha.2⟩ hz
theorem cover_836_837 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 250) (219 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((437 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_836 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_837 ⟨hr,ha.2⟩ hz
theorem cover_838_839 {a z : ℝ} (ha : a ∈ Set.Icc (219 / 500) (11 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((439 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_838 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_839 ⟨hr,ha.2⟩ hz
theorem cover_836_839 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 250) (11 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((219 / 500):ℝ) with hl | hr
  · exact cover_836_837 ⟨ha.1,hl⟩ hz
  · exact cover_838_839 ⟨hr,ha.2⟩ hz
theorem cover_832_839 {a z : ℝ} (ha : a ∈ Set.Icc (54 / 125) (11 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((109 / 250):ℝ) with hl | hr
  · exact cover_832_835 ⟨ha.1,hl⟩ hz
  · exact cover_836_839 ⟨hr,ha.2⟩ hz
theorem cover_840_841 {a z : ℝ} (ha : a ∈ Set.Icc (11 / 25) (221 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((441 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_840 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_841 ⟨hr,ha.2⟩ hz
theorem cover_842_843 {a z : ℝ} (ha : a ∈ Set.Icc (221 / 500) (111 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((443 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_842 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_843 ⟨hr,ha.2⟩ hz
theorem cover_840_843 {a z : ℝ} (ha : a ∈ Set.Icc (11 / 25) (111 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((221 / 500):ℝ) with hl | hr
  · exact cover_840_841 ⟨ha.1,hl⟩ hz
  · exact cover_842_843 ⟨hr,ha.2⟩ hz
theorem cover_844_845 {a z : ℝ} (ha : a ∈ Set.Icc (111 / 250) (223 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((89 / 200):ℝ) with hl | hr
  · exact curvature_leaf_844 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_845 ⟨hr,ha.2⟩ hz
theorem cover_846_847 {a z : ℝ} (ha : a ∈ Set.Icc (223 / 500) (56 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((447 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_846 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_847 ⟨hr,ha.2⟩ hz
theorem cover_844_847 {a z : ℝ} (ha : a ∈ Set.Icc (111 / 250) (56 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((223 / 500):ℝ) with hl | hr
  · exact cover_844_845 ⟨ha.1,hl⟩ hz
  · exact cover_846_847 ⟨hr,ha.2⟩ hz
theorem cover_840_847 {a z : ℝ} (ha : a ∈ Set.Icc (11 / 25) (56 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((111 / 250):ℝ) with hl | hr
  · exact cover_840_843 ⟨ha.1,hl⟩ hz
  · exact cover_844_847 ⟨hr,ha.2⟩ hz
theorem cover_832_847 {a z : ℝ} (ha : a ∈ Set.Icc (54 / 125) (56 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((11 / 25):ℝ) with hl | hr
  · exact cover_832_839 ⟨ha.1,hl⟩ hz
  · exact cover_840_847 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


