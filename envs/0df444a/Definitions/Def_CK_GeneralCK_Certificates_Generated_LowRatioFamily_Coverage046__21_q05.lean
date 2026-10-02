-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q05
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T14:04:47.413124+00:00
-- url     : https://prove2.me/theorems/22695d3b-185e-46ba-966d-973c70500a4d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 6 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 6 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 6 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 6 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q04
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0813__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0818__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0823__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0828__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_816_817 {a z : ℝ} (ha : a ∈ Set.Icc (52 / 125) (209 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((417 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_816 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_817 ⟨hr,ha.2⟩ hz
theorem cover_818_819 {a z : ℝ} (ha : a ∈ Set.Icc (209 / 500) (21 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((419 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_818 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_819 ⟨hr,ha.2⟩ hz
theorem cover_816_819 {a z : ℝ} (ha : a ∈ Set.Icc (52 / 125) (21 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((209 / 500):ℝ) with hl | hr
  · exact cover_816_817 ⟨ha.1,hl⟩ hz
  · exact cover_818_819 ⟨hr,ha.2⟩ hz
theorem cover_820_821 {a z : ℝ} (ha : a ∈ Set.Icc (21 / 50) (211 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((421 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_820 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_821 ⟨hr,ha.2⟩ hz
theorem cover_822_823 {a z : ℝ} (ha : a ∈ Set.Icc (211 / 500) (53 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((423 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_822 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_823 ⟨hr,ha.2⟩ hz
theorem cover_820_823 {a z : ℝ} (ha : a ∈ Set.Icc (21 / 50) (53 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((211 / 500):ℝ) with hl | hr
  · exact cover_820_821 ⟨ha.1,hl⟩ hz
  · exact cover_822_823 ⟨hr,ha.2⟩ hz
theorem cover_816_823 {a z : ℝ} (ha : a ∈ Set.Icc (52 / 125) (53 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((21 / 50):ℝ) with hl | hr
  · exact cover_816_819 ⟨ha.1,hl⟩ hz
  · exact cover_820_823 ⟨hr,ha.2⟩ hz
theorem cover_824_825 {a z : ℝ} (ha : a ∈ Set.Icc (53 / 125) (213 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((17 / 40):ℝ) with hl | hr
  · exact curvature_leaf_824 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_825 ⟨hr,ha.2⟩ hz
theorem cover_826_827 {a z : ℝ} (ha : a ∈ Set.Icc (213 / 500) (107 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((427 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_826 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_827 ⟨hr,ha.2⟩ hz
theorem cover_824_827 {a z : ℝ} (ha : a ∈ Set.Icc (53 / 125) (107 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((213 / 500):ℝ) with hl | hr
  · exact cover_824_825 ⟨ha.1,hl⟩ hz
  · exact cover_826_827 ⟨hr,ha.2⟩ hz
theorem cover_828_829 {a z : ℝ} (ha : a ∈ Set.Icc (107 / 250) (43 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((429 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_828 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_829 ⟨hr,ha.2⟩ hz
theorem cover_830_831 {a z : ℝ} (ha : a ∈ Set.Icc (43 / 100) (54 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((431 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_830 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_831 ⟨hr,ha.2⟩ hz
theorem cover_828_831 {a z : ℝ} (ha : a ∈ Set.Icc (107 / 250) (54 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((43 / 100):ℝ) with hl | hr
  · exact cover_828_829 ⟨ha.1,hl⟩ hz
  · exact cover_830_831 ⟨hr,ha.2⟩ hz
theorem cover_824_831 {a z : ℝ} (ha : a ∈ Set.Icc (53 / 125) (54 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((107 / 250):ℝ) with hl | hr
  · exact cover_824_827 ⟨ha.1,hl⟩ hz
  · exact cover_828_831 ⟨hr,ha.2⟩ hz
theorem cover_816_831 {a z : ℝ} (ha : a ∈ Set.Icc (52 / 125) (54 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((53 / 125):ℝ) with hl | hr
  · exact cover_816_823 ⟨ha.1,hl⟩ hz
  · exact cover_824_831 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


