-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q14
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:36:39.37536+00:00
-- url     : https://prove2.me/theorems/e9bc41d6-cf6d-4766-96fd-bd42c36bd6b8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 15 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 15 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 15 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 15 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q13
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0960__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0966__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0972__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_960_961 {a z : ℝ} (ha : a ∈ Set.Icc (17 / 25) (343 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((683 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_960 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_961 ⟨hr,ha.2⟩ hz
theorem cover_962_963 {a z : ℝ} (ha : a ∈ Set.Icc (343 / 500) (173 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((689 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_962 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_963 ⟨hr,ha.2⟩ hz
theorem cover_960_963 {a z : ℝ} (ha : a ∈ Set.Icc (17 / 25) (173 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((343 / 500):ℝ) with hl | hr
  · exact cover_960_961 ⟨ha.1,hl⟩ hz
  · exact cover_962_963 ⟨hr,ha.2⟩ hz
theorem cover_964_965 {a z : ℝ} (ha : a ∈ Set.Icc (173 / 250) (349 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((139 / 200):ℝ) with hl | hr
  · exact curvature_leaf_964 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_965 ⟨hr,ha.2⟩ hz
theorem cover_966_967 {a z : ℝ} (ha : a ∈ Set.Icc (349 / 500) (88 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((701 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_966 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_967 ⟨hr,ha.2⟩ hz
theorem cover_964_967 {a z : ℝ} (ha : a ∈ Set.Icc (173 / 250) (88 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((349 / 500):ℝ) with hl | hr
  · exact cover_964_965 ⟨ha.1,hl⟩ hz
  · exact cover_966_967 ⟨hr,ha.2⟩ hz
theorem cover_960_967 {a z : ℝ} (ha : a ∈ Set.Icc (17 / 25) (88 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((173 / 250):ℝ) with hl | hr
  · exact cover_960_963 ⟨ha.1,hl⟩ hz
  · exact cover_964_967 ⟨hr,ha.2⟩ hz
theorem cover_968_969 {a z : ℝ} (ha : a ∈ Set.Icc (88 / 125) (71 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((707 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_968 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_969 ⟨hr,ha.2⟩ hz
theorem cover_970_971 {a z : ℝ} (ha : a ∈ Set.Icc (71 / 100) (179 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((713 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_970 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_971 ⟨hr,ha.2⟩ hz
theorem cover_968_971 {a z : ℝ} (ha : a ∈ Set.Icc (88 / 125) (179 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((71 / 100):ℝ) with hl | hr
  · exact cover_968_969 ⟨ha.1,hl⟩ hz
  · exact cover_970_971 ⟨hr,ha.2⟩ hz
theorem cover_972_973 {a z : ℝ} (ha : a ∈ Set.Icc (179 / 250) (361 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((719 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_972 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_973 ⟨hr,ha.2⟩ hz
theorem cover_974_975 {a z : ℝ} (ha : a ∈ Set.Icc (361 / 500) (91 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((29 / 40):ℝ) with hl | hr
  · exact curvature_leaf_974 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_975 ⟨hr,ha.2⟩ hz
theorem cover_972_975 {a z : ℝ} (ha : a ∈ Set.Icc (179 / 250) (91 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((361 / 500):ℝ) with hl | hr
  · exact cover_972_973 ⟨ha.1,hl⟩ hz
  · exact cover_974_975 ⟨hr,ha.2⟩ hz
theorem cover_968_975 {a z : ℝ} (ha : a ∈ Set.Icc (88 / 125) (91 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((179 / 250):ℝ) with hl | hr
  · exact cover_968_971 ⟨ha.1,hl⟩ hz
  · exact cover_972_975 ⟨hr,ha.2⟩ hz
theorem cover_960_975 {a z : ℝ} (ha : a ∈ Set.Icc (17 / 25) (91 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((88 / 125):ℝ) with hl | hr
  · exact cover_960_967 ⟨ha.1,hl⟩ hz
  · exact cover_968_975 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


