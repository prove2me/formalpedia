-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q17
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q17
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:06:54.465071+00:00
-- url     : https://prove2.me/theorems/7d91bb09-489d-47f5-9297-fa03d9c60e2b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 18 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 18 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 18 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 18 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q16
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1008__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1012__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1017__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1023__5

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1008_1009 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 125) (83 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((827 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1008 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1009 ⟨hr,ha.2⟩ hz
theorem cover_1010_1011 {a z : ℝ} (ha : a ∈ Set.Icc (83 / 100) (209 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((833 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1010 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1011 ⟨hr,ha.2⟩ hz
theorem cover_1008_1011 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 125) (209 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((83 / 100):ℝ) with hl | hr
  · exact cover_1008_1009 ⟨ha.1,hl⟩ hz
  · exact cover_1010_1011 ⟨hr,ha.2⟩ hz
theorem cover_1012_1013 {a z : ℝ} (ha : a ∈ Set.Icc (209 / 250) (421 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((839 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1012 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1013 ⟨hr,ha.2⟩ hz
theorem cover_1014_1015 {a z : ℝ} (ha : a ∈ Set.Icc (421 / 500) (106 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((169 / 200):ℝ) with hl | hr
  · exact curvature_leaf_1014 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1015 ⟨hr,ha.2⟩ hz
theorem cover_1012_1015 {a z : ℝ} (ha : a ∈ Set.Icc (209 / 250) (106 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((421 / 500):ℝ) with hl | hr
  · exact cover_1012_1013 ⟨ha.1,hl⟩ hz
  · exact cover_1014_1015 ⟨hr,ha.2⟩ hz
theorem cover_1008_1015 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 125) (106 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((209 / 250):ℝ) with hl | hr
  · exact cover_1008_1011 ⟨ha.1,hl⟩ hz
  · exact cover_1012_1015 ⟨hr,ha.2⟩ hz
theorem cover_1016_1017 {a z : ℝ} (ha : a ∈ Set.Icc (106 / 125) (427 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((851 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1016 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1017 ⟨hr,ha.2⟩ hz
theorem cover_1018_1019 {a z : ℝ} (ha : a ∈ Set.Icc (427 / 500) (43 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((857 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1018 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1019 ⟨hr,ha.2⟩ hz
theorem cover_1016_1019 {a z : ℝ} (ha : a ∈ Set.Icc (106 / 125) (43 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((427 / 500):ℝ) with hl | hr
  · exact cover_1016_1017 ⟨ha.1,hl⟩ hz
  · exact cover_1018_1019 ⟨hr,ha.2⟩ hz
theorem cover_1020_1021 {a z : ℝ} (ha : a ∈ Set.Icc (43 / 50) (433 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((863 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1020 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1021 ⟨hr,ha.2⟩ hz
theorem cover_1022_1023 {a z : ℝ} (ha : a ∈ Set.Icc (433 / 500) (109 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((869 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1022 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1023 ⟨hr,ha.2⟩ hz
theorem cover_1020_1023 {a z : ℝ} (ha : a ∈ Set.Icc (43 / 50) (109 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((433 / 500):ℝ) with hl | hr
  · exact cover_1020_1021 ⟨ha.1,hl⟩ hz
  · exact cover_1022_1023 ⟨hr,ha.2⟩ hz
theorem cover_1016_1023 {a z : ℝ} (ha : a ∈ Set.Icc (106 / 125) (109 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((43 / 50):ℝ) with hl | hr
  · exact cover_1016_1019 ⟨ha.1,hl⟩ hz
  · exact cover_1020_1023 ⟨hr,ha.2⟩ hz
theorem cover_1008_1023 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 125) (109 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((106 / 125):ℝ) with hl | hr
  · exact cover_1008_1015 ⟨ha.1,hl⟩ hz
  · exact cover_1016_1023 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


