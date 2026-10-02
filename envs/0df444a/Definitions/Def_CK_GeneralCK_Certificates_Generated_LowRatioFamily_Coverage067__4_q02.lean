-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage067__4_q02
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage067__4_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:53:29.939693+00:00
-- url     : https://prove2.me/theorems/b457408a-1661-499c-b966-9e340c53d540
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage067 (+3 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage068, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage069, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage070) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage067__4_q01

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1104_1105 {a z : ℝ} (ha : a ∈ Set.Icc (1241 / 1250) (2483 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((993 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1104 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1105 ⟨hr,ha.2⟩ hz
theorem cover_1106_1107 {a z : ℝ} (ha : a ∈ Set.Icc (2483 / 2500) (621 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4967 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1106 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1107 ⟨hr,ha.2⟩ hz
theorem cover_1104_1107 {a z : ℝ} (ha : a ∈ Set.Icc (1241 / 1250) (621 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2483 / 2500):ℝ) with hl | hr
  · exact cover_1104_1105 ⟨ha.1,hl⟩ hz
  · exact cover_1106_1107 ⟨hr,ha.2⟩ hz
theorem cover_1108_1109 {a z : ℝ} (ha : a ∈ Set.Icc (621 / 625) (497 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4969 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1108 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1109 ⟨hr,ha.2⟩ hz
theorem cover_1110_1111 {a z : ℝ} (ha : a ∈ Set.Icc (497 / 500) (1243 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4971 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1110 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1111 ⟨hr,ha.2⟩ hz
theorem cover_1108_1111 {a z : ℝ} (ha : a ∈ Set.Icc (621 / 625) (1243 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((497 / 500):ℝ) with hl | hr
  · exact cover_1108_1109 ⟨ha.1,hl⟩ hz
  · exact cover_1110_1111 ⟨hr,ha.2⟩ hz
theorem cover_1104_1111 {a z : ℝ} (ha : a ∈ Set.Icc (1241 / 1250) (1243 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((621 / 625):ℝ) with hl | hr
  · exact cover_1104_1107 ⟨ha.1,hl⟩ hz
  · exact cover_1108_1111 ⟨hr,ha.2⟩ hz
theorem cover_1112_1113 {a z : ℝ} (ha : a ∈ Set.Icc (1243 / 1250) (2487 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4973 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1112 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1113 ⟨hr,ha.2⟩ hz
theorem cover_1114_1115 {a z : ℝ} (ha : a ∈ Set.Icc (2487 / 2500) (622 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((199 / 200):ℝ) with hl | hr
  · exact curvature_leaf_1114 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1115 ⟨hr,ha.2⟩ hz
theorem cover_1112_1115 {a z : ℝ} (ha : a ∈ Set.Icc (1243 / 1250) (622 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2487 / 2500):ℝ) with hl | hr
  · exact cover_1112_1113 ⟨ha.1,hl⟩ hz
  · exact cover_1114_1115 ⟨hr,ha.2⟩ hz
theorem cover_1116_1117 {a z : ℝ} (ha : a ∈ Set.Icc (622 / 625) (2489 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4977 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1116 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1117 ⟨hr,ha.2⟩ hz
theorem cover_1118_1119 {a z : ℝ} (ha : a ∈ Set.Icc (2489 / 2500) (249 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4979 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1118 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1119 ⟨hr,ha.2⟩ hz
theorem cover_1116_1119 {a z : ℝ} (ha : a ∈ Set.Icc (622 / 625) (249 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2489 / 2500):ℝ) with hl | hr
  · exact cover_1116_1117 ⟨ha.1,hl⟩ hz
  · exact cover_1118_1119 ⟨hr,ha.2⟩ hz
theorem cover_1112_1119 {a z : ℝ} (ha : a ∈ Set.Icc (1243 / 1250) (249 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((622 / 625):ℝ) with hl | hr
  · exact cover_1112_1115 ⟨ha.1,hl⟩ hz
  · exact cover_1116_1119 ⟨hr,ha.2⟩ hz
theorem cover_1104_1119 {a z : ℝ} (ha : a ∈ Set.Icc (1241 / 1250) (249 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1243 / 1250):ℝ) with hl | hr
  · exact cover_1104_1111 ⟨ha.1,hl⟩ hz
  · exact cover_1112_1119 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


