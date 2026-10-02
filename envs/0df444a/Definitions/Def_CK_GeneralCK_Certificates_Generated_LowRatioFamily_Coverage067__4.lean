-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage067__4
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage067__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:57:14.173384+00:00
-- url     : https://prove2.me/theorems/6efcc31b-391a-4d17-8c2e-bf56c24aa228
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage067 (+3 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage068, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage069, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage070).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage067__4_q02

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1121_1122 {a z : ℝ} (ha : a ∈ Set.Icc (4981 / 5000) (4983 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2491 / 2500):ℝ) with hl | hr
  · exact curvature_leaf_1121 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1122 ⟨hr,ha.2⟩ hz
theorem cover_1120_1122 {a z : ℝ} (ha : a ∈ Set.Icc (249 / 250) (4983 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4981 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1120 ⟨ha.1,hl⟩ hz
  · exact cover_1121_1122 ⟨hr,ha.2⟩ hz
theorem cover_1123_1124 {a z : ℝ} (ha : a ∈ Set.Icc (4983 / 5000) (997 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((623 / 625):ℝ) with hl | hr
  · exact curvature_leaf_1123 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1124 ⟨hr,ha.2⟩ hz
theorem cover_1125_1126 {a z : ℝ} (ha : a ∈ Set.Icc (997 / 1000) (4987 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2493 / 2500):ℝ) with hl | hr
  · exact curvature_leaf_1125 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1126 ⟨hr,ha.2⟩ hz
theorem cover_1123_1126 {a z : ℝ} (ha : a ∈ Set.Icc (4983 / 5000) (4987 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((997 / 1000):ℝ) with hl | hr
  · exact cover_1123_1124 ⟨ha.1,hl⟩ hz
  · exact cover_1125_1126 ⟨hr,ha.2⟩ hz
theorem cover_1120_1126 {a z : ℝ} (ha : a ∈ Set.Icc (249 / 250) (4987 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4983 / 5000):ℝ) with hl | hr
  · exact cover_1120_1122 ⟨ha.1,hl⟩ hz
  · exact cover_1123_1126 ⟨hr,ha.2⟩ hz
theorem cover_1127_1128 {a z : ℝ} (ha : a ∈ Set.Icc (4987 / 5000) (4989 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1247 / 1250):ℝ) with hl | hr
  · exact curvature_leaf_1127 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1128 ⟨hr,ha.2⟩ hz
theorem cover_1129_1130 {a z : ℝ} (ha : a ∈ Set.Icc (4989 / 5000) (4991 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((499 / 500):ℝ) with hl | hr
  · exact curvature_leaf_1129 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1130 ⟨hr,ha.2⟩ hz
theorem cover_1127_1130 {a z : ℝ} (ha : a ∈ Set.Icc (4987 / 5000) (4991 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4989 / 5000):ℝ) with hl | hr
  · exact cover_1127_1128 ⟨ha.1,hl⟩ hz
  · exact cover_1129_1130 ⟨hr,ha.2⟩ hz
theorem cover_1131_1132 {a z : ℝ} (ha : a ∈ Set.Icc (4991 / 5000) (4993 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((624 / 625):ℝ) with hl | hr
  · exact curvature_leaf_1131 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1132 ⟨hr,ha.2⟩ hz
theorem cover_1133_1134 {a z : ℝ} (ha : a ∈ Set.Icc (4993 / 5000) (999 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2497 / 2500):ℝ) with hl | hr
  · exact curvature_leaf_1133 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1134 ⟨hr,ha.2⟩ hz
theorem cover_1131_1134 {a z : ℝ} (ha : a ∈ Set.Icc (4991 / 5000) (999 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4993 / 5000):ℝ) with hl | hr
  · exact cover_1131_1132 ⟨ha.1,hl⟩ hz
  · exact cover_1133_1134 ⟨hr,ha.2⟩ hz
theorem cover_1127_1134 {a z : ℝ} (ha : a ∈ Set.Icc (4987 / 5000) (999 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4991 / 5000):ℝ) with hl | hr
  · exact cover_1127_1130 ⟨ha.1,hl⟩ hz
  · exact cover_1131_1134 ⟨hr,ha.2⟩ hz
theorem cover_1120_1134 {a z : ℝ} (ha : a ∈ Set.Icc (249 / 250) (999 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4987 / 5000):ℝ) with hl | hr
  · exact cover_1120_1126 ⟨ha.1,hl⟩ hz
  · exact cover_1127_1134 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


