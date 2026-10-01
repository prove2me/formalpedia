-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage067__4_q00
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage067__4_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T11:49:06.556851+00:00
-- url     : https://prove2.me/theorems/4659c12d-8daa-430a-96c1-f8807e9a892d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage067 (+3 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage068, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage069, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage070) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1070__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1076__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1081__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1085__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1089__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1094__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1100__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1105__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1110__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1117__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1124__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell1131__4

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1072_1073 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 250) (487 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((973 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1072 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1073 ⟨hr,ha.2⟩ hz
theorem cover_1074_1075 {a z : ℝ} (ha : a ∈ Set.Icc (487 / 500) (122 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((39 / 40):ℝ) with hl | hr
  · exact curvature_leaf_1074 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1075 ⟨hr,ha.2⟩ hz
theorem cover_1072_1075 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 250) (122 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((487 / 500):ℝ) with hl | hr
  · exact cover_1072_1073 ⟨ha.1,hl⟩ hz
  · exact cover_1074_1075 ⟨hr,ha.2⟩ hz
theorem cover_1076_1077 {a z : ℝ} (ha : a ∈ Set.Icc (122 / 125) (489 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((977 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1076 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1077 ⟨hr,ha.2⟩ hz
theorem cover_1078_1079 {a z : ℝ} (ha : a ∈ Set.Icc (489 / 500) (49 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((979 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1078 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1079 ⟨hr,ha.2⟩ hz
theorem cover_1076_1079 {a z : ℝ} (ha : a ∈ Set.Icc (122 / 125) (49 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((489 / 500):ℝ) with hl | hr
  · exact cover_1076_1077 ⟨ha.1,hl⟩ hz
  · exact cover_1078_1079 ⟨hr,ha.2⟩ hz
theorem cover_1072_1079 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 250) (49 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((122 / 125):ℝ) with hl | hr
  · exact cover_1072_1075 ⟨ha.1,hl⟩ hz
  · exact cover_1076_1079 ⟨hr,ha.2⟩ hz
theorem cover_1080_1081 {a z : ℝ} (ha : a ∈ Set.Icc (49 / 50) (491 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((981 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1080 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1081 ⟨hr,ha.2⟩ hz
theorem cover_1082_1083 {a z : ℝ} (ha : a ∈ Set.Icc (491 / 500) (123 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((983 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1082 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1083 ⟨hr,ha.2⟩ hz
theorem cover_1080_1083 {a z : ℝ} (ha : a ∈ Set.Icc (49 / 50) (123 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((491 / 500):ℝ) with hl | hr
  · exact cover_1080_1081 ⟨ha.1,hl⟩ hz
  · exact cover_1082_1083 ⟨hr,ha.2⟩ hz
theorem cover_1084_1085 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 125) (493 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((197 / 200):ℝ) with hl | hr
  · exact curvature_leaf_1084 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1085 ⟨hr,ha.2⟩ hz
theorem cover_1086_1087 {a z : ℝ} (ha : a ∈ Set.Icc (493 / 500) (247 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((987 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1086 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1087 ⟨hr,ha.2⟩ hz
theorem cover_1084_1087 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 125) (247 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((493 / 500):ℝ) with hl | hr
  · exact cover_1084_1085 ⟨ha.1,hl⟩ hz
  · exact cover_1086_1087 ⟨hr,ha.2⟩ hz
theorem cover_1080_1087 {a z : ℝ} (ha : a ∈ Set.Icc (49 / 50) (247 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((123 / 125):ℝ) with hl | hr
  · exact cover_1080_1083 ⟨ha.1,hl⟩ hz
  · exact cover_1084_1087 ⟨hr,ha.2⟩ hz
theorem cover_1072_1087 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 250) (247 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((49 / 50):ℝ) with hl | hr
  · exact cover_1072_1079 ⟨ha.1,hl⟩ hz
  · exact cover_1080_1087 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


