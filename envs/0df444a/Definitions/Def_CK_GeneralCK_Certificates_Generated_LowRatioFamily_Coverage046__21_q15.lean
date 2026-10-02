-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q15
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:50:06.698701+00:00
-- url     : https://prove2.me/theorems/d75a1064-5e6c-4c29-af23-e3bed880b439
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 16 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 16 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 16 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 16 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q14
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0972__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0978__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0984__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0990__7

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_976_977 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 125) (367 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((731 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_976 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_977 ⟨hr,ha.2⟩ hz
theorem cover_978_979 {a z : ℝ} (ha : a ∈ Set.Icc (367 / 500) (37 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((737 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_978 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_979 ⟨hr,ha.2⟩ hz
theorem cover_976_979 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 125) (37 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((367 / 500):ℝ) with hl | hr
  · exact cover_976_977 ⟨ha.1,hl⟩ hz
  · exact cover_978_979 ⟨hr,ha.2⟩ hz
theorem cover_980_981 {a z : ℝ} (ha : a ∈ Set.Icc (37 / 50) (373 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((743 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_980 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_981 ⟨hr,ha.2⟩ hz
theorem cover_982_983 {a z : ℝ} (ha : a ∈ Set.Icc (373 / 500) (94 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((749 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_982 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_983 ⟨hr,ha.2⟩ hz
theorem cover_980_983 {a z : ℝ} (ha : a ∈ Set.Icc (37 / 50) (94 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((373 / 500):ℝ) with hl | hr
  · exact cover_980_981 ⟨ha.1,hl⟩ hz
  · exact cover_982_983 ⟨hr,ha.2⟩ hz
theorem cover_976_983 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 125) (94 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((37 / 50):ℝ) with hl | hr
  · exact cover_976_979 ⟨ha.1,hl⟩ hz
  · exact cover_980_983 ⟨hr,ha.2⟩ hz
theorem cover_984_985 {a z : ℝ} (ha : a ∈ Set.Icc (94 / 125) (379 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((151 / 200):ℝ) with hl | hr
  · exact curvature_leaf_984 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_985 ⟨hr,ha.2⟩ hz
theorem cover_986_987 {a z : ℝ} (ha : a ∈ Set.Icc (379 / 500) (191 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((761 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_986 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_987 ⟨hr,ha.2⟩ hz
theorem cover_984_987 {a z : ℝ} (ha : a ∈ Set.Icc (94 / 125) (191 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((379 / 500):ℝ) with hl | hr
  · exact cover_984_985 ⟨ha.1,hl⟩ hz
  · exact cover_986_987 ⟨hr,ha.2⟩ hz
theorem cover_988_989 {a z : ℝ} (ha : a ∈ Set.Icc (191 / 250) (77 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((767 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_988 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_989 ⟨hr,ha.2⟩ hz
theorem cover_990_991 {a z : ℝ} (ha : a ∈ Set.Icc (77 / 100) (97 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((773 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_990 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_991 ⟨hr,ha.2⟩ hz
theorem cover_988_991 {a z : ℝ} (ha : a ∈ Set.Icc (191 / 250) (97 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((77 / 100):ℝ) with hl | hr
  · exact cover_988_989 ⟨ha.1,hl⟩ hz
  · exact cover_990_991 ⟨hr,ha.2⟩ hz
theorem cover_984_991 {a z : ℝ} (ha : a ∈ Set.Icc (94 / 125) (97 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((191 / 250):ℝ) with hl | hr
  · exact cover_984_987 ⟨ha.1,hl⟩ hz
  · exact cover_988_991 ⟨hr,ha.2⟩ hz
theorem cover_976_991 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 125) (97 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((94 / 125):ℝ) with hl | hr
  · exact cover_976_983 ⟨ha.1,hl⟩ hz
  · exact cover_984_991 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


