-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q12
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:53:11.385835+00:00
-- url     : https://prove2.me/theorems/22335f4c-144b-4a4a-9239-1dc5807c93e9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 13 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 13 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 13 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 13 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q11
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0924__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0929__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0933__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0939__7

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_928_929 {a z : ℝ} (ha : a ∈ Set.Icc (73 / 125) (59 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((587 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_928 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_929 ⟨hr,ha.2⟩ hz
theorem cover_930_931 {a z : ℝ} (ha : a ∈ Set.Icc (59 / 100) (149 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((593 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_930 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_931 ⟨hr,ha.2⟩ hz
theorem cover_928_931 {a z : ℝ} (ha : a ∈ Set.Icc (73 / 125) (149 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((59 / 100):ℝ) with hl | hr
  · exact cover_928_929 ⟨ha.1,hl⟩ hz
  · exact cover_930_931 ⟨hr,ha.2⟩ hz
theorem cover_932_933 {a z : ℝ} (ha : a ∈ Set.Icc (149 / 250) (301 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((599 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_932 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_933 ⟨hr,ha.2⟩ hz
theorem cover_934_935 {a z : ℝ} (ha : a ∈ Set.Icc (301 / 500) (76 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((121 / 200):ℝ) with hl | hr
  · exact curvature_leaf_934 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_935 ⟨hr,ha.2⟩ hz
theorem cover_932_935 {a z : ℝ} (ha : a ∈ Set.Icc (149 / 250) (76 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((301 / 500):ℝ) with hl | hr
  · exact cover_932_933 ⟨ha.1,hl⟩ hz
  · exact cover_934_935 ⟨hr,ha.2⟩ hz
theorem cover_928_935 {a z : ℝ} (ha : a ∈ Set.Icc (73 / 125) (76 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((149 / 250):ℝ) with hl | hr
  · exact cover_928_931 ⟨ha.1,hl⟩ hz
  · exact cover_932_935 ⟨hr,ha.2⟩ hz
theorem cover_936_937 {a z : ℝ} (ha : a ∈ Set.Icc (76 / 125) (307 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((611 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_936 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_937 ⟨hr,ha.2⟩ hz
theorem cover_938_939 {a z : ℝ} (ha : a ∈ Set.Icc (307 / 500) (31 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((617 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_938 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_939 ⟨hr,ha.2⟩ hz
theorem cover_936_939 {a z : ℝ} (ha : a ∈ Set.Icc (76 / 125) (31 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((307 / 500):ℝ) with hl | hr
  · exact cover_936_937 ⟨ha.1,hl⟩ hz
  · exact cover_938_939 ⟨hr,ha.2⟩ hz
theorem cover_940_941 {a z : ℝ} (ha : a ∈ Set.Icc (31 / 50) (313 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((623 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_940 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_941 ⟨hr,ha.2⟩ hz
theorem cover_942_943 {a z : ℝ} (ha : a ∈ Set.Icc (313 / 500) (79 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((629 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_942 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_943 ⟨hr,ha.2⟩ hz
theorem cover_940_943 {a z : ℝ} (ha : a ∈ Set.Icc (31 / 50) (79 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((313 / 500):ℝ) with hl | hr
  · exact cover_940_941 ⟨ha.1,hl⟩ hz
  · exact cover_942_943 ⟨hr,ha.2⟩ hz
theorem cover_936_943 {a z : ℝ} (ha : a ∈ Set.Icc (76 / 125) (79 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((31 / 50):ℝ) with hl | hr
  · exact cover_936_939 ⟨ha.1,hl⟩ hz
  · exact cover_940_943 ⟨hr,ha.2⟩ hz
theorem cover_928_943 {a z : ℝ} (ha : a ∈ Set.Icc (73 / 125) (79 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((76 / 125):ℝ) with hl | hr
  · exact cover_928_935 ⟨ha.1,hl⟩ hz
  · exact cover_936_943 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


