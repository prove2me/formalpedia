-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q13
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:30:15.22199+00:00
-- url     : https://prove2.me/theorems/25aa43a6-a9f0-40e5-ba96-89159e4b6d43
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 14 of 21)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 14 of 21)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage046 (+20 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage047, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage048, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage049, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage050, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage051, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage052, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage053, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage054, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage055, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage056, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage057, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage058, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage060, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage061, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage062, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage063, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage064, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage065, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage066) (piece 14 of 21) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage046 (+20 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage047, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage048, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage049, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage050, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage051, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage052, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage053, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage054, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage055, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage056, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage057, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage058, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage059, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage060, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage061, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage062, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage063, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage064, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage065, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage066) (piece 14 of 21).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage046__21_q12
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0939__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0946__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0953__7

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage059 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_944_945 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 125) (319 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((127 / 200):ℝ) with hl | hr
  · exact curvature_leaf_944 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_945 ⟨hr,ha.2⟩ hz
theorem cover_946_947 {a z : ℝ} (ha : a ∈ Set.Icc (319 / 500) (161 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((641 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_946 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_947 ⟨hr,ha.2⟩ hz
theorem cover_944_947 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 125) (161 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((319 / 500):ℝ) with hl | hr
  · exact cover_944_945 ⟨ha.1,hl⟩ hz
  · exact cover_946_947 ⟨hr,ha.2⟩ hz
theorem cover_948_949 {a z : ℝ} (ha : a ∈ Set.Icc (161 / 250) (13 / 20))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((647 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_948 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_949 ⟨hr,ha.2⟩ hz
theorem cover_950_951 {a z : ℝ} (ha : a ∈ Set.Icc (13 / 20) (82 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((653 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_950 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_951 ⟨hr,ha.2⟩ hz
theorem cover_948_951 {a z : ℝ} (ha : a ∈ Set.Icc (161 / 250) (82 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((13 / 20):ℝ) with hl | hr
  · exact cover_948_949 ⟨ha.1,hl⟩ hz
  · exact cover_950_951 ⟨hr,ha.2⟩ hz
theorem cover_944_951 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 125) (82 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((161 / 250):ℝ) with hl | hr
  · exact cover_944_947 ⟨ha.1,hl⟩ hz
  · exact cover_948_951 ⟨hr,ha.2⟩ hz
theorem cover_952_953 {a z : ℝ} (ha : a ∈ Set.Icc (82 / 125) (331 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((659 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_952 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_953 ⟨hr,ha.2⟩ hz
theorem cover_954_955 {a z : ℝ} (ha : a ∈ Set.Icc (331 / 500) (167 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((133 / 200):ℝ) with hl | hr
  · exact curvature_leaf_954 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_955 ⟨hr,ha.2⟩ hz
theorem cover_952_955 {a z : ℝ} (ha : a ∈ Set.Icc (82 / 125) (167 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((331 / 500):ℝ) with hl | hr
  · exact cover_952_953 ⟨ha.1,hl⟩ hz
  · exact cover_954_955 ⟨hr,ha.2⟩ hz
theorem cover_956_957 {a z : ℝ} (ha : a ∈ Set.Icc (167 / 250) (337 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((671 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_956 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_957 ⟨hr,ha.2⟩ hz
theorem cover_958_959 {a z : ℝ} (ha : a ∈ Set.Icc (337 / 500) (17 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((677 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_958 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_959 ⟨hr,ha.2⟩ hz
theorem cover_956_959 {a z : ℝ} (ha : a ∈ Set.Icc (167 / 250) (17 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((337 / 500):ℝ) with hl | hr
  · exact cover_956_957 ⟨ha.1,hl⟩ hz
  · exact cover_958_959 ⟨hr,ha.2⟩ hz
theorem cover_952_959 {a z : ℝ} (ha : a ∈ Set.Icc (82 / 125) (17 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((167 / 250):ℝ) with hl | hr
  · exact cover_952_955 ⟨ha.1,hl⟩ hz
  · exact cover_956_959 ⟨hr,ha.2⟩ hz
theorem cover_944_959 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 125) (17 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((82 / 125):ℝ) with hl | hr
  · exact cover_944_951 ⟨ha.1,hl⟩ hz
  · exact cover_952_959 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


