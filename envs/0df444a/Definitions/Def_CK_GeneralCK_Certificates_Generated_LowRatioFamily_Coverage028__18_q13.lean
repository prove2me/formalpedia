-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q13
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:23:13.713647+00:00
-- url     : https://prove2.me/theorems/7ca0ee3b-3b61-483a-adb6-5be3cf6ac112
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 14 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 14 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 14 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage028 (+17 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage029, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage030, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage031, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage032, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage033, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage034, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage035, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage036, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage037, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage038, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage039, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage040, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage041, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage042, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage043, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage044, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage045) (piece 14 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q12
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0655__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0660__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0665__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0671__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_656_657 {a z : ℝ} (ha : a ∈ Set.Icc (139 / 500) (279 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((557 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_656 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_657 ⟨hr,ha.2⟩ hz
theorem cover_658_659 {a z : ℝ} (ha : a ∈ Set.Icc (279 / 1000) (7 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((559 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_658 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_659 ⟨hr,ha.2⟩ hz
theorem cover_656_659 {a z : ℝ} (ha : a ∈ Set.Icc (139 / 500) (7 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((279 / 1000):ℝ) with hl | hr
  · exact cover_656_657 ⟨ha.1,hl⟩ hz
  · exact cover_658_659 ⟨hr,ha.2⟩ hz
theorem cover_660_661 {a z : ℝ} (ha : a ∈ Set.Icc (7 / 25) (281 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((561 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_660 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_661 ⟨hr,ha.2⟩ hz
theorem cover_662_663 {a z : ℝ} (ha : a ∈ Set.Icc (281 / 1000) (141 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((563 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_662 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_663 ⟨hr,ha.2⟩ hz
theorem cover_660_663 {a z : ℝ} (ha : a ∈ Set.Icc (7 / 25) (141 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((281 / 1000):ℝ) with hl | hr
  · exact cover_660_661 ⟨ha.1,hl⟩ hz
  · exact cover_662_663 ⟨hr,ha.2⟩ hz
theorem cover_656_663 {a z : ℝ} (ha : a ∈ Set.Icc (139 / 500) (141 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((7 / 25):ℝ) with hl | hr
  · exact cover_656_659 ⟨ha.1,hl⟩ hz
  · exact cover_660_663 ⟨hr,ha.2⟩ hz
theorem cover_664_665 {a z : ℝ} (ha : a ∈ Set.Icc (141 / 500) (283 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((113 / 400):ℝ) with hl | hr
  · exact curvature_leaf_664 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_665 ⟨hr,ha.2⟩ hz
theorem cover_666_667 {a z : ℝ} (ha : a ∈ Set.Icc (283 / 1000) (71 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((567 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_666 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_667 ⟨hr,ha.2⟩ hz
theorem cover_664_667 {a z : ℝ} (ha : a ∈ Set.Icc (141 / 500) (71 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((283 / 1000):ℝ) with hl | hr
  · exact cover_664_665 ⟨ha.1,hl⟩ hz
  · exact cover_666_667 ⟨hr,ha.2⟩ hz
theorem cover_668_669 {a z : ℝ} (ha : a ∈ Set.Icc (71 / 250) (57 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((569 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_668 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_669 ⟨hr,ha.2⟩ hz
theorem cover_670_671 {a z : ℝ} (ha : a ∈ Set.Icc (57 / 200) (143 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((571 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_670 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_671 ⟨hr,ha.2⟩ hz
theorem cover_668_671 {a z : ℝ} (ha : a ∈ Set.Icc (71 / 250) (143 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((57 / 200):ℝ) with hl | hr
  · exact cover_668_669 ⟨ha.1,hl⟩ hz
  · exact cover_670_671 ⟨hr,ha.2⟩ hz
theorem cover_664_671 {a z : ℝ} (ha : a ∈ Set.Icc (141 / 500) (143 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((71 / 250):ℝ) with hl | hr
  · exact cover_664_667 ⟨ha.1,hl⟩ hz
  · exact cover_668_671 ⟨hr,ha.2⟩ hz
theorem cover_656_671 {a z : ℝ} (ha : a ∈ Set.Icc (139 / 500) (143 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((141 / 500):ℝ) with hl | hr
  · exact cover_656_663 ⟨ha.1,hl⟩ hz
  · exact cover_664_671 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


