-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q10
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:37:36.662488+00:00
-- url     : https://prove2.me/theorems/64ff9b06-7204-4026-bb53-f4767520f266
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 11 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 11 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 11 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage028 (+17 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage029, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage030, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage031, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage032, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage033, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage034, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage035, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage036, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage037, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage038, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage039, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage040, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage041, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage042, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage043, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage044, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage045) (piece 11 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q09
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0604__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0610__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0616__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0621__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_608_609 {a z : ℝ} (ha : a ∈ Set.Icc (127 / 500) (51 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((509 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_608 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_609 ⟨hr,ha.2⟩ hz
theorem cover_610_611 {a z : ℝ} (ha : a ∈ Set.Icc (51 / 200) (32 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((511 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_610 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_611 ⟨hr,ha.2⟩ hz
theorem cover_608_611 {a z : ℝ} (ha : a ∈ Set.Icc (127 / 500) (32 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((51 / 200):ℝ) with hl | hr
  · exact cover_608_609 ⟨ha.1,hl⟩ hz
  · exact cover_610_611 ⟨hr,ha.2⟩ hz
theorem cover_612_613 {a z : ℝ} (ha : a ∈ Set.Icc (32 / 125) (257 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((513 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_612 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_613 ⟨hr,ha.2⟩ hz
theorem cover_614_615 {a z : ℝ} (ha : a ∈ Set.Icc (257 / 1000) (129 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((103 / 400):ℝ) with hl | hr
  · exact curvature_leaf_614 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_615 ⟨hr,ha.2⟩ hz
theorem cover_612_615 {a z : ℝ} (ha : a ∈ Set.Icc (32 / 125) (129 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((257 / 1000):ℝ) with hl | hr
  · exact cover_612_613 ⟨ha.1,hl⟩ hz
  · exact cover_614_615 ⟨hr,ha.2⟩ hz
theorem cover_608_615 {a z : ℝ} (ha : a ∈ Set.Icc (127 / 500) (129 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((32 / 125):ℝ) with hl | hr
  · exact cover_608_611 ⟨ha.1,hl⟩ hz
  · exact cover_612_615 ⟨hr,ha.2⟩ hz
theorem cover_616_617 {a z : ℝ} (ha : a ∈ Set.Icc (129 / 500) (259 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((517 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_616 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_617 ⟨hr,ha.2⟩ hz
theorem cover_618_619 {a z : ℝ} (ha : a ∈ Set.Icc (259 / 1000) (13 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((519 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_618 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_619 ⟨hr,ha.2⟩ hz
theorem cover_616_619 {a z : ℝ} (ha : a ∈ Set.Icc (129 / 500) (13 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((259 / 1000):ℝ) with hl | hr
  · exact cover_616_617 ⟨ha.1,hl⟩ hz
  · exact cover_618_619 ⟨hr,ha.2⟩ hz
theorem cover_620_621 {a z : ℝ} (ha : a ∈ Set.Icc (13 / 50) (261 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((521 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_620 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_621 ⟨hr,ha.2⟩ hz
theorem cover_622_623 {a z : ℝ} (ha : a ∈ Set.Icc (261 / 1000) (131 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((523 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_622 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_623 ⟨hr,ha.2⟩ hz
theorem cover_620_623 {a z : ℝ} (ha : a ∈ Set.Icc (13 / 50) (131 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((261 / 1000):ℝ) with hl | hr
  · exact cover_620_621 ⟨ha.1,hl⟩ hz
  · exact cover_622_623 ⟨hr,ha.2⟩ hz
theorem cover_616_623 {a z : ℝ} (ha : a ∈ Set.Icc (129 / 500) (131 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((13 / 50):ℝ) with hl | hr
  · exact cover_616_619 ⟨ha.1,hl⟩ hz
  · exact cover_620_623 ⟨hr,ha.2⟩ hz
theorem cover_608_623 {a z : ℝ} (ha : a ∈ Set.Icc (127 / 500) (131 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((129 / 500):ℝ) with hl | hr
  · exact cover_608_615 ⟨ha.1,hl⟩ hz
  · exact cover_616_623 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


