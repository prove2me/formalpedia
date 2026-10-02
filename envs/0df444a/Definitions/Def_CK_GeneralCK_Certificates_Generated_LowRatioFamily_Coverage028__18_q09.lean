-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q09
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q09
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:31:00.96524+00:00
-- url     : https://prove2.me/theorems/ff350b5f-e138-423d-bed0-7732a51d64b8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 10 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 10 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 10 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage028 (+17 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage029, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage030, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage031, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage032, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage033, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage034, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage035, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage036, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage037, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage038, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage039, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage040, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage041, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage042, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage043, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage044, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage045) (piece 10 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q08
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0591__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0598__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0604__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_592_593 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 500) (247 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((493 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_592 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_593 ⟨hr,ha.2⟩ hz
theorem cover_594_595 {a z : ℝ} (ha : a ∈ Set.Icc (247 / 1000) (31 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((99 / 400):ℝ) with hl | hr
  · exact curvature_leaf_594 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_595 ⟨hr,ha.2⟩ hz
theorem cover_592_595 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 500) (31 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((247 / 1000):ℝ) with hl | hr
  · exact cover_592_593 ⟨ha.1,hl⟩ hz
  · exact cover_594_595 ⟨hr,ha.2⟩ hz
theorem cover_596_597 {a z : ℝ} (ha : a ∈ Set.Icc (31 / 125) (249 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((497 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_596 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_597 ⟨hr,ha.2⟩ hz
theorem cover_598_599 {a z : ℝ} (ha : a ∈ Set.Icc (249 / 1000) (1 / 4))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((499 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_598 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_599 ⟨hr,ha.2⟩ hz
theorem cover_596_599 {a z : ℝ} (ha : a ∈ Set.Icc (31 / 125) (1 / 4))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((249 / 1000):ℝ) with hl | hr
  · exact cover_596_597 ⟨ha.1,hl⟩ hz
  · exact cover_598_599 ⟨hr,ha.2⟩ hz
theorem cover_592_599 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 500) (1 / 4))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((31 / 125):ℝ) with hl | hr
  · exact cover_592_595 ⟨ha.1,hl⟩ hz
  · exact cover_596_599 ⟨hr,ha.2⟩ hz
theorem cover_600_601 {a z : ℝ} (ha : a ∈ Set.Icc (1 / 4) (251 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((501 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_600 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_601 ⟨hr,ha.2⟩ hz
theorem cover_602_603 {a z : ℝ} (ha : a ∈ Set.Icc (251 / 1000) (63 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((503 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_602 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_603 ⟨hr,ha.2⟩ hz
theorem cover_600_603 {a z : ℝ} (ha : a ∈ Set.Icc (1 / 4) (63 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((251 / 1000):ℝ) with hl | hr
  · exact cover_600_601 ⟨ha.1,hl⟩ hz
  · exact cover_602_603 ⟨hr,ha.2⟩ hz
theorem cover_604_605 {a z : ℝ} (ha : a ∈ Set.Icc (63 / 250) (253 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((101 / 400):ℝ) with hl | hr
  · exact curvature_leaf_604 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_605 ⟨hr,ha.2⟩ hz
theorem cover_606_607 {a z : ℝ} (ha : a ∈ Set.Icc (253 / 1000) (127 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((507 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_606 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_607 ⟨hr,ha.2⟩ hz
theorem cover_604_607 {a z : ℝ} (ha : a ∈ Set.Icc (63 / 250) (127 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((253 / 1000):ℝ) with hl | hr
  · exact cover_604_605 ⟨ha.1,hl⟩ hz
  · exact cover_606_607 ⟨hr,ha.2⟩ hz
theorem cover_600_607 {a z : ℝ} (ha : a ∈ Set.Icc (1 / 4) (127 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((63 / 250):ℝ) with hl | hr
  · exact cover_600_603 ⟨ha.1,hl⟩ hz
  · exact cover_604_607 ⟨hr,ha.2⟩ hz
theorem cover_592_607 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 500) (127 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1 / 4):ℝ) with hl | hr
  · exact cover_592_599 ⟨ha.1,hl⟩ hz
  · exact cover_600_607 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


