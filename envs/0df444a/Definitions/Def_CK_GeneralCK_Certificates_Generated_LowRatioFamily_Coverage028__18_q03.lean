-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q03
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:55:56.296782+00:00
-- url     : https://prove2.me/theorems/8d621504-32f9-4b6f-9948-9360f73556e4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 4 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 4 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 4 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage028 (+17 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage029, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage030, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage031, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage032, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage033, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage034, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage035, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage036, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage037, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage038, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage039, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage040, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage041, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage042, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage043, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage044, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage045) (piece 4 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q02
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0491__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0497__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0503__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0509__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_496_497 {a z : ℝ} (ha : a ∈ Set.Icc (499 / 2500) (999 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1997 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_496 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_497 ⟨hr,ha.2⟩ hz
theorem cover_498_499 {a z : ℝ} (ha : a ∈ Set.Icc (999 / 5000) (1 / 5))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1999 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_498 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_499 ⟨hr,ha.2⟩ hz
theorem cover_496_499 {a z : ℝ} (ha : a ∈ Set.Icc (499 / 2500) (1 / 5))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((999 / 5000):ℝ) with hl | hr
  · exact cover_496_497 ⟨ha.1,hl⟩ hz
  · exact cover_498_499 ⟨hr,ha.2⟩ hz
theorem cover_500_501 {a z : ℝ} (ha : a ∈ Set.Icc (1 / 5) (201 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((401 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_500 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_501 ⟨hr,ha.2⟩ hz
theorem cover_502_503 {a z : ℝ} (ha : a ∈ Set.Icc (201 / 1000) (101 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((403 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_502 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_503 ⟨hr,ha.2⟩ hz
theorem cover_500_503 {a z : ℝ} (ha : a ∈ Set.Icc (1 / 5) (101 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((201 / 1000):ℝ) with hl | hr
  · exact cover_500_501 ⟨ha.1,hl⟩ hz
  · exact cover_502_503 ⟨hr,ha.2⟩ hz
theorem cover_496_503 {a z : ℝ} (ha : a ∈ Set.Icc (499 / 2500) (101 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1 / 5):ℝ) with hl | hr
  · exact cover_496_499 ⟨ha.1,hl⟩ hz
  · exact cover_500_503 ⟨hr,ha.2⟩ hz
theorem cover_504_505 {a z : ℝ} (ha : a ∈ Set.Icc (101 / 500) (203 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((81 / 400):ℝ) with hl | hr
  · exact curvature_leaf_504 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_505 ⟨hr,ha.2⟩ hz
theorem cover_506_507 {a z : ℝ} (ha : a ∈ Set.Icc (203 / 1000) (51 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((407 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_506 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_507 ⟨hr,ha.2⟩ hz
theorem cover_504_507 {a z : ℝ} (ha : a ∈ Set.Icc (101 / 500) (51 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((203 / 1000):ℝ) with hl | hr
  · exact cover_504_505 ⟨ha.1,hl⟩ hz
  · exact cover_506_507 ⟨hr,ha.2⟩ hz
theorem cover_508_509 {a z : ℝ} (ha : a ∈ Set.Icc (51 / 250) (41 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((409 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_508 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_509 ⟨hr,ha.2⟩ hz
theorem cover_510_511 {a z : ℝ} (ha : a ∈ Set.Icc (41 / 200) (103 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((411 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_510 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_511 ⟨hr,ha.2⟩ hz
theorem cover_508_511 {a z : ℝ} (ha : a ∈ Set.Icc (51 / 250) (103 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((41 / 200):ℝ) with hl | hr
  · exact cover_508_509 ⟨ha.1,hl⟩ hz
  · exact cover_510_511 ⟨hr,ha.2⟩ hz
theorem cover_504_511 {a z : ℝ} (ha : a ∈ Set.Icc (101 / 500) (103 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((51 / 250):ℝ) with hl | hr
  · exact cover_504_507 ⟨ha.1,hl⟩ hz
  · exact cover_508_511 ⟨hr,ha.2⟩ hz
theorem cover_496_511 {a z : ℝ} (ha : a ∈ Set.Icc (499 / 2500) (103 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((101 / 500):ℝ) with hl | hr
  · exact cover_496_503 ⟨ha.1,hl⟩ hz
  · exact cover_504_511 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


