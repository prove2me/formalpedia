-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q01
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:48:12.91943+00:00
-- url     : https://prove2.me/theorems/5e2edd28-d4b1-4989-a69b-5e36a97bfb1a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 2 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 2 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 2 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage028 (+17 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage029, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage030, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage031, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage032, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage033, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage034, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage035, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage036, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage037, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage038, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage039, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage040, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage041, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage042, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage043, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage044, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage045) (piece 2 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0461__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0467__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0473__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0479__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_464_465 {a z : ℝ} (ha : a ∈ Set.Icc (491 / 2500) (983 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((393 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_464 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_465 ⟨hr,ha.2⟩ hz
theorem cover_466_467 {a z : ℝ} (ha : a ∈ Set.Icc (983 / 5000) (123 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1967 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_466 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_467 ⟨hr,ha.2⟩ hz
theorem cover_464_467 {a z : ℝ} (ha : a ∈ Set.Icc (491 / 2500) (123 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((983 / 5000):ℝ) with hl | hr
  · exact cover_464_465 ⟨ha.1,hl⟩ hz
  · exact cover_466_467 ⟨hr,ha.2⟩ hz
theorem cover_468_469 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 625) (197 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1969 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_468 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_469 ⟨hr,ha.2⟩ hz
theorem cover_470_471 {a z : ℝ} (ha : a ∈ Set.Icc (197 / 1000) (493 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1971 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_470 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_471 ⟨hr,ha.2⟩ hz
theorem cover_468_471 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 625) (493 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((197 / 1000):ℝ) with hl | hr
  · exact cover_468_469 ⟨ha.1,hl⟩ hz
  · exact cover_470_471 ⟨hr,ha.2⟩ hz
theorem cover_464_471 {a z : ℝ} (ha : a ∈ Set.Icc (491 / 2500) (493 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((123 / 625):ℝ) with hl | hr
  · exact cover_464_467 ⟨ha.1,hl⟩ hz
  · exact cover_468_471 ⟨hr,ha.2⟩ hz
theorem cover_472_473 {a z : ℝ} (ha : a ∈ Set.Icc (493 / 2500) (987 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1973 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_472 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_473 ⟨hr,ha.2⟩ hz
theorem cover_474_475 {a z : ℝ} (ha : a ∈ Set.Icc (987 / 5000) (247 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((79 / 400):ℝ) with hl | hr
  · exact curvature_leaf_474 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_475 ⟨hr,ha.2⟩ hz
theorem cover_472_475 {a z : ℝ} (ha : a ∈ Set.Icc (493 / 2500) (247 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((987 / 5000):ℝ) with hl | hr
  · exact cover_472_473 ⟨ha.1,hl⟩ hz
  · exact cover_474_475 ⟨hr,ha.2⟩ hz
theorem cover_476_477 {a z : ℝ} (ha : a ∈ Set.Icc (247 / 1250) (989 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1977 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_476 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_477 ⟨hr,ha.2⟩ hz
theorem cover_478_479 {a z : ℝ} (ha : a ∈ Set.Icc (989 / 5000) (99 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1979 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_478 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_479 ⟨hr,ha.2⟩ hz
theorem cover_476_479 {a z : ℝ} (ha : a ∈ Set.Icc (247 / 1250) (99 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((989 / 5000):ℝ) with hl | hr
  · exact cover_476_477 ⟨ha.1,hl⟩ hz
  · exact cover_478_479 ⟨hr,ha.2⟩ hz
theorem cover_472_479 {a z : ℝ} (ha : a ∈ Set.Icc (493 / 2500) (99 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((247 / 1250):ℝ) with hl | hr
  · exact cover_472_475 ⟨ha.1,hl⟩ hz
  · exact cover_476_479 ⟨hr,ha.2⟩ hz
theorem cover_464_479 {a z : ℝ} (ha : a ∈ Set.Icc (491 / 2500) (99 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((493 / 2500):ℝ) with hl | hr
  · exact cover_464_471 ⟨ha.1,hl⟩ hz
  · exact cover_472_479 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


