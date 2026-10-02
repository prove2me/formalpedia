-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q02
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:52:10.248683+00:00
-- url     : https://prove2.me/theorems/057dafb0-7ce3-485c-a47d-597960281ce3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 3 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 3 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 3 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage028 (+17 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage029, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage030, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage031, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage032, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage033, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage034, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage035, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage036, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage037, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage038, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage039, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage040, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage041, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage042, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage043, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage044, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage045) (piece 3 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q01
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0479__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0485__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0491__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_480_481 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 500) (991 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1981 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_480 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_481 ⟨hr,ha.2⟩ hz
theorem cover_482_483 {a z : ℝ} (ha : a ∈ Set.Icc (991 / 5000) (124 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1983 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_482 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_483 ⟨hr,ha.2⟩ hz
theorem cover_480_483 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 500) (124 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((991 / 5000):ℝ) with hl | hr
  · exact cover_480_481 ⟨ha.1,hl⟩ hz
  · exact cover_482_483 ⟨hr,ha.2⟩ hz
theorem cover_484_485 {a z : ℝ} (ha : a ∈ Set.Icc (124 / 625) (993 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((397 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_484 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_485 ⟨hr,ha.2⟩ hz
theorem cover_486_487 {a z : ℝ} (ha : a ∈ Set.Icc (993 / 5000) (497 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1987 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_486 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_487 ⟨hr,ha.2⟩ hz
theorem cover_484_487 {a z : ℝ} (ha : a ∈ Set.Icc (124 / 625) (497 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((993 / 5000):ℝ) with hl | hr
  · exact cover_484_485 ⟨ha.1,hl⟩ hz
  · exact cover_486_487 ⟨hr,ha.2⟩ hz
theorem cover_480_487 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 500) (497 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((124 / 625):ℝ) with hl | hr
  · exact cover_480_483 ⟨ha.1,hl⟩ hz
  · exact cover_484_487 ⟨hr,ha.2⟩ hz
theorem cover_488_489 {a z : ℝ} (ha : a ∈ Set.Icc (497 / 2500) (199 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1989 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_488 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_489 ⟨hr,ha.2⟩ hz
theorem cover_490_491 {a z : ℝ} (ha : a ∈ Set.Icc (199 / 1000) (249 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1991 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_490 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_491 ⟨hr,ha.2⟩ hz
theorem cover_488_491 {a z : ℝ} (ha : a ∈ Set.Icc (497 / 2500) (249 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((199 / 1000):ℝ) with hl | hr
  · exact cover_488_489 ⟨ha.1,hl⟩ hz
  · exact cover_490_491 ⟨hr,ha.2⟩ hz
theorem cover_492_493 {a z : ℝ} (ha : a ∈ Set.Icc (249 / 1250) (997 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1993 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_492 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_493 ⟨hr,ha.2⟩ hz
theorem cover_494_495 {a z : ℝ} (ha : a ∈ Set.Icc (997 / 5000) (499 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((399 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_494 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_495 ⟨hr,ha.2⟩ hz
theorem cover_492_495 {a z : ℝ} (ha : a ∈ Set.Icc (249 / 1250) (499 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((997 / 5000):ℝ) with hl | hr
  · exact cover_492_493 ⟨ha.1,hl⟩ hz
  · exact cover_494_495 ⟨hr,ha.2⟩ hz
theorem cover_488_495 {a z : ℝ} (ha : a ∈ Set.Icc (497 / 2500) (499 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((249 / 1250):ℝ) with hl | hr
  · exact cover_488_491 ⟨ha.1,hl⟩ hz
  · exact cover_492_495 ⟨hr,ha.2⟩ hz
theorem cover_480_495 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 500) (499 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((497 / 2500):ℝ) with hl | hr
  · exact cover_480_487 ⟨ha.1,hl⟩ hz
  · exact cover_488_495 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


