-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q08
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q08
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:37:48.651693+00:00
-- url     : https://prove2.me/theorems/996bcb21-16e6-42e6-82d4-0af2d2af2119
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 9 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 9 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 9 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage028 (+17 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage029, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage030, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage031, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage032, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage033, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage034, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage035, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage036, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage037, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage038, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage039, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage040, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage041, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage042, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage043, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage044, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage045) (piece 9 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q07
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0571__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0577__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0584__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0591__7

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_576_577 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 500) (239 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((477 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_576 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_577 ⟨hr,ha.2⟩ hz
theorem cover_578_579 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 1000) (6 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((479 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_578 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_579 ⟨hr,ha.2⟩ hz
theorem cover_576_579 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 500) (6 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((239 / 1000):ℝ) with hl | hr
  · exact cover_576_577 ⟨ha.1,hl⟩ hz
  · exact cover_578_579 ⟨hr,ha.2⟩ hz
theorem cover_580_581 {a z : ℝ} (ha : a ∈ Set.Icc (6 / 25) (241 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((481 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_580 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_581 ⟨hr,ha.2⟩ hz
theorem cover_582_583 {a z : ℝ} (ha : a ∈ Set.Icc (241 / 1000) (121 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((483 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_582 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_583 ⟨hr,ha.2⟩ hz
theorem cover_580_583 {a z : ℝ} (ha : a ∈ Set.Icc (6 / 25) (121 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((241 / 1000):ℝ) with hl | hr
  · exact cover_580_581 ⟨ha.1,hl⟩ hz
  · exact cover_582_583 ⟨hr,ha.2⟩ hz
theorem cover_576_583 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 500) (121 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((6 / 25):ℝ) with hl | hr
  · exact cover_576_579 ⟨ha.1,hl⟩ hz
  · exact cover_580_583 ⟨hr,ha.2⟩ hz
theorem cover_584_585 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 500) (243 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((97 / 400):ℝ) with hl | hr
  · exact curvature_leaf_584 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_585 ⟨hr,ha.2⟩ hz
theorem cover_586_587 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 1000) (61 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((487 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_586 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_587 ⟨hr,ha.2⟩ hz
theorem cover_584_587 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 500) (61 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((243 / 1000):ℝ) with hl | hr
  · exact cover_584_585 ⟨ha.1,hl⟩ hz
  · exact cover_586_587 ⟨hr,ha.2⟩ hz
theorem cover_588_589 {a z : ℝ} (ha : a ∈ Set.Icc (61 / 250) (49 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((489 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_588 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_589 ⟨hr,ha.2⟩ hz
theorem cover_590_591 {a z : ℝ} (ha : a ∈ Set.Icc (49 / 200) (123 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((491 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_590 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_591 ⟨hr,ha.2⟩ hz
theorem cover_588_591 {a z : ℝ} (ha : a ∈ Set.Icc (61 / 250) (123 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((49 / 200):ℝ) with hl | hr
  · exact cover_588_589 ⟨ha.1,hl⟩ hz
  · exact cover_590_591 ⟨hr,ha.2⟩ hz
theorem cover_584_591 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 500) (123 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((61 / 250):ℝ) with hl | hr
  · exact cover_584_587 ⟨ha.1,hl⟩ hz
  · exact cover_588_591 ⟨hr,ha.2⟩ hz
theorem cover_576_591 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 500) (123 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((121 / 500):ℝ) with hl | hr
  · exact cover_576_583 ⟨ha.1,hl⟩ hz
  · exact cover_584_591 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


