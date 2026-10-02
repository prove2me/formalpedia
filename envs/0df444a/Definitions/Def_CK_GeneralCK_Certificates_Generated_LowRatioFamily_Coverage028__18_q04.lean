-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q04
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T14:01:38.082296+00:00
-- url     : https://prove2.me/theorems/be92c273-3fca-4385-a631-ae6b30ec4bc2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 5 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 5 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 5 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage028 (+17 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage029, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage030, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage031, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage032, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage033, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage034, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage035, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage036, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage037, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage038, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage039, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage040, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage041, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage042, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage043, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage044, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage045) (piece 5 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q03
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0509__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0515__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0522__7

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_512_513 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 500) (207 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((413 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_512 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_513 ⟨hr,ha.2⟩ hz
theorem cover_514_515 {a z : ℝ} (ha : a ∈ Set.Icc (207 / 1000) (26 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((83 / 400):ℝ) with hl | hr
  · exact curvature_leaf_514 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_515 ⟨hr,ha.2⟩ hz
theorem cover_512_515 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 500) (26 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((207 / 1000):ℝ) with hl | hr
  · exact cover_512_513 ⟨ha.1,hl⟩ hz
  · exact cover_514_515 ⟨hr,ha.2⟩ hz
theorem cover_516_517 {a z : ℝ} (ha : a ∈ Set.Icc (26 / 125) (209 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((417 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_516 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_517 ⟨hr,ha.2⟩ hz
theorem cover_518_519 {a z : ℝ} (ha : a ∈ Set.Icc (209 / 1000) (21 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((419 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_518 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_519 ⟨hr,ha.2⟩ hz
theorem cover_516_519 {a z : ℝ} (ha : a ∈ Set.Icc (26 / 125) (21 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((209 / 1000):ℝ) with hl | hr
  · exact cover_516_517 ⟨ha.1,hl⟩ hz
  · exact cover_518_519 ⟨hr,ha.2⟩ hz
theorem cover_512_519 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 500) (21 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((26 / 125):ℝ) with hl | hr
  · exact cover_512_515 ⟨ha.1,hl⟩ hz
  · exact cover_516_519 ⟨hr,ha.2⟩ hz
theorem cover_520_521 {a z : ℝ} (ha : a ∈ Set.Icc (21 / 100) (211 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((421 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_520 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_521 ⟨hr,ha.2⟩ hz
theorem cover_522_523 {a z : ℝ} (ha : a ∈ Set.Icc (211 / 1000) (53 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((423 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_522 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_523 ⟨hr,ha.2⟩ hz
theorem cover_520_523 {a z : ℝ} (ha : a ∈ Set.Icc (21 / 100) (53 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((211 / 1000):ℝ) with hl | hr
  · exact cover_520_521 ⟨ha.1,hl⟩ hz
  · exact cover_522_523 ⟨hr,ha.2⟩ hz
theorem cover_524_525 {a z : ℝ} (ha : a ∈ Set.Icc (53 / 250) (213 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((17 / 80):ℝ) with hl | hr
  · exact curvature_leaf_524 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_525 ⟨hr,ha.2⟩ hz
theorem cover_526_527 {a z : ℝ} (ha : a ∈ Set.Icc (213 / 1000) (107 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((427 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_526 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_527 ⟨hr,ha.2⟩ hz
theorem cover_524_527 {a z : ℝ} (ha : a ∈ Set.Icc (53 / 250) (107 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((213 / 1000):ℝ) with hl | hr
  · exact cover_524_525 ⟨ha.1,hl⟩ hz
  · exact cover_526_527 ⟨hr,ha.2⟩ hz
theorem cover_520_527 {a z : ℝ} (ha : a ∈ Set.Icc (21 / 100) (107 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((53 / 250):ℝ) with hl | hr
  · exact cover_520_523 ⟨ha.1,hl⟩ hz
  · exact cover_524_527 ⟨hr,ha.2⟩ hz
theorem cover_512_527 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 500) (107 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((21 / 100):ℝ) with hl | hr
  · exact cover_512_519 ⟨ha.1,hl⟩ hz
  · exact cover_520_527 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


