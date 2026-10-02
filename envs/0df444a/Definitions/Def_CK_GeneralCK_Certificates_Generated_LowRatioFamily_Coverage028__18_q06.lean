-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q06
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:07:06.04612+00:00
-- url     : https://prove2.me/theorems/7376a217-153d-4381-841d-30b0c20198ea
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 7 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 7 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 7 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage028 (+17 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage029, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage030, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage031, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage032, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage033, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage034, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage035, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage036, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage037, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage038, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage039, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage040, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage041, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage042, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage043, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage044, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage045) (piece 7 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q05
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0543__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0550__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0557__7

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_544_545 {a z : ℝ} (ha : a ∈ Set.Icc (111 / 500) (223 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((89 / 400):ℝ) with hl | hr
  · exact curvature_leaf_544 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_545 ⟨hr,ha.2⟩ hz
theorem cover_546_547 {a z : ℝ} (ha : a ∈ Set.Icc (223 / 1000) (28 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((447 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_546 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_547 ⟨hr,ha.2⟩ hz
theorem cover_544_547 {a z : ℝ} (ha : a ∈ Set.Icc (111 / 500) (28 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((223 / 1000):ℝ) with hl | hr
  · exact cover_544_545 ⟨ha.1,hl⟩ hz
  · exact cover_546_547 ⟨hr,ha.2⟩ hz
theorem cover_548_549 {a z : ℝ} (ha : a ∈ Set.Icc (28 / 125) (9 / 40))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((449 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_548 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_549 ⟨hr,ha.2⟩ hz
theorem cover_550_551 {a z : ℝ} (ha : a ∈ Set.Icc (9 / 40) (113 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((451 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_550 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_551 ⟨hr,ha.2⟩ hz
theorem cover_548_551 {a z : ℝ} (ha : a ∈ Set.Icc (28 / 125) (113 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((9 / 40):ℝ) with hl | hr
  · exact cover_548_549 ⟨ha.1,hl⟩ hz
  · exact cover_550_551 ⟨hr,ha.2⟩ hz
theorem cover_544_551 {a z : ℝ} (ha : a ∈ Set.Icc (111 / 500) (113 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((28 / 125):ℝ) with hl | hr
  · exact cover_544_547 ⟨ha.1,hl⟩ hz
  · exact cover_548_551 ⟨hr,ha.2⟩ hz
theorem cover_552_553 {a z : ℝ} (ha : a ∈ Set.Icc (113 / 500) (227 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((453 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_552 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_553 ⟨hr,ha.2⟩ hz
theorem cover_554_555 {a z : ℝ} (ha : a ∈ Set.Icc (227 / 1000) (57 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((91 / 400):ℝ) with hl | hr
  · exact curvature_leaf_554 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_555 ⟨hr,ha.2⟩ hz
theorem cover_552_555 {a z : ℝ} (ha : a ∈ Set.Icc (113 / 500) (57 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((227 / 1000):ℝ) with hl | hr
  · exact cover_552_553 ⟨ha.1,hl⟩ hz
  · exact cover_554_555 ⟨hr,ha.2⟩ hz
theorem cover_556_557 {a z : ℝ} (ha : a ∈ Set.Icc (57 / 250) (229 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((457 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_556 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_557 ⟨hr,ha.2⟩ hz
theorem cover_558_559 {a z : ℝ} (ha : a ∈ Set.Icc (229 / 1000) (23 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((459 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_558 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_559 ⟨hr,ha.2⟩ hz
theorem cover_556_559 {a z : ℝ} (ha : a ∈ Set.Icc (57 / 250) (23 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((229 / 1000):ℝ) with hl | hr
  · exact cover_556_557 ⟨ha.1,hl⟩ hz
  · exact cover_558_559 ⟨hr,ha.2⟩ hz
theorem cover_552_559 {a z : ℝ} (ha : a ∈ Set.Icc (113 / 500) (23 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((57 / 250):ℝ) with hl | hr
  · exact cover_552_555 ⟨ha.1,hl⟩ hz
  · exact cover_556_559 ⟨hr,ha.2⟩ hz
theorem cover_544_559 {a z : ℝ} (ha : a ∈ Set.Icc (111 / 500) (23 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((113 / 500):ℝ) with hl | hr
  · exact cover_544_551 ⟨ha.1,hl⟩ hz
  · exact cover_552_559 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


