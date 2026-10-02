-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q07
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:25:03.099144+00:00
-- url     : https://prove2.me/theorems/cbec9885-cab1-4715-b687-1371f5cbe999
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 8 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 8 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 8 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage028 (+17 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage029, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage030, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage031, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage032, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage033, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage034, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage035, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage036, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage037, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage038, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage039, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage040, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage041, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage042, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage043, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage044, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage045) (piece 8 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q06
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0557__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0564__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0571__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_560_561 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 100) (231 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((461 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_560 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_561 ⟨hr,ha.2⟩ hz
theorem cover_562_563 {a z : ℝ} (ha : a ∈ Set.Icc (231 / 1000) (29 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((463 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_562 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_563 ⟨hr,ha.2⟩ hz
theorem cover_560_563 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 100) (29 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((231 / 1000):ℝ) with hl | hr
  · exact cover_560_561 ⟨ha.1,hl⟩ hz
  · exact cover_562_563 ⟨hr,ha.2⟩ hz
theorem cover_564_565 {a z : ℝ} (ha : a ∈ Set.Icc (29 / 125) (233 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((93 / 400):ℝ) with hl | hr
  · exact curvature_leaf_564 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_565 ⟨hr,ha.2⟩ hz
theorem cover_566_567 {a z : ℝ} (ha : a ∈ Set.Icc (233 / 1000) (117 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((467 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_566 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_567 ⟨hr,ha.2⟩ hz
theorem cover_564_567 {a z : ℝ} (ha : a ∈ Set.Icc (29 / 125) (117 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((233 / 1000):ℝ) with hl | hr
  · exact cover_564_565 ⟨ha.1,hl⟩ hz
  · exact cover_566_567 ⟨hr,ha.2⟩ hz
theorem cover_560_567 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 100) (117 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((29 / 125):ℝ) with hl | hr
  · exact cover_560_563 ⟨ha.1,hl⟩ hz
  · exact cover_564_567 ⟨hr,ha.2⟩ hz
theorem cover_568_569 {a z : ℝ} (ha : a ∈ Set.Icc (117 / 500) (47 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((469 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_568 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_569 ⟨hr,ha.2⟩ hz
theorem cover_570_571 {a z : ℝ} (ha : a ∈ Set.Icc (47 / 200) (59 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((471 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_570 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_571 ⟨hr,ha.2⟩ hz
theorem cover_568_571 {a z : ℝ} (ha : a ∈ Set.Icc (117 / 500) (59 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((47 / 200):ℝ) with hl | hr
  · exact cover_568_569 ⟨ha.1,hl⟩ hz
  · exact cover_570_571 ⟨hr,ha.2⟩ hz
theorem cover_572_573 {a z : ℝ} (ha : a ∈ Set.Icc (59 / 250) (237 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((473 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_572 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_573 ⟨hr,ha.2⟩ hz
theorem cover_574_575 {a z : ℝ} (ha : a ∈ Set.Icc (237 / 1000) (119 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((19 / 80):ℝ) with hl | hr
  · exact curvature_leaf_574 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_575 ⟨hr,ha.2⟩ hz
theorem cover_572_575 {a z : ℝ} (ha : a ∈ Set.Icc (59 / 250) (119 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((237 / 1000):ℝ) with hl | hr
  · exact cover_572_573 ⟨ha.1,hl⟩ hz
  · exact cover_574_575 ⟨hr,ha.2⟩ hz
theorem cover_568_575 {a z : ℝ} (ha : a ∈ Set.Icc (117 / 500) (119 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((59 / 250):ℝ) with hl | hr
  · exact cover_568_571 ⟨ha.1,hl⟩ hz
  · exact cover_572_575 ⟨hr,ha.2⟩ hz
theorem cover_560_575 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 100) (119 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((117 / 500):ℝ) with hl | hr
  · exact cover_560_567 ⟨ha.1,hl⟩ hz
  · exact cover_568_575 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


