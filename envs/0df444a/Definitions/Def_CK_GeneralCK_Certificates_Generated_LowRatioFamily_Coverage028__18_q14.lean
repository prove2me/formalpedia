-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q14
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T00:54:22.728932+00:00
-- url     : https://prove2.me/theorems/c52a709e-dea5-4b9a-958c-9add7408024a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 15 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 15 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 15 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage028 (+17 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage029, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage030, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage031, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage032, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage033, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage034, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage035, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage036, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage037, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage038, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage039, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage040, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage041, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage042, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage043, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage044, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage045) (piece 15 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q13
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0671__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0677__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0683__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_672_673 {a z : ℝ} (ha : a ∈ Set.Icc (143 / 500) (287 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((573 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_672 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_673 ⟨hr,ha.2⟩ hz
theorem cover_674_675 {a z : ℝ} (ha : a ∈ Set.Icc (287 / 1000) (36 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((23 / 80):ℝ) with hl | hr
  · exact curvature_leaf_674 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_675 ⟨hr,ha.2⟩ hz
theorem cover_672_675 {a z : ℝ} (ha : a ∈ Set.Icc (143 / 500) (36 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((287 / 1000):ℝ) with hl | hr
  · exact cover_672_673 ⟨ha.1,hl⟩ hz
  · exact cover_674_675 ⟨hr,ha.2⟩ hz
theorem cover_676_677 {a z : ℝ} (ha : a ∈ Set.Icc (36 / 125) (289 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((577 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_676 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_677 ⟨hr,ha.2⟩ hz
theorem cover_678_679 {a z : ℝ} (ha : a ∈ Set.Icc (289 / 1000) (29 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((579 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_678 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_679 ⟨hr,ha.2⟩ hz
theorem cover_676_679 {a z : ℝ} (ha : a ∈ Set.Icc (36 / 125) (29 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((289 / 1000):ℝ) with hl | hr
  · exact cover_676_677 ⟨ha.1,hl⟩ hz
  · exact cover_678_679 ⟨hr,ha.2⟩ hz
theorem cover_672_679 {a z : ℝ} (ha : a ∈ Set.Icc (143 / 500) (29 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((36 / 125):ℝ) with hl | hr
  · exact cover_672_675 ⟨ha.1,hl⟩ hz
  · exact cover_676_679 ⟨hr,ha.2⟩ hz
theorem cover_680_681 {a z : ℝ} (ha : a ∈ Set.Icc (29 / 100) (291 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((581 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_680 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_681 ⟨hr,ha.2⟩ hz
theorem cover_682_683 {a z : ℝ} (ha : a ∈ Set.Icc (291 / 1000) (73 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((583 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_682 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_683 ⟨hr,ha.2⟩ hz
theorem cover_680_683 {a z : ℝ} (ha : a ∈ Set.Icc (29 / 100) (73 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((291 / 1000):ℝ) with hl | hr
  · exact cover_680_681 ⟨ha.1,hl⟩ hz
  · exact cover_682_683 ⟨hr,ha.2⟩ hz
theorem cover_684_685 {a z : ℝ} (ha : a ∈ Set.Icc (73 / 250) (293 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((117 / 400):ℝ) with hl | hr
  · exact curvature_leaf_684 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_685 ⟨hr,ha.2⟩ hz
theorem cover_686_687 {a z : ℝ} (ha : a ∈ Set.Icc (293 / 1000) (147 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((587 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_686 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_687 ⟨hr,ha.2⟩ hz
theorem cover_684_687 {a z : ℝ} (ha : a ∈ Set.Icc (73 / 250) (147 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((293 / 1000):ℝ) with hl | hr
  · exact cover_684_685 ⟨ha.1,hl⟩ hz
  · exact cover_686_687 ⟨hr,ha.2⟩ hz
theorem cover_680_687 {a z : ℝ} (ha : a ∈ Set.Icc (29 / 100) (147 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((73 / 250):ℝ) with hl | hr
  · exact cover_680_683 ⟨ha.1,hl⟩ hz
  · exact cover_684_687 ⟨hr,ha.2⟩ hz
theorem cover_672_687 {a z : ℝ} (ha : a ∈ Set.Icc (143 / 500) (147 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((29 / 100):ℝ) with hl | hr
  · exact cover_672_679 ⟨ha.1,hl⟩ hz
  · exact cover_680_687 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


