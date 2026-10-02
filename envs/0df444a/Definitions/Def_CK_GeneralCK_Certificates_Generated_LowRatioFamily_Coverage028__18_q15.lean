-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q15
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T01:49:11.726013+00:00
-- url     : https://prove2.me/theorems/820d4108-030f-44f4-bf9b-652a3bd22759
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 16 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 16 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 16 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage028 (+17 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage029, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage030, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage031, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage032, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage033, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage034, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage035, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage036, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage037, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage038, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage039, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage040, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage041, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage042, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage043, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage044, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage045) (piece 16 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q14
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0683__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0689__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0694__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0700__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_688_689 {a z : ℝ} (ha : a ∈ Set.Icc (147 / 500) (59 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((589 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_688 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_689 ⟨hr,ha.2⟩ hz
theorem cover_690_691 {a z : ℝ} (ha : a ∈ Set.Icc (59 / 200) (37 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((591 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_690 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_691 ⟨hr,ha.2⟩ hz
theorem cover_688_691 {a z : ℝ} (ha : a ∈ Set.Icc (147 / 500) (37 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((59 / 200):ℝ) with hl | hr
  · exact cover_688_689 ⟨ha.1,hl⟩ hz
  · exact cover_690_691 ⟨hr,ha.2⟩ hz
theorem cover_692_693 {a z : ℝ} (ha : a ∈ Set.Icc (37 / 125) (297 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((593 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_692 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_693 ⟨hr,ha.2⟩ hz
theorem cover_694_695 {a z : ℝ} (ha : a ∈ Set.Icc (297 / 1000) (149 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((119 / 400):ℝ) with hl | hr
  · exact curvature_leaf_694 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_695 ⟨hr,ha.2⟩ hz
theorem cover_692_695 {a z : ℝ} (ha : a ∈ Set.Icc (37 / 125) (149 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((297 / 1000):ℝ) with hl | hr
  · exact cover_692_693 ⟨ha.1,hl⟩ hz
  · exact cover_694_695 ⟨hr,ha.2⟩ hz
theorem cover_688_695 {a z : ℝ} (ha : a ∈ Set.Icc (147 / 500) (149 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((37 / 125):ℝ) with hl | hr
  · exact cover_688_691 ⟨ha.1,hl⟩ hz
  · exact cover_692_695 ⟨hr,ha.2⟩ hz
theorem cover_696_697 {a z : ℝ} (ha : a ∈ Set.Icc (149 / 500) (299 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((597 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_696 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_697 ⟨hr,ha.2⟩ hz
theorem cover_698_699 {a z : ℝ} (ha : a ∈ Set.Icc (299 / 1000) (3 / 10))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((599 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_698 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_699 ⟨hr,ha.2⟩ hz
theorem cover_696_699 {a z : ℝ} (ha : a ∈ Set.Icc (149 / 500) (3 / 10))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((299 / 1000):ℝ) with hl | hr
  · exact cover_696_697 ⟨ha.1,hl⟩ hz
  · exact cover_698_699 ⟨hr,ha.2⟩ hz
theorem cover_700_701 {a z : ℝ} (ha : a ∈ Set.Icc (3 / 10) (151 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((301 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_700 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_701 ⟨hr,ha.2⟩ hz
theorem cover_702_703 {a z : ℝ} (ha : a ∈ Set.Icc (151 / 500) (38 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((303 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_702 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_703 ⟨hr,ha.2⟩ hz
theorem cover_700_703 {a z : ℝ} (ha : a ∈ Set.Icc (3 / 10) (38 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((151 / 500):ℝ) with hl | hr
  · exact cover_700_701 ⟨ha.1,hl⟩ hz
  · exact cover_702_703 ⟨hr,ha.2⟩ hz
theorem cover_696_703 {a z : ℝ} (ha : a ∈ Set.Icc (149 / 500) (38 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((3 / 10):ℝ) with hl | hr
  · exact cover_696_699 ⟨ha.1,hl⟩ hz
  · exact cover_700_703 ⟨hr,ha.2⟩ hz
theorem cover_688_703 {a z : ℝ} (ha : a ∈ Set.Icc (147 / 500) (38 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((149 / 500):ℝ) with hl | hr
  · exact cover_688_695 ⟨ha.1,hl⟩ hz
  · exact cover_696_703 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


