-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0123__7
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0123__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T10:54:07.218508+00:00
-- url     : https://prove2.me/theorems/67902368-cfbb-469c-b8d3-3265d796712a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0123 (+6 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0124, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0123 (+6 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0124, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0125, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0126, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0127, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0128, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0129)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0123 (+6 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0124, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0125, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0126, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0127, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0128, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0129)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0123 (+6 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0124, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0125, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0126, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0127, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0128, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0129) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Cell0123 (+6 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Cell0124, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0125, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0126, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0127, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0128, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0129).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0123__7_q101

namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open GeneralCK.Reflection
/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_129 {a z : ℝ}
    (ha : a ∈ Set.Icc ((1629 / 10000):ℝ) ((163 / 1000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_129 ha ⟨hz.1.le,hz.2⟩ hs) (M := (403832168174929214162308599 / 1184539201319610125000000000))
  exact lt_of_lt_of_le (by norm_num : (403832168174929214162308599 / 1184539201319610125000000000) < 2*((1629 / 10000):ℝ)/(1-((1629 / 10000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily


