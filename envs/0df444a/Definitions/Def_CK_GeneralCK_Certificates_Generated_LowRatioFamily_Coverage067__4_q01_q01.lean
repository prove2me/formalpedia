-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage067__4_q01_q01
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage067__4_q01_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:45:57.106955+00:00
-- url     : https://prove2.me/theorems/605d5b0b-33a7-4919-8386-ffb413662127
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070) (piece 2 of 4) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070) (piece 2 of 4) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070) (piece 2 of 4) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage067 (+3 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage068, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage069, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage070) (piece 2 of 4) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage067__4_q01_q00

namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1092_1095 {a z : ℝ} (ha : a ∈ Set.Icc (619 / 625) (1239 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2477 / 2500):ℝ) with hl | hr
  · exact cover_1092_1093 ⟨ha.1,hl⟩ hz
  · exact cover_1094_1095 ⟨hr,ha.2⟩ hz
theorem cover_1088_1095 {a z : ℝ} (ha : a ∈ Set.Icc (247 / 250) (1239 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((619 / 625):ℝ) with hl | hr
  · exact cover_1088_1091 ⟨ha.1,hl⟩ hz
  · exact cover_1092_1095 ⟨hr,ha.2⟩ hz
theorem cover_1096_1097 {a z : ℝ} (ha : a ∈ Set.Icc (1239 / 1250) (2479 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4957 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1096 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1097 ⟨hr,ha.2⟩ hz
theorem cover_1098_1099 {a z : ℝ} (ha : a ∈ Set.Icc (2479 / 2500) (124 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4959 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1098 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1099 ⟨hr,ha.2⟩ hz
theorem cover_1096_1099 {a z : ℝ} (ha : a ∈ Set.Icc (1239 / 1250) (124 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2479 / 2500):ℝ) with hl | hr
  · exact cover_1096_1097 ⟨ha.1,hl⟩ hz
  · exact cover_1098_1099 ⟨hr,ha.2⟩ hz
end GeneralCK.Certificates.LowRatioFamily


