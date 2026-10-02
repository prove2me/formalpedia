-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage067__4_q01_q00_q03
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage067__4_q01_q00_q03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:37:45.88599+00:00
-- url     : https://prove2.me/theorems/c9d90a7d-076b-4ac4-a70a-f2ace99e828e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070) (piece 2 of 4) (piece 1 of 3) (piece 4 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070) (piece 2 of 4) (piece 1 of 3) (piece 4 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage067 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage068, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage069, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage070) (piece 2 of 4) (piece 1 of 3) (piece 4 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage067 (+3 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage068, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage069, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage070) (piece 2 of 4) (piece 1 of 3) (piece 4 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage067__4_q01_q00_q02

namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1092_1093 {a z : ℝ} (ha : a ∈ Set.Icc (619 / 625) (2477 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4953 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1092 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1093 ⟨hr,ha.2⟩ hz
end GeneralCK.Certificates.LowRatioFamily


