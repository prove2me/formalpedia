-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q00_q01
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:33:14.205486+00:00
-- url     : https://prove2.me/theorems/c9914230-bca3-4e11-89b5-65036ece8ab0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 1 of 18) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 1 of 18) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage028 (+17 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage029, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage030, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage031, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage032, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage033, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage034, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage035, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage036, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage037, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage038, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage039, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage040, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage041, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage042, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage043, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage044, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage045) (piece 1 of 18) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage028 (+17 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage029, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage030, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage031, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage032, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage033, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage034, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage035, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage036, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage037, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage038, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage039, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage040, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage041, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage042, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage043, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage044, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage045) (piece 1 of 18) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage028__18_q00_q00
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0444__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0450__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0456__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0461__6

namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_452_455 {a z : ℝ} (ha : a ∈ Set.Icc (122 / 625) (489 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((977 / 5000):ℝ) with hl | hr
  · exact cover_452_453 ⟨ha.1,hl⟩ hz
  · exact cover_454_455 ⟨hr,ha.2⟩ hz
theorem cover_448_455 {a z : ℝ} (ha : a ∈ Set.Icc (487 / 2500) (489 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((122 / 625):ℝ) with hl | hr
  · exact cover_448_451 ⟨ha.1,hl⟩ hz
  · exact cover_452_455 ⟨hr,ha.2⟩ hz
theorem cover_456_457 {a z : ℝ} (ha : a ∈ Set.Icc (489 / 2500) (979 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1957 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_456 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_457 ⟨hr,ha.2⟩ hz
theorem cover_458_459 {a z : ℝ} (ha : a ∈ Set.Icc (979 / 5000) (49 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1959 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_458 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_459 ⟨hr,ha.2⟩ hz
theorem cover_456_459 {a z : ℝ} (ha : a ∈ Set.Icc (489 / 2500) (49 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((979 / 5000):ℝ) with hl | hr
  · exact cover_456_457 ⟨ha.1,hl⟩ hz
  · exact cover_458_459 ⟨hr,ha.2⟩ hz
end GeneralCK.Certificates.LowRatioFamily


