-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T06:28:53.714134+00:00
-- url     : https://prove2.me/theorems/80d636f3-78f1-474c-a4ba-f7fab514f55d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage002, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage003, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage004, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage006, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage008, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage009, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage011, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage012, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage013, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage014, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage015, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage016, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage017, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage019, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage020, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage021, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage022, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage023, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage024, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage025, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage026, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage002, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage003, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage004, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage006, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage008, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage009, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage011, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage012, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage013, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage014, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage015, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage016, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage017, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage019, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage020, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage021, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage022, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage023, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage024, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage025, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage026, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage002, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage003, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage004, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage006, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage008, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage009, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage011, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage012, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage013, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage014, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage015, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage016, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage017, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage019, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage020, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage021, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage022, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage023, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage024, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage025, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage026, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage000 (+27 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage001, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage002, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage003, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage004, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage005, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage006, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage007, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage008, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage009, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage010, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage011, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage012, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage013, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage014, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage015, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage016, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage017, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage018, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage019, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage020, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage021, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage022, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage023, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage024, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage025, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage026, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage027).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28_q26
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0427__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0433__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0438__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0444__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_432_433 {a z : ℝ} (ha : a ∈ Set.Icc (483 / 2500) (967 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1933 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_432 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_433 ⟨hr,ha.2⟩ hz
theorem cover_434_435 {a z : ℝ} (ha : a ∈ Set.Icc (967 / 5000) (121 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((387 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_434 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_435 ⟨hr,ha.2⟩ hz
theorem cover_432_435 {a z : ℝ} (ha : a ∈ Set.Icc (483 / 2500) (121 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((967 / 5000):ℝ) with hl | hr
  · exact cover_432_433 ⟨ha.1,hl⟩ hz
  · exact cover_434_435 ⟨hr,ha.2⟩ hz
theorem cover_436_437 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 625) (969 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1937 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_436 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_437 ⟨hr,ha.2⟩ hz
theorem cover_438_439 {a z : ℝ} (ha : a ∈ Set.Icc (969 / 5000) (97 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1939 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_438 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_439 ⟨hr,ha.2⟩ hz
theorem cover_436_439 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 625) (97 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((969 / 5000):ℝ) with hl | hr
  · exact cover_436_437 ⟨ha.1,hl⟩ hz
  · exact cover_438_439 ⟨hr,ha.2⟩ hz
theorem cover_432_439 {a z : ℝ} (ha : a ∈ Set.Icc (483 / 2500) (97 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((121 / 625):ℝ) with hl | hr
  · exact cover_432_435 ⟨ha.1,hl⟩ hz
  · exact cover_436_439 ⟨hr,ha.2⟩ hz
theorem cover_440_441 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 500) (971 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1941 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_440 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_441 ⟨hr,ha.2⟩ hz
theorem cover_442_443 {a z : ℝ} (ha : a ∈ Set.Icc (971 / 5000) (243 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1943 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_442 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_443 ⟨hr,ha.2⟩ hz
theorem cover_440_443 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 500) (243 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((971 / 5000):ℝ) with hl | hr
  · exact cover_440_441 ⟨ha.1,hl⟩ hz
  · exact cover_442_443 ⟨hr,ha.2⟩ hz
theorem cover_444_445 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 1250) (973 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((389 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_444 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_445 ⟨hr,ha.2⟩ hz
theorem cover_446_447 {a z : ℝ} (ha : a ∈ Set.Icc (973 / 5000) (487 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1947 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_446 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_447 ⟨hr,ha.2⟩ hz
theorem cover_444_447 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 1250) (487 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((973 / 5000):ℝ) with hl | hr
  · exact cover_444_445 ⟨ha.1,hl⟩ hz
  · exact cover_446_447 ⟨hr,ha.2⟩ hz
theorem cover_440_447 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 500) (487 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((243 / 1250):ℝ) with hl | hr
  · exact cover_440_443 ⟨ha.1,hl⟩ hz
  · exact cover_444_447 ⟨hr,ha.2⟩ hz
theorem cover_432_447 {a z : ℝ} (ha : a ∈ Set.Icc (483 / 2500) (487 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((97 / 500):ℝ) with hl | hr
  · exact cover_432_439 ⟨ha.1,hl⟩ hz
  · exact cover_440_447 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


