-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28_q18
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28_q18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T18:26:11.31313+00:00
-- url     : https://prove2.me/theorems/2950be88-79c4-4a30-9efe-aecce76dbe1a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage002, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage003, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage004, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage006, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage008, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage009, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage011, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage012, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage013, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage014, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage015, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage016, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage017, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage019, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage020, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage021, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage022, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage023, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage024, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage025, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage026, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027) (piece 19 of 28)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage002, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage003, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage004, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage006, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage008, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage009, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage011, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage012, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage013, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage014, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage015, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage016, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage017, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage019, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage020, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage021, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage022, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage023, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage024, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage025, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage026, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027) (piece 19 of 28)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage002, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage003, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage004, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage006, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage008, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage009, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage011, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage012, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage013, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage014, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage015, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage016, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage017, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage019, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage020, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage021, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage022, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage023, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage024, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage025, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage026, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027) (piece 19 of 28) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage000 (+27 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage001, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage002, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage003, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage004, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage005, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage006, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage007, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage008, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage009, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage010, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage011, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage012, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage013, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage014, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage015, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage016, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage017, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage018, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage019, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage020, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage021, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage022, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage023, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage024, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage025, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage026, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage027) (piece 19 of 28).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28_q17
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0288__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0293__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0298__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_288_289 {a z : ℝ} (ha : a ∈ Set.Icc (447 / 2500) (179 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1789 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_288 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_289 ⟨hr,ha.2⟩ hz
theorem cover_290_291 {a z : ℝ} (ha : a ∈ Set.Icc (179 / 1000) (112 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1791 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_290 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_291 ⟨hr,ha.2⟩ hz
theorem cover_288_291 {a z : ℝ} (ha : a ∈ Set.Icc (447 / 2500) (112 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((179 / 1000):ℝ) with hl | hr
  · exact cover_288_289 ⟨ha.1,hl⟩ hz
  · exact cover_290_291 ⟨hr,ha.2⟩ hz
theorem cover_292_293 {a z : ℝ} (ha : a ∈ Set.Icc (112 / 625) (897 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1793 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_292 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_293 ⟨hr,ha.2⟩ hz
theorem cover_294_295 {a z : ℝ} (ha : a ∈ Set.Icc (897 / 5000) (449 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((359 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_294 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_295 ⟨hr,ha.2⟩ hz
theorem cover_292_295 {a z : ℝ} (ha : a ∈ Set.Icc (112 / 625) (449 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((897 / 5000):ℝ) with hl | hr
  · exact cover_292_293 ⟨ha.1,hl⟩ hz
  · exact cover_294_295 ⟨hr,ha.2⟩ hz
theorem cover_288_295 {a z : ℝ} (ha : a ∈ Set.Icc (447 / 2500) (449 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((112 / 625):ℝ) with hl | hr
  · exact cover_288_291 ⟨ha.1,hl⟩ hz
  · exact cover_292_295 ⟨hr,ha.2⟩ hz
theorem cover_296_297 {a z : ℝ} (ha : a ∈ Set.Icc (449 / 2500) (899 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1797 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_296 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_297 ⟨hr,ha.2⟩ hz
theorem cover_298_299 {a z : ℝ} (ha : a ∈ Set.Icc (899 / 5000) (9 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1799 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_298 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_299 ⟨hr,ha.2⟩ hz
theorem cover_296_299 {a z : ℝ} (ha : a ∈ Set.Icc (449 / 2500) (9 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((899 / 5000):ℝ) with hl | hr
  · exact cover_296_297 ⟨ha.1,hl⟩ hz
  · exact cover_298_299 ⟨hr,ha.2⟩ hz
theorem cover_300_301 {a z : ℝ} (ha : a ∈ Set.Icc (9 / 50) (901 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1801 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_300 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_301 ⟨hr,ha.2⟩ hz
theorem cover_302_303 {a z : ℝ} (ha : a ∈ Set.Icc (901 / 5000) (451 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1803 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_302 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_303 ⟨hr,ha.2⟩ hz
theorem cover_300_303 {a z : ℝ} (ha : a ∈ Set.Icc (9 / 50) (451 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((901 / 5000):ℝ) with hl | hr
  · exact cover_300_301 ⟨ha.1,hl⟩ hz
  · exact cover_302_303 ⟨hr,ha.2⟩ hz
theorem cover_296_303 {a z : ℝ} (ha : a ∈ Set.Icc (449 / 2500) (451 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((9 / 50):ℝ) with hl | hr
  · exact cover_296_299 ⟨ha.1,hl⟩ hz
  · exact cover_300_303 ⟨hr,ha.2⟩ hz
theorem cover_288_303 {a z : ℝ} (ha : a ∈ Set.Icc (447 / 2500) (451 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((449 / 2500):ℝ) with hl | hr
  · exact cover_288_295 ⟨ha.1,hl⟩ hz
  · exact cover_296_303 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


