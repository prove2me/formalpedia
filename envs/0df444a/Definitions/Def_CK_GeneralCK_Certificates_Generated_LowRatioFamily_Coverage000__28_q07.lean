-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28_q07
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28_q07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:54:45.633828+00:00
-- url     : https://prove2.me/theorems/c115b8a8-70ed-41c0-abb2-62cb50b652dc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage002, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage003, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage004, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage006, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage008, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage009, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage011, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage012, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage013, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage014, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage015, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage016, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage017, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage019, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage020, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage021, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage022, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage023, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage024, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage025, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage026, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027) (piece 8 of 28)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage002, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage003, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage004, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage006, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage008, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage009, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage011, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage012, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage013, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage014, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage015, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage016, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage017, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage019, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage020, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage021, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage022, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage023, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage024, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage025, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage026, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027) (piece 8 of 28)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage002, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage003, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage004, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage006, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage008, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage009, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage011, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage012, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage013, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage014, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage015, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage016, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage017, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage019, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage020, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage021, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage022, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage023, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage024, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage025, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage026, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027) (piece 8 of 28) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage000 (+27 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage001, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage002, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage003, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage004, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage005, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage006, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage007, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage008, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage009, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage010, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage011, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage012, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage013, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage014, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage015, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage016, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage017, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage018, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage019, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage020, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage021, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage022, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage023, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage024, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage025, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage026, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage027) (piece 8 of 28).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28_q06
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0111__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0117__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0123__7

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_112_113 {a z : ℝ} (ha : a ∈ Set.Icc (403 / 2500) (807 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1613 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_112 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_113 ⟨hr,ha.2⟩ hz
theorem cover_114_115 {a z : ℝ} (ha : a ∈ Set.Icc (807 / 5000) (101 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((323 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_114 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_115 ⟨hr,ha.2⟩ hz
theorem cover_112_115 {a z : ℝ} (ha : a ∈ Set.Icc (403 / 2500) (101 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((807 / 5000):ℝ) with hl | hr
  · exact cover_112_113 ⟨ha.1,hl⟩ hz
  · exact cover_114_115 ⟨hr,ha.2⟩ hz
theorem cover_116_117 {a z : ℝ} (ha : a ∈ Set.Icc (101 / 625) (809 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1617 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_116 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_117 ⟨hr,ha.2⟩ hz
theorem cover_118_119 {a z : ℝ} (ha : a ∈ Set.Icc (809 / 5000) (81 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1619 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_118 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_119 ⟨hr,ha.2⟩ hz
theorem cover_116_119 {a z : ℝ} (ha : a ∈ Set.Icc (101 / 625) (81 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((809 / 5000):ℝ) with hl | hr
  · exact cover_116_117 ⟨ha.1,hl⟩ hz
  · exact cover_118_119 ⟨hr,ha.2⟩ hz
theorem cover_112_119 {a z : ℝ} (ha : a ∈ Set.Icc (403 / 2500) (81 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((101 / 625):ℝ) with hl | hr
  · exact cover_112_115 ⟨ha.1,hl⟩ hz
  · exact cover_116_119 ⟨hr,ha.2⟩ hz
theorem cover_120_121 {a z : ℝ} (ha : a ∈ Set.Icc (81 / 500) (811 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1621 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_120 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_121 ⟨hr,ha.2⟩ hz
theorem cover_122_123 {a z : ℝ} (ha : a ∈ Set.Icc (811 / 5000) (203 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1623 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_122 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_123 ⟨hr,ha.2⟩ hz
theorem cover_120_123 {a z : ℝ} (ha : a ∈ Set.Icc (81 / 500) (203 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((811 / 5000):ℝ) with hl | hr
  · exact cover_120_121 ⟨ha.1,hl⟩ hz
  · exact cover_122_123 ⟨hr,ha.2⟩ hz
theorem cover_124_125 {a z : ℝ} (ha : a ∈ Set.Icc (203 / 1250) (813 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((13 / 80):ℝ) with hl | hr
  · exact curvature_leaf_124 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_125 ⟨hr,ha.2⟩ hz
theorem cover_126_127 {a z : ℝ} (ha : a ∈ Set.Icc (813 / 5000) (407 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1627 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_126 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_127 ⟨hr,ha.2⟩ hz
theorem cover_124_127 {a z : ℝ} (ha : a ∈ Set.Icc (203 / 1250) (407 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((813 / 5000):ℝ) with hl | hr
  · exact cover_124_125 ⟨ha.1,hl⟩ hz
  · exact cover_126_127 ⟨hr,ha.2⟩ hz
theorem cover_120_127 {a z : ℝ} (ha : a ∈ Set.Icc (81 / 500) (407 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((203 / 1250):ℝ) with hl | hr
  · exact cover_120_123 ⟨ha.1,hl⟩ hz
  · exact cover_124_127 ⟨hr,ha.2⟩ hz
theorem cover_112_127 {a z : ℝ} (ha : a ∈ Set.Icc (403 / 2500) (407 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((81 / 500):ℝ) with hl | hr
  · exact cover_112_119 ⟨ha.1,hl⟩ hz
  · exact cover_120_127 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


