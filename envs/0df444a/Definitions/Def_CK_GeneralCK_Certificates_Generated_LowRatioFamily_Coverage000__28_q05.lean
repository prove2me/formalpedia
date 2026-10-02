-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28_q05
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28_q05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:38:25.658922+00:00
-- url     : https://prove2.me/theorems/21a3a615-a5a3-42a6-9b5b-644fc5cecb66
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage002, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage003, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage004, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage006, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage008, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage009, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage011, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage012, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage013, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage014, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage015, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage016, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage017, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage019, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage020, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage021, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage022, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage023, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage024, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage025, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage026, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027) (piece 6 of 28)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage002, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage003, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage004, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage006, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage008, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage009, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage011, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage012, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage013, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage014, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage015, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage016, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage017, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage019, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage020, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage021, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage022, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage023, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage024, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage025, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage026, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027) (piece 6 of 28)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage002, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage003, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage004, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage006, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage008, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage009, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage011, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage012, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage013, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage014, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage015, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage016, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage017, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage019, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage020, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage021, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage022, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage023, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage024, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage025, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage026, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027) (piece 6 of 28) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage000 (+27 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage001, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage002, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage003, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage004, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage005, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage006, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage007, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage008, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage009, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage010, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage011, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage012, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage013, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage014, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage015, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage016, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage017, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage018, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage019, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage020, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage021, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage022, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage023, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage024, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage025, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage026, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage027) (piece 6 of 28).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28_q04
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0075__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0081__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0087__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0093__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_80_81 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 500) (791 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1581 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_80 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_81 ⟨hr,ha.2⟩ hz
theorem cover_82_83 {a z : ℝ} (ha : a ∈ Set.Icc (791 / 5000) (99 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1583 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_82 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_83 ⟨hr,ha.2⟩ hz
theorem cover_80_83 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 500) (99 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((791 / 5000):ℝ) with hl | hr
  · exact cover_80_81 ⟨ha.1,hl⟩ hz
  · exact cover_82_83 ⟨hr,ha.2⟩ hz
theorem cover_84_85 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 625) (793 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((317 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_84 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_85 ⟨hr,ha.2⟩ hz
theorem cover_86_87 {a z : ℝ} (ha : a ∈ Set.Icc (793 / 5000) (397 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1587 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_86 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_87 ⟨hr,ha.2⟩ hz
theorem cover_84_87 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 625) (397 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((793 / 5000):ℝ) with hl | hr
  · exact cover_84_85 ⟨ha.1,hl⟩ hz
  · exact cover_86_87 ⟨hr,ha.2⟩ hz
theorem cover_80_87 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 500) (397 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((99 / 625):ℝ) with hl | hr
  · exact cover_80_83 ⟨ha.1,hl⟩ hz
  · exact cover_84_87 ⟨hr,ha.2⟩ hz
theorem cover_88_89 {a z : ℝ} (ha : a ∈ Set.Icc (397 / 2500) (159 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1589 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_88 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_89 ⟨hr,ha.2⟩ hz
theorem cover_90_91 {a z : ℝ} (ha : a ∈ Set.Icc (159 / 1000) (199 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1591 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_90 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_91 ⟨hr,ha.2⟩ hz
theorem cover_88_91 {a z : ℝ} (ha : a ∈ Set.Icc (397 / 2500) (199 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((159 / 1000):ℝ) with hl | hr
  · exact cover_88_89 ⟨ha.1,hl⟩ hz
  · exact cover_90_91 ⟨hr,ha.2⟩ hz
theorem cover_92_93 {a z : ℝ} (ha : a ∈ Set.Icc (199 / 1250) (797 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1593 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_92 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_93 ⟨hr,ha.2⟩ hz
theorem cover_94_95 {a z : ℝ} (ha : a ∈ Set.Icc (797 / 5000) (399 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((319 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_94 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_95 ⟨hr,ha.2⟩ hz
theorem cover_92_95 {a z : ℝ} (ha : a ∈ Set.Icc (199 / 1250) (399 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((797 / 5000):ℝ) with hl | hr
  · exact cover_92_93 ⟨ha.1,hl⟩ hz
  · exact cover_94_95 ⟨hr,ha.2⟩ hz
theorem cover_88_95 {a z : ℝ} (ha : a ∈ Set.Icc (397 / 2500) (399 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((199 / 1250):ℝ) with hl | hr
  · exact cover_88_91 ⟨ha.1,hl⟩ hz
  · exact cover_92_95 ⟨hr,ha.2⟩ hz
theorem cover_80_95 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 500) (399 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((397 / 2500):ℝ) with hl | hr
  · exact cover_80_87 ⟨ha.1,hl⟩ hz
  · exact cover_88_95 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


