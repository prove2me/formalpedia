-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28_q10
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28_q10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T14:25:40.956981+00:00
-- url     : https://prove2.me/theorems/9696afd0-df39-48a5-af9c-766f41d907e9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage002, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage003, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage004, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage006, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage008, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage009, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage011, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage012, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage013, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage014, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage015, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage016, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage017, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage019, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage020, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage021, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage022, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage023, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage024, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage025, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage026, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027) (piece 11 of 28)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage002, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage003, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage004, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage006, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage008, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage009, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage011, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage012, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage013, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage014, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage015, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage016, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage017, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage019, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage020, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage021, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage022, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage023, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage024, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage025, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage026, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027) (piece 11 of 28)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage000 (+27 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Coverage001, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage002, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage003, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage004, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage005, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage006, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage007, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage008, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage009, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage011, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage012, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage013, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage014, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage015, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage016, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage017, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage018, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage019, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage020, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage021, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage022, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage023, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage024, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage025, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage026, GeneralCK.Certificates.Generated.LowRatioFamily.Coverage027) (piece 11 of 28) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Coverage000 (+27 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Coverage001, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage002, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage003, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage004, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage005, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage006, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage007, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage008, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage009, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage010, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage011, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage012, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage013, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage014, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage015, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage016, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage017, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage018, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage019, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage020, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage021, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage022, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage023, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage024, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage025, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage026, GeneralCK/Certificates/Generated/LowRatioFamily/Coverage027) (piece 11 of 28).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Coverage000__28_q09
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0155__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0161__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0168__7
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0175__6

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Coverage010 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_160_161 {a z : ℝ} (ha : a ∈ Set.Icc (83 / 500) (831 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1661 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_160 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_161 ⟨hr,ha.2⟩ hz
theorem cover_162_163 {a z : ℝ} (ha : a ∈ Set.Icc (831 / 5000) (104 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1663 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_162 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_163 ⟨hr,ha.2⟩ hz
theorem cover_160_163 {a z : ℝ} (ha : a ∈ Set.Icc (83 / 500) (104 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((831 / 5000):ℝ) with hl | hr
  · exact cover_160_161 ⟨ha.1,hl⟩ hz
  · exact cover_162_163 ⟨hr,ha.2⟩ hz
theorem cover_164_165 {a z : ℝ} (ha : a ∈ Set.Icc (104 / 625) (833 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((333 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_164 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_165 ⟨hr,ha.2⟩ hz
theorem cover_166_167 {a z : ℝ} (ha : a ∈ Set.Icc (833 / 5000) (417 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1667 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_166 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_167 ⟨hr,ha.2⟩ hz
theorem cover_164_167 {a z : ℝ} (ha : a ∈ Set.Icc (104 / 625) (417 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((833 / 5000):ℝ) with hl | hr
  · exact cover_164_165 ⟨ha.1,hl⟩ hz
  · exact cover_166_167 ⟨hr,ha.2⟩ hz
theorem cover_160_167 {a z : ℝ} (ha : a ∈ Set.Icc (83 / 500) (417 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((104 / 625):ℝ) with hl | hr
  · exact cover_160_163 ⟨ha.1,hl⟩ hz
  · exact cover_164_167 ⟨hr,ha.2⟩ hz
theorem cover_168_169 {a z : ℝ} (ha : a ∈ Set.Icc (417 / 2500) (167 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1669 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_168 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_169 ⟨hr,ha.2⟩ hz
theorem cover_170_171 {a z : ℝ} (ha : a ∈ Set.Icc (167 / 1000) (209 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1671 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_170 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_171 ⟨hr,ha.2⟩ hz
theorem cover_168_171 {a z : ℝ} (ha : a ∈ Set.Icc (417 / 2500) (209 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((167 / 1000):ℝ) with hl | hr
  · exact cover_168_169 ⟨ha.1,hl⟩ hz
  · exact cover_170_171 ⟨hr,ha.2⟩ hz
theorem cover_172_173 {a z : ℝ} (ha : a ∈ Set.Icc (209 / 1250) (837 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1673 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_172 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_173 ⟨hr,ha.2⟩ hz
theorem cover_174_175 {a z : ℝ} (ha : a ∈ Set.Icc (837 / 5000) (419 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((67 / 400):ℝ) with hl | hr
  · exact curvature_leaf_174 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_175 ⟨hr,ha.2⟩ hz
theorem cover_172_175 {a z : ℝ} (ha : a ∈ Set.Icc (209 / 1250) (419 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((837 / 5000):ℝ) with hl | hr
  · exact cover_172_173 ⟨ha.1,hl⟩ hz
  · exact cover_174_175 ⟨hr,ha.2⟩ hz
theorem cover_168_175 {a z : ℝ} (ha : a ∈ Set.Icc (417 / 2500) (419 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((209 / 1250):ℝ) with hl | hr
  · exact cover_168_171 ⟨ha.1,hl⟩ hz
  · exact cover_172_175 ⟨hr,ha.2⟩ hz
theorem cover_160_175 {a z : ℝ} (ha : a ∈ Set.Icc (83 / 500) (419 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((417 / 2500):ℝ) with hl | hr
  · exact cover_160_167 ⟨ha.1,hl⟩ hz
  · exact cover_168_175 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

end


