-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0043GraphWholeA__20
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0043GraphWholeA__20
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T06:39:50.403271+00:00
-- url     : https://prove2.me/theorems/85256b66-dbce-40da-8664-e64fea6ac1df
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0043GraphWholeA (+19 modules: GeneralCK.Certificates.E8TAxisZero0044GraphWholeA, GeneralCK.Certificates.E8TAxisZero0045Graph…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0043GraphWholeA (+19 modules: GeneralCK.Certificates.E8TAxisZero0044GraphWholeA, GeneralCK.Certificates.E8TAxisZero0045GraphWholeA, GeneralCK.Certificates.E8TAxisZero0046GraphWholeA, GeneralCK.Certificates.E8TAxisZero0047GraphWholeA, GeneralCK.Certificates.E8TAxisZero0048GraphWholeA, GeneralCK.Certificates.E8TAxisZero0049GraphWholeA, GeneralCK.Certificates.E8TAxisZero0050GraphWholeA, GeneralCK.Certificates.E8TAxisZero0051GraphWholeA, GeneralCK.Certificates.E8TAxisZero0052GraphWholeA, GeneralCK.Certificates.E8TAxisZero0053GraphWholeA, GeneralCK.Certificates.E8TAxisZero0054GraphWholeA, GeneralCK.Certificates.E8TAxisZero0055GraphWholeA, GeneralCK.Certificates.E8TAxisZero0056GraphWholeA, GeneralCK.Certificates.E8TAxisZero0057GraphWholeA, GeneralCK.Certificates.E8TAxisZero0058GraphWholeA, GeneralCK.Certificates.E8TAxisZero0059GraphWholeA, GeneralCK.Certificates.E8TAxisZero0060GraphWholeA, GeneralCK.Certificates.E8TAxisZero0061GraphWholeA, GeneralCK.Certificates.E8TAxisZero0062GraphWholeA)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0043GraphWholeA (+19 modules: GeneralCK.Certificates.E8TAxisZero0044GraphWholeA, GeneralCK.Certificates.E8TAxisZero0045GraphWholeA, GeneralCK.Certificates.E8TAxisZero0046GraphWholeA, GeneralCK.Certificates.E8TAxisZero0047GraphWholeA, GeneralCK.Certificates.E8TAxisZero0048GraphWholeA, GeneralCK.Certificates.E8TAxisZero0049GraphWholeA, GeneralCK.Certificates.E8TAxisZero0050GraphWholeA, GeneralCK.Certificates.E8TAxisZero0051GraphWholeA, GeneralCK.Certificates.E8TAxisZero0052GraphWholeA, GeneralCK.Certificates.E8TAxisZero0053GraphWholeA, GeneralCK.Certificates.E8TAxisZero0054GraphWholeA, GeneralCK.Certificates.E8TAxisZero0055GraphWholeA, GeneralCK.Certificates.E8TAxisZero0056GraphWholeA, GeneralCK.Certificates.E8TAxisZero0057GraphWholeA, GeneralCK.Certificates.E8TAxisZero0058GraphWholeA, GeneralCK.Certificates.E8TAxisZero0059GraphWholeA, GeneralCK.Certificates.E8TAxisZero0060GraphWholeA, GeneralCK.Certificates.E8TAxisZero0061GraphWholeA, GeneralCK.Certificates.E8TAxisZero0062GraphWholeA)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0043GraphWholeA (+19 modules: GeneralCK.Certificates.E8TAxisZero0044GraphWholeA, GeneralCK.Certificates.E8TAxisZero0045GraphWholeA, GeneralCK.Certificates.E8TAxisZero0046GraphWholeA, GeneralCK.Certificates.E8TAxisZero0047GraphWholeA, GeneralCK.Certificates.E8TAxisZero0048GraphWholeA, GeneralCK.Certificates.E8TAxisZero0049GraphWholeA, GeneralCK.Certificates.E8TAxisZero0050GraphWholeA, GeneralCK.Certificates.E8TAxisZero0051GraphWholeA, GeneralCK.Certificates.E8TAxisZero0052GraphWholeA, GeneralCK.Certificates.E8TAxisZero0053GraphWholeA, GeneralCK.Certificates.E8TAxisZero0054GraphWholeA, GeneralCK.Certificates.E8TAxisZero0055GraphWholeA, GeneralCK.Certificates.E8TAxisZero0056GraphWholeA, GeneralCK.Certificates.E8TAxisZero0057GraphWholeA, GeneralCK.Certificates.E8TAxisZero0058GraphWholeA, GeneralCK.Certificates.E8TAxisZero0059GraphWholeA, GeneralCK.Certificates.E8TAxisZero0060GraphWholeA, GeneralCK.Certificates.E8TAxisZero0061GraphWholeA, GeneralCK.Certificates.E8TAxisZero0062GraphWholeA) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0043GraphWholeA (+19 modules: GeneralCK/Certificates/E8TAxisZero0044GraphWholeA, GeneralCK/Certificates/E8TAxisZero0045GraphWholeA, GeneralCK/Certificates/E8TAxisZero0046GraphWholeA, GeneralCK/Certificates/E8TAxisZero0047GraphWholeA, GeneralCK/Certificates/E8TAxisZero0048GraphWholeA, GeneralCK/Certificates/E8TAxisZero0049GraphWholeA, GeneralCK/Certificates/E8TAxisZero0050GraphWholeA, GeneralCK/Certificates/E8TAxisZero0051GraphWholeA, GeneralCK/Certificates/E8TAxisZero0052GraphWholeA, GeneralCK/Certificates/E8TAxisZero0053GraphWholeA, GeneralCK/Certificates/E8TAxisZero0054GraphWholeA, GeneralCK/Certificates/E8TAxisZero0055GraphWholeA, GeneralCK/Certificates/E8TAxisZero0056GraphWholeA, GeneralCK/Certificates/E8TAxisZero0057GraphWholeA, GeneralCK/Certificates/E8TAxisZero0058GraphWholeA, GeneralCK/Certificates/E8TAxisZero0059GraphWholeA, GeneralCK/Certificates/E8TAxisZero0060GraphWholeA, GeneralCK/Certificates/E8TAxisZero0061GraphWholeA, GeneralCK/Certificates/E8TAxisZero0062GraphWholeA).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularUnconditionalSource

-- ===== source module GeneralCK.Certificates.E8TAxisZero0043GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0043GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-5374820139, 316573714637776686286688825891685108255886818⟩,
   ⟨126629467412457383891962325730849795299091128369, 126629522740422691195352252146003446050018542664⟩,
   ⟨-94597021146140255, 44262383116714132504672510273171611184785934⟩,
   ⟨17704944549989160507950634607783361465279542548, 17704970640082501731328311906250987545614215982⟩,
   ⟨-1089764495002802204107256, 20872082400462391840700785241964134973049154⟩,
   ⟨8348826778198316166050346011808885812228005088, 8348845324160105023411291559644293916509901301⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0043GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0044GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0044GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-5374820139, 316573714637776686286688825891685108255886818⟩,
   ⟨126629467412457383891962325730849795299091128369, 126629522740422691195352252146003446050018542664⟩,
   ⟨-94597021146140255, 44262383116714132504672510273171611184785934⟩,
   ⟨17704944549989160507950634607783361465279542548, 17704970640082501731328311906250987545614215982⟩,
   ⟨-1089764495002802204107256, 20872082400462391840700785241964134973049154⟩,
   ⟨8348826778198316166050346011808885812228005088, 8348845324160105023411291559644293916509901301⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0044GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0045GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0045GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-5374820139, 316573714637776686286688825891685108255886818⟩,
   ⟨126629467412457383891962325730849795299091128369, 126629522740422691195352252146003446050018542664⟩,
   ⟨-94597021146140255, 44262383116714132504672510273171611184785934⟩,
   ⟨17704944549989160507950634607783361465279542548, 17704970640082501731328311906250987545614215982⟩,
   ⟨-1089764495002802204107256, 20872082400462391840700785241964134973049154⟩,
   ⟨8348826778198316166050346011808885812228005088, 8348845324160105023411291559644293916509901301⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0045GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0046GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0046GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-5374820139, 316573714637776686286688825891685108255886818⟩,
   ⟨126629467412457383891962325730849795299091128369, 126629522740422691195352252146003446050018542664⟩,
   ⟨-94597021146140255, 44262383116714132504672510273171611184785934⟩,
   ⟨17704944549989160507950634607783361465279542548, 17704970640082501731328311906250987545614215982⟩,
   ⟨-1089764495002802204107256, 20872082400462391840700785241964134973049154⟩,
   ⟨8348826778198316166050346011808885812228005088, 8348845324160105023411291559644293916509901301⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0046GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0047GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0047GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-5374820139, 316573714637776686286688825891685108255886818⟩,
   ⟨126629467412457383891962325730849795299091128369, 126629522740422691195352252146003446050018542664⟩,
   ⟨-94597021146140255, 44262383116714132504672510273171611184785934⟩,
   ⟨17704944549989160507950634607783361465279542548, 17704970640082501731328311906250987545614215982⟩,
   ⟨-1089764495002802204107256, 20872082400462391840700785241964134973049154⟩,
   ⟨8348826778198316166050346011808885812228005088, 8348845324160105023411291559644293916509901301⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0047GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0048GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0048GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-5374820139, 316573714637776686286688825891685108255886818⟩,
   ⟨126629467412457383891962325730849795299091128369, 126629522740422691195352252146003446050018542664⟩,
   ⟨-94597021146140255, 44262383116714132504672510273171611184785934⟩,
   ⟨17704944549989160507950634607783361465279542548, 17704970640082501731328311906250987545614215982⟩,
   ⟨-1089764495002802204107256, 20872082400462391840700785241964134973049154⟩,
   ⟨8348826778198316166050346011808885812228005088, 8348845324160105023411291559644293916509901301⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0048GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0049GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0049GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-5374820139, 316573714637776686286688825891685108255886818⟩,
   ⟨126629467412457383891962325730849795299091128369, 126629522740422691195352252146003446050018542664⟩,
   ⟨-94597021146140255, 44262383116714132504672510273171611184785934⟩,
   ⟨17704944549989160507950634607783361465279542548, 17704970640082501731328311906250987545614215982⟩,
   ⟨-1089764495002802204107256, 20872082400462391840700785241964134973049154⟩,
   ⟨8348826778198316166050346011808885812228005088, 8348845324160105023411291559644293916509901301⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0049GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0050GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0050GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-5374820139, 316573714637776686286688825891685108255886818⟩,
   ⟨126629467412457383891962325730849795299091128369, 126629522740422691195352252146003446050018542664⟩,
   ⟨-94597021146140255, 44262383116714132504672510273171611184785934⟩,
   ⟨17704944549989160507950634607783361465279542548, 17704970640082501731328311906250987545614215982⟩,
   ⟨-1089764495002802204107256, 20872082400462391840700785241964134973049154⟩,
   ⟨8348826778198316166050346011808885812228005088, 8348845324160105023411291559644293916509901301⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0050GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0051GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0051GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-2624431, 158286840028900246219532921336190878770374352⟩,
   ⟨126629467412457383891962325730849818925222214174, 126629481244446162857603601636872238811738981552⟩,
   ⟨-184759191294496, 22131183405203651757090809608120314174451228⟩,
   ⟨17704944549989160507950634947003115071758515451, 17704951072510684684942035306722147605733633873⟩,
   ⟨-8513704634469968292700, 10436035404618501581654779580618386742011623⟩,
   ⟨8348826778198316169054034525298269567467058818, 8348831414687888154816406649917552886681883003⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0051GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0052GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0052GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-2624431, 158286840028900246219532921336190878770374352⟩,
   ⟨126629467412457383891962325730849818925222214174, 126629481244446162857603601636872238811738981552⟩,
   ⟨-184759191294496, 22131183405203651757090809608120314174451228⟩,
   ⟨17704944549989160507950634947003115071758515451, 17704951072510684684942035306722147605733633873⟩,
   ⟨-8513704634469968292700, 10436035404618501581654779580618386742011623⟩,
   ⟨8348826778198316169054034525298269567467058818, 8348831414687888154816406649917552886681883003⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0052GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0053GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0053GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-2624431, 158286840028900246219532921336190878770374352⟩,
   ⟨126629467412457383891962325730849818925222214174, 126629481244446162857603601636872238811738981552⟩,
   ⟨-184759191294496, 22131183405203651757090809608120314174451228⟩,
   ⟨17704944549989160507950634947003115071758515451, 17704951072510684684942035306722147605733633873⟩,
   ⟨-8513704634469968292700, 10436035404618501581654779580618386742011623⟩,
   ⟨8348826778198316169054034525298269567467058818, 8348831414687888154816406649917552886681883003⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0053GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0054GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0054GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-2624431, 158286840028900246219532921336190878770374352⟩,
   ⟨126629467412457383891962325730849818925222214174, 126629481244446162857603601636872238811738981552⟩,
   ⟨-184759191294496, 22131183405203651757090809608120314174451228⟩,
   ⟨17704944549989160507950634947003115071758515451, 17704951072510684684942035306722147605733633873⟩,
   ⟨-8513704634469968292700, 10436035404618501581654779580618386742011623⟩,
   ⟨8348826778198316169054034525298269567467058818, 8348831414687888154816406649917552886681883003⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0054GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0055GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0055GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-2624431, 158286840028900246219532921336190878770374352⟩,
   ⟨126629467412457383891962325730849818925222214174, 126629481244446162857603601636872238811738981552⟩,
   ⟨-184759191294496, 22131183405203651757090809608120314174451228⟩,
   ⟨17704944549989160507950634947003115071758515451, 17704951072510684684942035306722147605733633873⟩,
   ⟨-8513704634469968292700, 10436035404618501581654779580618386742011623⟩,
   ⟨8348826778198316169054034525298269567467058818, 8348831414687888154816406649917552886681883003⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0055GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0056GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0056GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-2624431, 158286840028900246219532921336190878770374352⟩,
   ⟨126629467412457383891962325730849818925222214174, 126629481244446162857603601636872238811738981552⟩,
   ⟨-184759191294496, 22131183405203651757090809608120314174451228⟩,
   ⟨17704944549989160507950634947003115071758515451, 17704951072510684684942035306722147605733633873⟩,
   ⟨-8513704634469968292700, 10436035404618501581654779580618386742011623⟩,
   ⟨8348826778198316169054034525298269567467058818, 8348831414687888154816406649917552886681883003⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0056GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0057GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0057GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-2624431, 158286840028900246219532921336190878770374352⟩,
   ⟨126629467412457383891962325730849818925222214174, 126629481244446162857603601636872238811738981552⟩,
   ⟨-184759191294496, 22131183405203651757090809608120314174451228⟩,
   ⟨17704944549989160507950634947003115071758515451, 17704951072510684684942035306722147605733633873⟩,
   ⟨-8513704634469968292700, 10436035404618501581654779580618386742011623⟩,
   ⟨8348826778198316169054034525298269567467058818, 8348831414687888154816406649917552886681883003⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0057GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0058GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0058GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-2624431, 158286840028900246219532921336190878770374352⟩,
   ⟨126629467412457383891962325730849818925222214174, 126629481244446162857603601636872238811738981552⟩,
   ⟨-184759191294496, 22131183405203651757090809608120314174451228⟩,
   ⟨17704944549989160507950634947003115071758515451, 17704951072510684684942035306722147605733633873⟩,
   ⟨-8513704634469968292700, 10436035404618501581654779580618386742011623⟩,
   ⟨8348826778198316169054034525298269567467058818, 8348831414687888154816406649917552886681883003⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0058GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0059GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0059GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-2624431, 158286840028900246219532921336190878770374352⟩,
   ⟨126629467412457383891962325730849818925222214174, 126629481244446162857603601636872238811738981552⟩,
   ⟨-184759191294496, 22131183405203651757090809608120314174451228⟩,
   ⟨17704944549989160507950634947003115071758515451, 17704951072510684684942035306722147605733633873⟩,
   ⟨-8513704634469968292700, 10436035404618501581654779580618386742011623⟩,
   ⟨8348826778198316169054034525298269567467058818, 8348831414687888154816406649917552886681883003⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0059GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0060GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0060GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-2624431, 158286840028900246219532921336190878770374352⟩,
   ⟨126629467412457383891962325730849818925222214174, 126629481244446162857603601636872238811738981552⟩,
   ⟨-184759191294496, 22131183405203651757090809608120314174451228⟩,
   ⟨17704944549989160507950634947003115071758515451, 17704951072510684684942035306722147605733633873⟩,
   ⟨-8513704634469968292700, 10436035404618501581654779580618386742011623⟩,
   ⟨8348826778198316169054034525298269567467058818, 8348831414687888154816406649917552886681883003⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0060GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0061GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0061GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-2624431, 158286840028900246219532921336190878770374352⟩,
   ⟨126629467412457383891962325730849818925222214174, 126629481244446162857603601636872238811738981552⟩,
   ⟨-184759191294496, 22131183405203651757090809608120314174451228⟩,
   ⟨17704944549989160507950634947003115071758515451, 17704951072510684684942035306722147605733633873⟩,
   ⟨-8513704634469968292700, 10436035404618501581654779580618386742011623⟩,
   ⟨8348826778198316169054034525298269567467058818, 8348831414687888154816406649917552886681883003⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0061GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0062GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0062GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-2624431, 158286840028900246219532921336190878770374352⟩,
   ⟨126629467412457383891962325730849818925222214174, 126629481244446162857603601636872238811738981552⟩,
   ⟨-184759191294496, 22131183405203651757090809608120314174451228⟩,
   ⟨17704944549989160507950634947003115071758515451, 17704951072510684684942035306722147605733633873⟩,
   ⟨-8513704634469968292700, 10436035404618501581654779580618386742011623⟩,
   ⟨8348826778198316169054034525298269567467058818, 8348831414687888154816406649917552886681883003⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0062GraphWholeA

end


