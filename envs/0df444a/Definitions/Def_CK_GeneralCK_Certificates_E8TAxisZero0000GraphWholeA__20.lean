-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphWholeA__20
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0000GraphWholeA__20
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T10:30:14.870197+00:00
-- url     : https://prove2.me/theorems/a7ddbf2b-cbac-479e-8035-2a6ac3ccec37
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0000GraphWholeA (+19 modules: GeneralCK.Certificates.E8TAxisZero0001GraphWholeA, GeneralCK.Certificates.E8TAxisZero0002Graph…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0000GraphWholeA (+19 modules: GeneralCK.Certificates.E8TAxisZero0001GraphWholeA, GeneralCK.Certificates.E8TAxisZero0002GraphWholeA, GeneralCK.Certificates.E8TAxisZero0003GraphWholeA, GeneralCK.Certificates.E8TAxisZero0004GraphWholeA, GeneralCK.Certificates.E8TAxisZero0005GraphWholeA, GeneralCK.Certificates.E8TAxisZero0006GraphWholeA, GeneralCK.Certificates.E8TAxisZero0007GraphWholeA, GeneralCK.Certificates.E8TAxisZero0008GraphWholeA, GeneralCK.Certificates.E8TAxisZero0009GraphWholeA, GeneralCK.Certificates.E8TAxisZero0010GraphWholeA, GeneralCK.Certificates.E8TAxisZero0011GraphWholeA, GeneralCK.Certificates.E8TAxisZero0012GraphWholeA, GeneralCK.Certificates.E8TAxisZero0013GraphWholeA, GeneralCK.Certificates.E8TAxisZero0015GraphWholeA, GeneralCK.Certificates.E8TAxisZero0016GraphWholeA, GeneralCK.Certificates.E8TAxisZero0017GraphWholeA, GeneralCK.Certificates.E8TAxisZero0018GraphWholeA, GeneralCK.Certificates.E8TAxisZero0019GraphWholeA, GeneralCK.Certificates.E8TAxisZero0020GraphWholeA)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0000GraphWholeA (+19 modules: GeneralCK.Certificates.E8TAxisZero0001GraphWholeA, GeneralCK.Certificates.E8TAxisZero0002GraphWholeA, GeneralCK.Certificates.E8TAxisZero0003GraphWholeA, GeneralCK.Certificates.E8TAxisZero0004GraphWholeA, GeneralCK.Certificates.E8TAxisZero0005GraphWholeA, GeneralCK.Certificates.E8TAxisZero0006GraphWholeA, GeneralCK.Certificates.E8TAxisZero0007GraphWholeA, GeneralCK.Certificates.E8TAxisZero0008GraphWholeA, GeneralCK.Certificates.E8TAxisZero0009GraphWholeA, GeneralCK.Certificates.E8TAxisZero0010GraphWholeA, GeneralCK.Certificates.E8TAxisZero0011GraphWholeA, GeneralCK.Certificates.E8TAxisZero0012GraphWholeA, GeneralCK.Certificates.E8TAxisZero0013GraphWholeA, GeneralCK.Certificates.E8TAxisZero0015GraphWholeA, GeneralCK.Certificates.E8TAxisZero0016GraphWholeA, GeneralCK.Certificates.E8TAxisZero0017GraphWholeA, GeneralCK.Certificates.E8TAxisZero0018GraphWholeA, GeneralCK.Certificates.E8TAxisZero0019GraphWholeA, GeneralCK.Certificates.E8TAxisZero0020GraphWholeA)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0000GraphWholeA (+19 modules: GeneralCK.Certificates.E8TAxisZero0001GraphWholeA, GeneralCK.Certificates.E8TAxisZero0002GraphWholeA, GeneralCK.Certificates.E8TAxisZero0003GraphWholeA, GeneralCK.Certificates.E8TAxisZero0004GraphWholeA, GeneralCK.Certificates.E8TAxisZero0005GraphWholeA, GeneralCK.Certificates.E8TAxisZero0006GraphWholeA, GeneralCK.Certificates.E8TAxisZero0007GraphWholeA, GeneralCK.Certificates.E8TAxisZero0008GraphWholeA, GeneralCK.Certificates.E8TAxisZero0009GraphWholeA, GeneralCK.Certificates.E8TAxisZero0010GraphWholeA, GeneralCK.Certificates.E8TAxisZero0011GraphWholeA, GeneralCK.Certificates.E8TAxisZero0012GraphWholeA, GeneralCK.Certificates.E8TAxisZero0013GraphWholeA, GeneralCK.Certificates.E8TAxisZero0015GraphWholeA, GeneralCK.Certificates.E8TAxisZero0016GraphWholeA, GeneralCK.Certificates.E8TAxisZero0017GraphWholeA, GeneralCK.Certificates.E8TAxisZero0018GraphWholeA, GeneralCK.Certificates.E8TAxisZero0019GraphWholeA, GeneralCK.Certificates.E8TAxisZero0020GraphWholeA) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0000GraphWholeA (+19 modules: GeneralCK/Certificates/E8TAxisZero0001GraphWholeA, GeneralCK/Certificates/E8TAxisZero0002GraphWholeA, GeneralCK/Certificates/E8TAxisZero0003GraphWholeA, GeneralCK/Certificates/E8TAxisZero0004GraphWholeA, GeneralCK/Certificates/E8TAxisZero0005GraphWholeA, GeneralCK/Certificates/E8TAxisZero0006GraphWholeA, GeneralCK/Certificates/E8TAxisZero0007GraphWholeA, GeneralCK/Certificates/E8TAxisZero0008GraphWholeA, GeneralCK/Certificates/E8TAxisZero0009GraphWholeA, GeneralCK/Certificates/E8TAxisZero0010GraphWholeA, GeneralCK/Certificates/E8TAxisZero0011GraphWholeA, GeneralCK/Certificates/E8TAxisZero0012GraphWholeA, GeneralCK/Certificates/E8TAxisZero0013GraphWholeA, GeneralCK/Certificates/E8TAxisZero0015GraphWholeA, GeneralCK/Certificates/E8TAxisZero0016GraphWholeA, GeneralCK/Certificates/E8TAxisZero0017GraphWholeA, GeneralCK/Certificates/E8TAxisZero0018GraphWholeA, GeneralCK/Certificates/E8TAxisZero0019GraphWholeA, GeneralCK/Certificates/E8TAxisZero0020GraphWholeA).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularUnconditionalSource

-- ===== source module GeneralCK.Certificates.E8TAxisZero0000GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0000GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-22662820719024547, 1266297624955622871203425286306175026059377347⟩,
   ⟨126629467412457383891962325705849207485803801899, 126630352663163569416891743950595378344323944816⟩,
   ⟨-25122171023263887892287, 177050836975966899054831181973763801624999293⟩,
   ⟨17704944549989160507927830505850472904245568630, 17705361993800868689815143524722982103359919024⟩,
   ⟨-18535278747007071365174228121, 83489256902086236448709670194277929909601678⟩,
   ⟨8348826778198302786000813924705679608818210299, 8349123514707230387123927400171578900366548387⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0000GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0001GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0001GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-22662820719024547, 1266297624955622871203425286306175026059377347⟩,
   ⟨126629467412457383891962325705849207485803801899, 126630352663163569416891743950595378344323944816⟩,
   ⟨-25122171023263887892287, 177050836975966899054831181973763801624999293⟩,
   ⟨17704944549989160507927830505850472904245568630, 17705361993800868689815143524722982103359919024⟩,
   ⟨-18535278747007071365174228121, 83489256902086236448709670194277929909601678⟩,
   ⟨8348826778198302786000813924705679608818210299, 8349123514707230387123927400171578900366548387⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0001GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0002GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0002GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-22662820719024547, 1266297624955622871203425286306175026059377347⟩,
   ⟨126629467412457383891962325705849207485803801899, 126630352663163569416891743950595378344323944816⟩,
   ⟨-25122171023263887892287, 177050836975966899054831181973763801624999293⟩,
   ⟨17704944549989160507927830505850472904245568630, 17705361993800868689815143524722982103359919024⟩,
   ⟨-18535278747007071365174228121, 83489256902086236448709670194277929909601678⟩,
   ⟨8348826778198302786000813924705679608818210299, 8349123514707230387123927400171578900366548387⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0002GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0003GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0003GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-22662820719024547, 1266297624955622871203425286306175026059377347⟩,
   ⟨126629467412457383891962325705849207485803801899, 126630352663163569416891743950595378344323944816⟩,
   ⟨-25122171023263887892287, 177050836975966899054831181973763801624999293⟩,
   ⟨17704944549989160507927830505850472904245568630, 17705361993800868689815143524722982103359919024⟩,
   ⟨-18535278747007071365174228121, 83489256902086236448709670194277929909601678⟩,
   ⟨8348826778198302786000813924705679608818210299, 8349123514707230387123927400171578900366548387⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0003GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0004GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0004GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-22662820719024547, 1266297624955622871203425286306175026059377347⟩,
   ⟨126629467412457383891962325705849207485803801899, 126630352663163569416891743950595378344323944816⟩,
   ⟨-25122171023263887892287, 177050836975966899054831181973763801624999293⟩,
   ⟨17704944549989160507927830505850472904245568630, 17705361993800868689815143524722982103359919024⟩,
   ⟨-18535278747007071365174228121, 83489256902086236448709670194277929909601678⟩,
   ⟨8348826778198302786000813924705679608818210299, 8349123514707230387123927400171578900366548387⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0004GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0005GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0005GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-22662820719024547, 1266297624955622871203425286306175026059377347⟩,
   ⟨126629467412457383891962325705849207485803801899, 126630352663163569416891743950595378344323944816⟩,
   ⟨-25122171023263887892287, 177050836975966899054831181973763801624999293⟩,
   ⟨17704944549989160507927830505850472904245568630, 17705361993800868689815143524722982103359919024⟩,
   ⟨-18535278747007071365174228121, 83489256902086236448709670194277929909601678⟩,
   ⟨8348826778198302786000813924705679608818210299, 8349123514707230387123927400171578900366548387⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0005GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0006GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0006GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-22662820719024547, 1266297624955622871203425286306175026059377347⟩,
   ⟨126629467412457383891962325705849207485803801899, 126630352663163569416891743950595378344323944816⟩,
   ⟨-25122171023263887892287, 177050836975966899054831181973763801624999293⟩,
   ⟨17704944549989160507927830505850472904245568630, 17705361993800868689815143524722982103359919024⟩,
   ⟨-18535278747007071365174228121, 83489256902086236448709670194277929909601678⟩,
   ⟨8348826778198302786000813924705679608818210299, 8349123514707230387123927400171578900366548387⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0006GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0007GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0007GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-22662820719024547, 1266297624955622871203425286306175026059377347⟩,
   ⟨126629467412457383891962325705849207485803801899, 126630352663163569416891743950595378344323944816⟩,
   ⟨-25122171023263887892287, 177050836975966899054831181973763801624999293⟩,
   ⟨17704944549989160507927830505850472904245568630, 17705361993800868689815143524722982103359919024⟩,
   ⟨-18535278747007071365174228121, 83489256902086236448709670194277929909601678⟩,
   ⟨8348826778198302786000813924705679608818210299, 8349123514707230387123927400171578900366548387⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0007GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0008GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0008GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-11008532462562, 633147705915515795023331642470956594340716867⟩,
   ⟨126629467412457383891962325730825599082799199938, 126629688724481676249275652944676708236045099266⟩,
   ⟨-48443448447076028754, 88524896683991564691804152586044155267537223⟩,
   ⟨17704944549989160507950547738237037944793455675, 17705048910478437691815944333768101463291331460⟩,
   ⟨-139571805779583766986298350, 41744257530780406772375555176985441782474566⟩,
   ⟨8348826778198315973601393351082387052204886503, 8348900962101486169767782353446789003711585553⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0008GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0009GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0009GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-11008532462562, 633147705915515795023331642470956594340716867⟩,
   ⟨126629467412457383891962325730825599082799199938, 126629688724481676249275652944676708236045099266⟩,
   ⟨-48443448447076028754, 88524896683991564691804152586044155267537223⟩,
   ⟨17704944549989160507950547738237037944793455675, 17705048910478437691815944333768101463291331460⟩,
   ⟨-139571805779583766986298350, 41744257530780406772375555176985441782474566⟩,
   ⟨8348826778198315973601393351082387052204886503, 8348900962101486169767782353446789003711585553⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0009GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0010GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0010GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-11008532462562, 633147705915515795023331642470956594340716867⟩,
   ⟨126629467412457383891962325730825599082799199938, 126629688724481676249275652944676708236045099266⟩,
   ⟨-48443448447076028754, 88524896683991564691804152586044155267537223⟩,
   ⟨17704944549989160507950547738237037944793455675, 17705048910478437691815944333768101463291331460⟩,
   ⟨-139571805779583766986298350, 41744257530780406772375555176985441782474566⟩,
   ⟨8348826778198315973601393351082387052204886503, 8348900962101486169767782353446789003711585553⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0010GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0011GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0011GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-11008532462562, 633147705915515795023331642470956594340716867⟩,
   ⟨126629467412457383891962325730825599082799199938, 126629688724481676249275652944676708236045099266⟩,
   ⟨-48443448447076028754, 88524896683991564691804152586044155267537223⟩,
   ⟨17704944549989160507950547738237037944793455675, 17705048910478437691815944333768101463291331460⟩,
   ⟨-139571805779583766986298350, 41744257530780406772375555176985441782474566⟩,
   ⟨8348826778198315973601393351082387052204886503, 8348900962101486169767782353446789003711585553⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0011GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0012GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0012GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-11008532462562, 633147705915515795023331642470956594340716867⟩,
   ⟨126629467412457383891962325730825599082799199938, 126629688724481676249275652944676708236045099266⟩,
   ⟨-48443448447076028754, 88524896683991564691804152586044155267537223⟩,
   ⟨17704944549989160507950547738237037944793455675, 17705048910478437691815944333768101463291331460⟩,
   ⟨-139571805779583766986298350, 41744257530780406772375555176985441782474566⟩,
   ⟨8348826778198315973601393351082387052204886503, 8348900962101486169767782353446789003711585553⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0012GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0013GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0013GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-11008532462562, 633147705915515795023331642470956594340716867⟩,
   ⟨126629467412457383891962325730825599082799199938, 126629688724481676249275652944676708236045099266⟩,
   ⟨-48443448447076028754, 88524896683991564691804152586044155267537223⟩,
   ⟨17704944549989160507950547738237037944793455675, 17705048910478437691815944333768101463291331460⟩,
   ⟨-139571805779583766986298350, 41744257530780406772375555176985441782474566⟩,
   ⟨8348826778198315973601393351082387052204886503, 8348900962101486169767782353446789003711585553⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0013GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0015GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0015GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0015GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0016GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0016GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0016GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0017GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0017GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-11008532462562, 633147705915515795023331642470956594340716867⟩,
   ⟨126629467412457383891962325730825599082799199938, 126629688724481676249275652944676708236045099266⟩,
   ⟨-48443448447076028754, 88524896683991564691804152586044155267537223⟩,
   ⟨17704944549989160507950547738237037944793455675, 17705048910478437691815944333768101463291331460⟩,
   ⟨-139571805779583766986298350, 41744257530780406772375555176985441782474566⟩,
   ⟨8348826778198315973601393351082387052204886503, 8348900962101486169767782353446789003711585553⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0017GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0018GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0018GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-11008532462562, 633147705915515795023331642470956594340716867⟩,
   ⟨126629467412457383891962325730825599082799199938, 126629688724481676249275652944676708236045099266⟩,
   ⟨-48443448447076028754, 88524896683991564691804152586044155267537223⟩,
   ⟨17704944549989160507950547738237037944793455675, 17705048910478437691815944333768101463291331460⟩,
   ⟨-139571805779583766986298350, 41744257530780406772375555176985441782474566⟩,
   ⟨8348826778198315973601393351082387052204886503, 8348900962101486169767782353446789003711585553⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0018GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0019GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0019GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-11008532462562, 633147705915515795023331642470956594340716867⟩,
   ⟨126629467412457383891962325730825599082799199938, 126629688724481676249275652944676708236045099266⟩,
   ⟨-48443448447076028754, 88524896683991564691804152586044155267537223⟩,
   ⟨17704944549989160507950547738237037944793455675, 17705048910478437691815944333768101463291331460⟩,
   ⟨-139571805779583766986298350, 41744257530780406772375555176985441782474566⟩,
   ⟨8348826778198315973601393351082387052204886503, 8348900962101486169767782353446789003711585553⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0019GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0020GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0020GraphWholeA
open Set DyadicInterval E8TAxisRegularDyadicEvaluator E8TAxisRegularGermJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev precision := 160
def input : DyadicInterval precision := rationalHull precision (0 / 1 : ℚ) (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
def qJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨-11008532462562, 633147705915515795023331642470956594340716867⟩,
   ⟨126629467412457383891962325730825599082799199938, 126629688724481676249275652944676708236045099266⟩,
   ⟨-48443448447076028754, 88524896683991564691804152586044155267537223⟩,
   ⟨17704944549989160507950547738237037944793455675, 17705048910478437691815944333768101463291331460⟩,
   ⟨-139571805779583766986298350, 41744257530780406772375555176985441782474566⟩,
   ⟨8348826778198315973601393351082387052204886503, 8348900962101486169767782353446789003711585553⟩⟩
theorem evaluator_checked : regularJetBox input = qJetBox := by decide +kernel

theorem regular_contains {y : ℝ}
    (hy : y ∈ Icc ((0 / 1 : ℚ) : ℝ) ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)) :
    qJetBox.Contains regularQJet y := by
  rw [← evaluator_checked]
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains
    (rationalHull_sound precision hy)
    ((show (0 : ℝ) ≤ ((0 / 1 : ℚ) : ℝ) by norm_num).trans hy.1)
    (hy.2.trans (show ((24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) ≤ 4 / 25 by norm_num))

#print axioms evaluator_checked
#print axioms regular_contains
end GeneralCK.Certificates.E8TAxisZero0020GraphWholeA

end


