-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0021GraphWholeA__22
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0021GraphWholeA__22
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T09:19:02.211184+00:00
-- url     : https://prove2.me/theorems/418452ca-13d4-4950-a783-2627ba1fe28a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0021GraphWholeA (+21 modules: GeneralCK.Certificates.E8TAxisZero0022GraphWholeA, GeneralCK.Certificates.E8TAxisZero0023Graph…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0021GraphWholeA (+21 modules: GeneralCK.Certificates.E8TAxisZero0022GraphWholeA, GeneralCK.Certificates.E8TAxisZero0023GraphWholeA, GeneralCK.Certificates.E8TAxisZero0024GraphWholeA, GeneralCK.Certificates.E8TAxisZero0025GraphWholeA, GeneralCK.Certificates.E8TAxisZero0026GraphWholeA, GeneralCK.Certificates.E8TAxisZero0027GraphWholeA, GeneralCK.Certificates.E8TAxisZero0028GraphWholeA, GeneralCK.Certificates.E8TAxisZero0029GraphWholeA, GeneralCK.Certificates.E8TAxisZero0030GraphWholeA, GeneralCK.Certificates.E8TAxisZero0031GraphWholeA, GeneralCK.Certificates.E8TAxisZero0032GraphWholeA, GeneralCK.Certificates.E8TAxisZero0033GraphWholeA, GeneralCK.Certificates.E8TAxisZero0034GraphWholeA, GeneralCK.Certificates.E8TAxisZero0035GraphWholeA, GeneralCK.Certificates.E8TAxisZero0036GraphWholeA, GeneralCK.Certificates.E8TAxisZero0037GraphWholeA, GeneralCK.Certificates.E8TAxisZero0038GraphWholeA, GeneralCK.Certificates.E8TAxisZero0039GraphWholeA, GeneralCK.Certificates.E8TAxisZero0040GraphWholeA, GeneralCK.Certificates.E8TAxisZero0041GraphWholeA, GeneralCK.Certificates.E8TAxisZero0042GraphWholeA)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0021GraphWholeA (+21 modules: GeneralCK.Certificates.E8TAxisZero0022GraphWholeA, GeneralCK.Certificates.E8TAxisZero0023GraphWholeA, GeneralCK.Certificates.E8TAxisZero0024GraphWholeA, GeneralCK.Certificates.E8TAxisZero0025GraphWholeA, GeneralCK.Certificates.E8TAxisZero0026GraphWholeA, GeneralCK.Certificates.E8TAxisZero0027GraphWholeA, GeneralCK.Certificates.E8TAxisZero0028GraphWholeA, GeneralCK.Certificates.E8TAxisZero0029GraphWholeA, GeneralCK.Certificates.E8TAxisZero0030GraphWholeA, GeneralCK.Certificates.E8TAxisZero0031GraphWholeA, GeneralCK.Certificates.E8TAxisZero0032GraphWholeA, GeneralCK.Certificates.E8TAxisZero0033GraphWholeA, GeneralCK.Certificates.E8TAxisZero0034GraphWholeA, GeneralCK.Certificates.E8TAxisZero0035GraphWholeA, GeneralCK.Certificates.E8TAxisZero0036GraphWholeA, GeneralCK.Certificates.E8TAxisZero0037GraphWholeA, GeneralCK.Certificates.E8TAxisZero0038GraphWholeA, GeneralCK.Certificates.E8TAxisZero0039GraphWholeA, GeneralCK.Certificates.E8TAxisZero0040GraphWholeA, GeneralCK.Certificates.E8TAxisZero0041GraphWholeA, GeneralCK.Certificates.E8TAxisZero0042GraphWholeA)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0021GraphWholeA (+21 modules: GeneralCK.Certificates.E8TAxisZero0022GraphWholeA, GeneralCK.Certificates.E8TAxisZero0023GraphWholeA, GeneralCK.Certificates.E8TAxisZero0024GraphWholeA, GeneralCK.Certificates.E8TAxisZero0025GraphWholeA, GeneralCK.Certificates.E8TAxisZero0026GraphWholeA, GeneralCK.Certificates.E8TAxisZero0027GraphWholeA, GeneralCK.Certificates.E8TAxisZero0028GraphWholeA, GeneralCK.Certificates.E8TAxisZero0029GraphWholeA, GeneralCK.Certificates.E8TAxisZero0030GraphWholeA, GeneralCK.Certificates.E8TAxisZero0031GraphWholeA, GeneralCK.Certificates.E8TAxisZero0032GraphWholeA, GeneralCK.Certificates.E8TAxisZero0033GraphWholeA, GeneralCK.Certificates.E8TAxisZero0034GraphWholeA, GeneralCK.Certificates.E8TAxisZero0035GraphWholeA, GeneralCK.Certificates.E8TAxisZero0036GraphWholeA, GeneralCK.Certificates.E8TAxisZero0037GraphWholeA, GeneralCK.Certificates.E8TAxisZero0038GraphWholeA, GeneralCK.Certificates.E8TAxisZero0039GraphWholeA, GeneralCK.Certificates.E8TAxisZero0040GraphWholeA, GeneralCK.Certificates.E8TAxisZero0041GraphWholeA, GeneralCK.Certificates.E8TAxisZero0042GraphWholeA) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0021GraphWholeA (+21 modules: GeneralCK/Certificates/E8TAxisZero0022GraphWholeA, GeneralCK/Certificates/E8TAxisZero0023GraphWholeA, GeneralCK/Certificates/E8TAxisZero0024GraphWholeA, GeneralCK/Certificates/E8TAxisZero0025GraphWholeA, GeneralCK/Certificates/E8TAxisZero0026GraphWholeA, GeneralCK/Certificates/E8TAxisZero0027GraphWholeA, GeneralCK/Certificates/E8TAxisZero0028GraphWholeA, GeneralCK/Certificates/E8TAxisZero0029GraphWholeA, GeneralCK/Certificates/E8TAxisZero0030GraphWholeA, GeneralCK/Certificates/E8TAxisZero0031GraphWholeA, GeneralCK/Certificates/E8TAxisZero0032GraphWholeA, GeneralCK/Certificates/E8TAxisZero0033GraphWholeA, GeneralCK/Certificates/E8TAxisZero0034GraphWholeA, GeneralCK/Certificates/E8TAxisZero0035GraphWholeA, GeneralCK/Certificates/E8TAxisZero0036GraphWholeA, GeneralCK/Certificates/E8TAxisZero0037GraphWholeA, GeneralCK/Certificates/E8TAxisZero0038GraphWholeA, GeneralCK/Certificates/E8TAxisZero0039GraphWholeA, GeneralCK/Certificates/E8TAxisZero0040GraphWholeA, GeneralCK/Certificates/E8TAxisZero0041GraphWholeA, GeneralCK/Certificates/E8TAxisZero0042GraphWholeA).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularUnconditionalSource

-- ===== source module GeneralCK.Certificates.E8TAxisZero0021GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0021GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0021GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0022GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0022GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0022GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0023GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0023GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0023GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0024GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0024GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0024GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0025GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0025GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0025GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0026GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0026GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0026GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0027GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0027GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0027GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0028GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0028GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0028GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0029GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0029GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0029GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0030GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0030GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0030GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0031GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0031GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0031GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0032GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0032GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0032GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0033GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0033GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0033GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0034GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0034GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0034GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0035GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0035GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0035GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0036GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0036GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0036GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0037GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0037GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0037GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0038GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0038GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0038GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0039GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0039GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0039GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0040GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0040GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0040GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0041GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0041GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0041GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0042GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0042GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0042GraphWholeA

end


