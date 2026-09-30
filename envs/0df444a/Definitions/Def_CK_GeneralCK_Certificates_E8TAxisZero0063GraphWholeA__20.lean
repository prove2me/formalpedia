-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0063GraphWholeA__20
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0063GraphWholeA__20
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T08:05:13.814749+00:00
-- url     : https://prove2.me/theorems/7d3136e6-9bd1-4ba1-9c6f-d439b5d845c4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0063GraphWholeA (+19 modules: GeneralCK.Certificates.E8TAxisZero0064GraphWholeA, GeneralCK.Certificates.E8TAxisZero0065Graph…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0063GraphWholeA (+19 modules: GeneralCK.Certificates.E8TAxisZero0064GraphWholeA, GeneralCK.Certificates.E8TAxisZero0065GraphWholeA, GeneralCK.Certificates.E8TAxisZero0066GraphWholeA, GeneralCK.Certificates.E8TAxisZero0067GraphWholeA, GeneralCK.Certificates.E8TAxisZero0068GraphWholeA, GeneralCK.Certificates.E8TAxisZero0069GraphWholeA, GeneralCK.Certificates.E8TAxisZero0070GraphWholeA, GeneralCK.Certificates.E8TAxisZero0071GraphWholeA, GeneralCK.Certificates.E8TAxisZero0072GraphWholeA, GeneralCK.Certificates.E8TAxisZero0073GraphWholeA, GeneralCK.Certificates.E8TAxisZero0074GraphWholeA, GeneralCK.Certificates.E8TAxisZero0075GraphWholeA, GeneralCK.Certificates.E8TAxisZero0076GraphWholeA, GeneralCK.Certificates.E8TAxisZero0077GraphWholeA, GeneralCK.Certificates.E8TAxisZero0078GraphWholeA, GeneralCK.Certificates.E8TAxisZero0079GraphWholeA, GeneralCK.Certificates.E8TAxisZero0080GraphWholeA, GeneralCK.Certificates.E8TAxisZero0081GraphWholeA, GeneralCK.Certificates.E8TAxisZero0082GraphWholeA)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0063GraphWholeA (+19 modules: GeneralCK.Certificates.E8TAxisZero0064GraphWholeA, GeneralCK.Certificates.E8TAxisZero0065GraphWholeA, GeneralCK.Certificates.E8TAxisZero0066GraphWholeA, GeneralCK.Certificates.E8TAxisZero0067GraphWholeA, GeneralCK.Certificates.E8TAxisZero0068GraphWholeA, GeneralCK.Certificates.E8TAxisZero0069GraphWholeA, GeneralCK.Certificates.E8TAxisZero0070GraphWholeA, GeneralCK.Certificates.E8TAxisZero0071GraphWholeA, GeneralCK.Certificates.E8TAxisZero0072GraphWholeA, GeneralCK.Certificates.E8TAxisZero0073GraphWholeA, GeneralCK.Certificates.E8TAxisZero0074GraphWholeA, GeneralCK.Certificates.E8TAxisZero0075GraphWholeA, GeneralCK.Certificates.E8TAxisZero0076GraphWholeA, GeneralCK.Certificates.E8TAxisZero0077GraphWholeA, GeneralCK.Certificates.E8TAxisZero0078GraphWholeA, GeneralCK.Certificates.E8TAxisZero0079GraphWholeA, GeneralCK.Certificates.E8TAxisZero0080GraphWholeA, GeneralCK.Certificates.E8TAxisZero0081GraphWholeA, GeneralCK.Certificates.E8TAxisZero0082GraphWholeA)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0063GraphWholeA (+19 modules: GeneralCK.Certificates.E8TAxisZero0064GraphWholeA, GeneralCK.Certificates.E8TAxisZero0065GraphWholeA, GeneralCK.Certificates.E8TAxisZero0066GraphWholeA, GeneralCK.Certificates.E8TAxisZero0067GraphWholeA, GeneralCK.Certificates.E8TAxisZero0068GraphWholeA, GeneralCK.Certificates.E8TAxisZero0069GraphWholeA, GeneralCK.Certificates.E8TAxisZero0070GraphWholeA, GeneralCK.Certificates.E8TAxisZero0071GraphWholeA, GeneralCK.Certificates.E8TAxisZero0072GraphWholeA, GeneralCK.Certificates.E8TAxisZero0073GraphWholeA, GeneralCK.Certificates.E8TAxisZero0074GraphWholeA, GeneralCK.Certificates.E8TAxisZero0075GraphWholeA, GeneralCK.Certificates.E8TAxisZero0076GraphWholeA, GeneralCK.Certificates.E8TAxisZero0077GraphWholeA, GeneralCK.Certificates.E8TAxisZero0078GraphWholeA, GeneralCK.Certificates.E8TAxisZero0079GraphWholeA, GeneralCK.Certificates.E8TAxisZero0080GraphWholeA, GeneralCK.Certificates.E8TAxisZero0081GraphWholeA, GeneralCK.Certificates.E8TAxisZero0082GraphWholeA) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0063GraphWholeA (+19 modules: GeneralCK/Certificates/E8TAxisZero0064GraphWholeA, GeneralCK/Certificates/E8TAxisZero0065GraphWholeA, GeneralCK/Certificates/E8TAxisZero0066GraphWholeA, GeneralCK/Certificates/E8TAxisZero0067GraphWholeA, GeneralCK/Certificates/E8TAxisZero0068GraphWholeA, GeneralCK/Certificates/E8TAxisZero0069GraphWholeA, GeneralCK/Certificates/E8TAxisZero0070GraphWholeA, GeneralCK/Certificates/E8TAxisZero0071GraphWholeA, GeneralCK/Certificates/E8TAxisZero0072GraphWholeA, GeneralCK/Certificates/E8TAxisZero0073GraphWholeA, GeneralCK/Certificates/E8TAxisZero0074GraphWholeA, GeneralCK/Certificates/E8TAxisZero0075GraphWholeA, GeneralCK/Certificates/E8TAxisZero0076GraphWholeA, GeneralCK/Certificates/E8TAxisZero0077GraphWholeA, GeneralCK/Certificates/E8TAxisZero0078GraphWholeA, GeneralCK/Certificates/E8TAxisZero0079GraphWholeA, GeneralCK/Certificates/E8TAxisZero0080GraphWholeA, GeneralCK/Certificates/E8TAxisZero0081GraphWholeA, GeneralCK/Certificates/E8TAxisZero0082GraphWholeA).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularUnconditionalSource

-- ===== source module GeneralCK.Certificates.E8TAxisZero0063GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0063GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0063GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0064GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0064GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0064GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0065GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0065GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0065GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0066GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0066GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0066GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0067GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0067GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0067GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0068GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0068GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0068GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0069GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0069GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0069GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0070GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0070GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0070GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0071GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0071GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0071GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0072GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0072GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0072GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0073GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0073GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0073GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0074GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0074GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0074GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0075GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0075GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0075GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0076GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0076GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0076GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0077GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0077GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0077GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0078GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0078GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0078GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0079GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0079GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0079GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0080GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0080GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0080GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0081GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0081GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0081GraphWholeA

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0082GraphWholeA =====
section

namespace GeneralCK.Certificates.E8TAxisZero0082GraphWholeA
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
end GeneralCK.Certificates.E8TAxisZero0082GraphWholeA

end


