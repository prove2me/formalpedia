-- Prove2me | Definitions.Def_OAIQ124K028
-- name    : OAIQ124K028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:21:08.353884+00:00
-- url     : https://prove2.me/theorems/22ed7aaa-dd2a-402a-a8f9-5b416bc2e13b
-- title:
--   Definitions bundle OAIQ124K028 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean).
--
--   **Imports.** It imports the bundles `OAIQ124K025` and `OAIQ124K027` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ124K029`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ124K025
import Definitions.Def_OAIQ124K027

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_IntegralPairings
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert recurrences, projective section ranges, integral lattices and graded perfect adjoints.
-/


section

namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottCommon_range_of_lift (i : I) (l : List I) (H : BottFlabby cs l)
    (U : Set W) (hU : BruhatUpper cs U) (z : bottCommonKernel cs i l U)
    (m : BottSamelsonModule cs (i::l)) (hm : bottSetProjection cs (i::l) U m=z.val)
    (hmJ : bottSetProjection cs (i::l) (simpleInter cs i U) m=0)
    (hmp : bottSetProjection cs l U (bottHeadTail cs i l m)=0) :
    ∃ d : Twist (coefficientAction cs (cs.simple i)).toRingEquiv
        (LinearMap.ker (bottUnionRestriction cs i l U)),
      bottCommonSecond cs i l U z=
        twistMap (coefficientAction cs (cs.simple i)).toRingEquiv (bottUnionKernelSecond cs i l U) d := by
  exact bottCommon_range_of_patch cs i l U z m hm _
    (bottCommon_patch_lift cs i l H U hU m hmJ hmp).choose_spec.1
    (bottCommon_patch_lift cs i l H U hU m hmJ hmp).choose_spec.2

end
end KLInvariance.TitsSpace

end


end OAI
end


