-- Prove2me | Definitions.Def_OAIQ124K027
-- name    : OAIQ124K027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:13:11.157878+00:00
-- url     : https://prove2.me/theorems/159ac907-a40d-4ee4-bd2d-39e75d1c3d91
-- title:
--   Definitions bundle OAIQ124K027 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean).
--
--   **Imports.** It imports the bundle `OAIQ124K019` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ124K028`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ124K019

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

 theorem bottCommon_range_of_patch (i : I) (l : List I) (U : Set W)
    (z : bottCommonKernel cs i l U) (m : BottSamelsonModule cs (i::l))
    (hm : bottSetProjection cs (i::l) U m=z.val) (n : BottSamelsonModule cs l)
    (hnU : bottSetProjection cs l U n=0)
    (hnq : bottSetProjection cs l (simplePull cs i U) n=
      bottSetProjection cs l (simplePull cs i U) (bottHeadReflectedTail cs i l m).val) :
    ∃ d : Twist (coefficientAction cs (cs.simple i)).toRingEquiv
        (LinearMap.ker (bottUnionRestriction cs i l U)),
      bottCommonSecond cs i l U z=
        twistMap (coefficientAction cs (cs.simple i)).toRingEquiv (bottUnionKernelSecond cs i l U) d := by
  let d : LinearMap.ker (bottUnionRestriction cs i l U) :=
    ⟨bottSetProjection cs l (simpleUnion cs i U) n,hnU⟩
  refine ⟨Twist.mk d,?_⟩
  change bottSetSecond cs i l U z.val=Twist.mk (bottSetProjection cs l (simplePull cs i U) n)
  exact ((congrArg (bottSetSecond cs i l U) hm).symm.trans
    (bottSetSecond_project cs i l U m)).trans (congrArg Twist.mk hnq.symm)

end
end KLInvariance.TitsSpace

end


end OAI
end


