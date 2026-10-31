-- Prove2me | Definitions.Def_OAIQ124K030
-- name    : OAIQ124K030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:43:45.819087+00:00
-- url     : https://prove2.me/theorems/b0744603-2629-42cf-8520-ecc6ea4be6e8
-- title:
--   Definitions bundle OAIQ124K030 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean).
--
--   **Imports.** It imports the bundles `OAIQ124K026`, `OAIQ124K020` and `OAIQ124K029` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ124K033`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ124K026
import Definitions.Def_OAIQ124K020
import Definitions.Def_OAIQ124K029

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
open Module CoordinateProjection ReflectionPairTranslation ProjectiveRange
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottCommon_projective (i : I) (l : List I) (HP : BottProjectiveUpper cs l)
    (HF : BottFlabby cs l) (U : Set W) (hU : BruhatUpper cs U) :
    Module.Projective (SymmetricCoefficient (M := M)) (bottCommonKernel cs i l U) := by
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l U) := HP U hU
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l (simpleUnion cs i U)) :=
    HP (simpleUnion cs i U) (hU.simpleUnion cs U i)
  let : Module.Projective (SymmetricCoefficient (M := M)) (LinearMap.ker (bottUnionRestriction cs i l U)) :=
    kernel_projective (bottUnionRestriction cs i l U) (bottSetRestrict_surjective cs l (fun _ h => Or.inl h))
  let : Module.Projective (SymmetricCoefficient (M := M))
      (Twist (coefficientAction cs (cs.simple i)).toRingEquiv (LinearMap.ker (bottUnionRestriction cs i l U))) :=
    Twist.projective _
  exact projective_of_coordinates (bottCommonSecond cs i l U) (bottCommonSecond_injective cs i l U)
    (twistMap (coefficientAction cs (cs.simple i)).toRingEquiv (bottUnionKernelSecond cs i l U))
    (twistMap_injective _ _ (bottUnionKernelSecond_injective cs i l U))
    (bottCommon_range_forward cs i l HF U hU) (bottCommon_range_backward cs i l U)

end
end KLInvariance.TitsSpace

end


end OAI
end


