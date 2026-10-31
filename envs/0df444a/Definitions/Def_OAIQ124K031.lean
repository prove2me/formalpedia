-- Prove2me | Definitions.Def_OAIQ124K031
-- name    : OAIQ124K031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:11:00.301272+00:00
-- url     : https://prove2.me/theorems/552ee7eb-c76e-4b01-a889-d8f4f76580b3
-- title:
--   Definitions bundle OAIQ124K031 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean).
--
--   **Imports.** It imports the bundle `OAIQ124K019` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ124K032`.
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
open Module TensorProduct CoordinateProjection ReflectionPairTranslation
open FrobeniusDuality ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem bottSetFirst_restrict (i : I) (l : List I) {U K : Set W} (h : U⊆K)
    (z : bottSetImage cs (i::l) K) :
    bottSetFirst cs i l U (bottSetRestrict cs (i::l) h z)=
      bottSetRestrict cs l h (bottSetFirst cs i l K z) := by
  refine functions_eq_of_surjective (bottSetProjection cs (i::l) K)
    (bottSetProjection_surjective cs (i::l) K)
    (fun z => bottSetFirst cs i l U (bottSetRestrict cs (i::l) h z))
    (fun z => bottSetRestrict cs l h (bottSetFirst cs i l K z)) ?_ z
  intro m
  exact (bottSetFirst_project cs i l U m).trans
    (congrArg (bottSetRestrict cs l h) (bottSetFirst_project cs i l K m)).symm

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation ProjectiveRange
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottInter_first_zero (i : I) (l : List I) (U : Set W)
    (z : bottSetImage cs (i::l) U) (hz : bottInterRestriction cs i (i::l) U z=0) :
    bottInterRestriction cs i l U (bottSetFirst cs i l U z)=0 :=
  (bottSetFirst_restrict cs i l (fun _ h => h.1) z).symm.trans
    ((congrArg (bottSetFirst cs i l (simpleInter cs i U)) hz).trans (map_zero _))

end
end KLInvariance.TitsSpace

end


end OAI
end


