-- Prove2me | Definitions.Def_OAIQ124K025
-- name    : OAIQ124K025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:10:52.422994+00:00
-- url     : https://prove2.me/theorems/f86c7986-349d-483b-8ca4-0256957fdfdf
-- title:
--   Definitions bundle OAIQ124K025 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean).
--
--   **Imports.** It imports the bundle `OAIQ124K019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K026`, `OAIQ124K028` and `OAIQ124K032`.
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

 theorem bottSetFirst_seed (i : I) (l : List I) (U : Set W) (n : BottSamelsonModule cs l) :
    bottSetFirst cs i l U (bottSetProjection cs (i::l) U (bottSeed cs i l n))=
      bottSetProjection cs l U n :=
  (bottSetFirst_project cs i l U _).trans
    (congrArg (bottSetProjection cs l U) (bottSeed_first cs i l n))

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottCommonSecond_injective (i : I) (l : List I) (U : Set W) :
    Function.Injective (bottCommonSecond cs i l U) :=
  common_kernel_coordinate_injective _ _ _ (bottSetComponents_injective cs i l U)

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottCommon_lift (i : I) (l : List I) (U : Set W)
    (z : bottCommonKernel cs i l U) :
    ∃ m : BottSamelsonModule cs (i::l),
      bottSetProjection cs (i::l) U m=z.val ∧
      bottSetProjection cs (i::l) (simpleInter cs i U) m=0 ∧
      bottSetProjection cs l U (bottHeadTail cs i l m)=0 := by
  let m : BottSamelsonModule cs (i::l) :=
    (bottSetProjection_surjective cs (i::l) U z.val).choose
  have hm : bottSetProjection cs (i::l) U m=z.val :=
    (bottSetProjection_surjective cs (i::l) U z.val).choose_spec
  refine ⟨m,hm,?_,?_⟩
  · exact (congrArg (bottInterRestriction cs i (i::l) U) hm).trans z.property.1
  · exact (bottSetFirst_project cs i l U m).symm.trans
      ((congrArg (bottSetFirst cs i l U) hm).trans z.property.2)

 theorem bottCommon_patch_lift (i : I) (l : List I) (H : BottFlabby cs l)
    (U : Set W) (hU : BruhatUpper cs U) (m : BottSamelsonModule cs (i::l))
    (hmJ : bottSetProjection cs (i::l) (simpleInter cs i U) m=0)
    (hmp : bottSetProjection cs l U (bottHeadTail cs i l m)=0) :
    ∃ n : BottSamelsonModule cs l, bottSetProjection cs l U n=0 ∧
      bottSetProjection cs l (simplePull cs i U) n=
      bottSetProjection cs l (simplePull cs i U) (bottHeadReflectedTail cs i l m).val := by
  let n : BottSamelsonModule cs l := (bottHeadPatch_lift_of_zero_inter cs i l H U hU m hmJ).choose
  have hnp := (bottHeadPatch_lift_of_zero_inter cs i l H U hU m hmJ).choose_spec.1
  have hnq := (bottHeadPatch_lift_of_zero_inter cs i l H U hU m hmJ).choose_spec.2
  refine ⟨n,?_,Subtype.ext (funext fun x => hnq x.val x.property)⟩
  apply (bottSetProjection_zero_iff cs l U n).mpr
  intro x hx
  exact (hnp x hx).trans ((bottSetProjection_zero_iff cs l U _).mp hmp x hx)

end
end KLInvariance.TitsSpace

end


end OAI
end


