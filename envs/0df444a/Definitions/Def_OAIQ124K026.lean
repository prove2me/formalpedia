-- Prove2me | Definitions.Def_OAIQ124K026
-- name    : OAIQ124K026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:14:15.238963+00:00
-- url     : https://prove2.me/theorems/2559ba9d-a062-4562-9c3c-d10b09ae8055
-- title:
--   Definitions bundle OAIQ124K026 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 1 instance and 3 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BottSamelson`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BottSamelson.lean), [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean).
--
--   **Imports.** It imports the bundle `OAIQ124K025` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K023` and `OAIQ124K030`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ124K025

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BottSamelson
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.bottSetImageAddCommGroup _root_.OAI.KLInvariance.TitsSpace.bottSetImageModule _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bott-Samelson tensor ranges, actual sections, grading and right kernels.
-/


section

/-! Unconditional integral free stalks and exact oriented edge kernels for
all tensor words. These are the local parts of BMP recognition; flabbiness
and the KL character are not asserted here. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 instance bottStalkFree (l : List I) (x : W) :
    Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x) :=
  (bottStandardStalks cs l).2 x

end
end KLInvariance.TitsSpace

end


end OAI
end

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

 theorem bottSetSecond_seed (i : I) (l : List I) (U : Set W) (n : BottSamelsonModule cs l) :
    bottSetSecond cs i l U (bottSetProjection cs (i::l) U (bottSeed cs i l n))=
      Twist.mk (bottSetProjection cs l (simplePull cs i U) n) :=
  (bottSetSecond_project cs i l U _).trans
    (congrArg (fun t => Twist.mk (bottSetProjection cs l (simplePull cs i U) t.val))
      (bottSeed_second cs i l n))

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

 theorem bottCommon_range_backward (i : I) (l : List I) (U : Set W)
    (d : Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (LinearMap.ker (bottUnionRestriction cs i l U))) :
    ∃ z : bottCommonKernel cs i l U,
      bottCommonSecond cs i l U z=
        twistMap (coefficientAction cs (cs.simple i)).toRingEquiv (bottUnionKernelSecond cs i l U) d := by
  let n : BottSamelsonModule cs l :=
    (bottSetProjection_surjective cs l (simpleUnion cs i U) d.val.val).choose
  have hn : bottSetProjection cs l (simpleUnion cs i U) n=d.val.val :=
    (bottSetProjection_surjective cs l (simpleUnion cs i U) d.val.val).choose_spec
  have hnU : bottSetProjection cs l U n=0 :=
    (congrArg (bottUnionRestriction cs i l U) hn).trans d.val.property
  let z : bottCommonKernel cs i l U :=
    ⟨bottSetProjection cs (i::l) U (bottSeed cs i l n),
      bottSeed_zero_inter cs i l U n hnU,(bottSetFirst_seed cs i l U n).trans hnU⟩
  refine ⟨z,?_⟩
  exact (bottSetSecond_seed cs i l U n).trans
    (congrArg Twist.mk (congrArg (bottUnionPullRestriction cs i l U) hn))

end
end KLInvariance.TitsSpace

end


section

/-! Prime-local realization on arbitrary upper coordinate sets. Projectivity
of the actual image is kept explicit here and discharged by word induction. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection FiniteCharacterLocalization
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottFlabby_of_projective (l : List I) (H : BottProjectiveUpper cs l) :
    BottFlabby cs l := by
  intro U hU z hz
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l U) := H U hU
  let : UniqueFactorizationMonoid (SymmetricCoefficient (M := M)) :=
    (SymmetricAlgebra.equivMvPolynomial (Module.Free.chooseBasis ℝ (Extended M))).symm.toRingEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  exact ProjectiveLattice.mem_of_prime_local_membership (bottSetImage cs l U) z
    ⟨bottCoordinateDenominator cs l,bottCoordinateDenominator_ne_zero cs l,bottSet_scaled cs l U z⟩
    (hz.local_denominator cs)

end
end KLInvariance.TitsSpace

end


end OAI
end


