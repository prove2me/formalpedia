-- Prove2me | Definitions.Def_OAIQ124K019
-- name    : OAIQ124K019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:09:06.436612+00:00
-- url     : https://prove2.me/theorems/2b124dc6-4063-4b03-8ea4-bf10a38c140b
-- title:
--   Definitions bundle OAIQ124K019 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 4 definitions and 4 theorems. The definitions and types are `OAI.KLInvariance.TitsSpace.bottCommonKernel`, `OAI.KLInvariance.TitsSpace.bottCommonSecond`, `OAI.KLInvariance.TitsSpace.bottSetFirst`, `OAI.KLInvariance.TitsSpace.bottSetSecond`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BalancedPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BalancedPairings.lean), [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean).
--
--   **Imports.** It imports the bundles `OAIQ124K016`, `OAIQ124K017` and `OAIQ124K018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K025`, `OAIQ124K027` and `OAIQ124K031`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ124K016
import Definitions.Def_OAIQ124K017
import Definitions.Def_OAIQ124K018

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

/-! Genuine first/reflected-tail maps on projected upper-set images. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius ReflectionPairTranslation
open CoordinateProjection ProjectiveRange
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def bottSetFirst (i : I) (l : List I) (U : Set W) : bottSetImage cs (i::l) U →ₗ[
    SymmetricCoefficient (M := M)] bottSetImage cs l U :=
  descend (bottSetProjection cs (i::l) U) (bottSetProjection_surjective cs (i::l) U)
    ((bottSetProjection cs l U).comp (bottHeadTail cs i l))
    (fun m hm => ((bottHeadSet_zero_iff cs i l U m).mp hm).1)

 def bottSetSecond (i : I) (l : List I) (U : Set W) : bottSetImage cs (i::l) U →ₗ[
    SymmetricCoefficient (M := M)]
    Twist (coefficientAction cs (cs.simple i)).toRingEquiv (bottSetImage cs l (simplePull cs i U)) :=
  descend (bottSetProjection cs (i::l) U) (bottSetProjection_surjective cs (i::l) U)
    ((twistMap (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottSetProjection cs l (simplePull cs i U))).comp (bottHeadReflectedTail cs i l))
    (fun m hm => Twist.ext (((bottHeadSet_zero_iff cs i l U m).mp hm).2))

 theorem bottSetFirst_project (i : I) (l : List I) (U : Set W) (m : BottSamelsonModule cs (i::l)) :
    bottSetFirst cs i l U (bottSetProjection cs (i::l) U m)=
      bottSetProjection cs l U (bottHeadTail cs i l m) := descend_apply _ _ _ _ m

 theorem bottSetSecond_project (i : I) (l : List I) (U : Set W) (m : BottSamelsonModule cs (i::l)) :
    bottSetSecond cs i l U (bottSetProjection cs (i::l) U m)=
      Twist.mk (bottSetProjection cs l (simplePull cs i U) (bottHeadReflectedTail cs i l m).val) :=
  descend_apply _ _ _ _ m

 theorem bottSetComponents_injective (i : I) (l : List I) (U : Set W) :
    Function.Injective ((bottSetFirst cs i l U).prod (bottSetSecond cs i l U)) := by
  apply injective_of_zero_lift (bottSetProjection cs (i::l) U)
    (bottSetProjection_surjective cs (i::l) U)
  intro m hz
  apply (bottHeadSet_zero_iff cs i l U m).mpr
  have hp := congrArg Prod.fst hz
  have hq := congrArg (fun z => z.2.val) hz
  exact ⟨(bottSetFirst_project cs i l U m).symm.trans hp,
    (congrArg Twist.val (bottSetSecond_project cs i l U m)).symm.trans hq⟩

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

 def bottCommonKernel (i : I) (l : List I) (U : Set W) :
    Submodule (SymmetricCoefficient (M := M)) (bottSetImage cs (i::l) U) :=
  LinearMap.ker (bottInterRestriction cs i (i::l) U) ⊓ LinearMap.ker (bottSetFirst cs i l U)

 def bottCommonSecond (i : I) (l : List I) (U : Set W) :
    bottCommonKernel cs i l U →ₗ[SymmetricCoefficient (M := M)]
      Twist (coefficientAction cs (cs.simple i)).toRingEquiv (bottSetImage cs l (simplePull cs i U)) :=
  (bottSetSecond cs i l U).comp (bottCommonKernel cs i l U).subtype

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BalancedPairings
attribute [-instance] _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded stalk duality, integral perfect balanced all-sections pairings, recognition and top grading.
-/


section

/-! A specified integral graded sheaf splitting identifies its source with
its literal projector image. No existence of a word/BMP splitting is assumed
outside each explicitly parametric helper. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G} (s : SplitIn B C)
noncomputable section

 theorem SplitIn.imageTo_toImage_vertex (x : V) (v : B.vertex x) :
    (s.imageTo.vertex x).map ((s.toImage.vertex x).map v)=v := by
  change (s.projection.vertex x).map ((s.inclusion.vertex x).map
    ((s.projection.vertex x).map ((s.inclusion.vertex x).map v)))=v
  rw [s.vertex_split,s.vertex_split]

end
end KLInvariance.MomentGraph.GradedSheaf

end


end OAI
end


