-- Prove2me | Definitions.Def_OAIQ124K017
-- name    : OAIQ124K017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:02:00.977358+00:00
-- url     : https://prove2.me/theorems/d3167c12-fb47-4e9f-85f5-55edd6b7e4fc
-- title:
--   Definitions bundle OAIQ124K017 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 4 definitions and 8 theorems. The definitions and types are `OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.imageTo`, `OAI.KLInvariance.TitsSpace.bottUnionKernelSecond`, `OAI.KLInvariance.TitsSpace.bottUnionPullRestriction`, `OAI.KLInvariance.TitsSpace.bottUnionRestriction`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BalancedPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BalancedPairings.lean), [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean).
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K012`, `OAIQ124K013` and `OAIQ124K014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K019`, `OAIQ124K020` and `OAIQ124K021`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K012
import Definitions.Def_OAIQ124K013
import Definitions.Def_OAIQ124K014

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_IntegralPairings
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

 theorem bottSetProjection_surjective (l : List I) (U : Set W) :
    Function.Surjective (bottSetProjection cs l U) := project_surjective _ _

 theorem bottHeadSet_zero_iff (i : I) (l : List I) (U : Set W)
    (m : BottSamelsonModule cs (i::l)) :
    bottSetProjection cs (i::l) U m=0 ↔
      bottSetProjection cs l U (bottHeadTail cs i l m)=0 ∧
      bottSetProjection cs l (simplePull cs i U) (bottHeadReflectedTail cs i l m).val=0 := by
  constructor
  · intro hm
    have h := (bottSetProjection_zero_iff cs (i::l) U m).mp hm
    refine ⟨?_,?_⟩
    · apply (bottSetProjection_zero_iff cs l U _).mpr
      intro x hx
      exact congrArg Prod.fst ((bottHeadLocalPair_zero_iff cs i l x m).mp (h x hx))
    · apply (bottSetProjection_zero_iff cs l (simplePull cs i U) _).mpr
      intro x hx
      have hh : bottStalkProjection cs l (cs.simple i*(cs.simple i*x))
          (bottHeadReflectedTail cs i l m).val=0 := congrArg (fun z => z.2.val)
        ((bottHeadLocalPair_zero_iff cs i l (cs.simple i*x) m).mp (h _ hx))
      exact bottStalkProjection_zero_of_eq cs l (cs.simple_mul_simple_cancel_left i) _ hh
  · rintro ⟨hp,hq⟩
    apply (bottSetProjection_zero_iff cs (i::l) U m).mpr
    intro x hx
    apply (bottHeadLocalPair_zero_iff cs i l x m).mpr
    apply Prod.ext
    · exact (bottSetProjection_zero_iff cs l U _).mp hp x hx
    · apply Twist.ext
      exact (bottSetProjection_zero_iff cs l (simplePull cs i U) _).mp hq (cs.simple i*x)
        (by simpa only [simplePull,Set.mem_ofPred_eq,cs.simple_mul_simple_cancel_left] using hx)

end
end KLInvariance.TitsSpace

end


section

/-! Honest head/tail gluing. An exclusive-part crossing can only be the
simple head edge; alpha-divisibility handles precisely that crossing. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
open FrobeniusDuality ReflectionFrobenius
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem bottHeadPatch_compatible (i : I) (l : List I) (U : Set W) (hU : BruhatUpper cs U)
    (m : BottSamelsonModule cs (i::l))
    (hJ : ∀ x∈simpleInter cs i U,
      bottStalkProjection cs l x (bottHeadTail cs i l m)=
        bottStalkProjection cs l x (bottHeadReflectedTail cs i l m).val) :
    BottCompatible cs l (simpleUnion cs i U) (bottHeadPatch cs i l U m) := by
  classical
  intro x y hx hy hxy
  by_cases hxU : x∈U
  · have hyU := hU (.single hxy) hxU
    simp only [bottHeadPatch,ite_eq_left hxU,ite_eq_left hyU]
    exact ⟨bottHeadTail cs i l m,rfl,rfl⟩
  · by_cases hyU : y∈U
    · simp only [bottHeadPatch,ite_eq_right hxU,ite_eq_left hyU]
      by_cases hsy : cs.simple i*y∈U
      · exact ⟨(bottHeadReflectedTail cs i l m).val,rfl,(hJ y ⟨hyU,hsy⟩).symm⟩
      · have he := cross_edge_is_simple cs U hU i hxy (hx.resolve_left hxU) hsy
        subst y
        exact PairProjection.cross_lift _ _ (simpleRootPolynomial (M := M) i)
          (bottReflectionEdge_annihilated cs l x (cs.simple i) (simple_represents cs i))
          (bottHeadTail cs i l m) (bottHeadReflectedTail cs i l m).val (bottHead_difference cs i l m)
    · simp only [bottHeadPatch,ite_eq_right hxU,ite_eq_right hyU]
      exact ⟨(bottHeadReflectedTail cs i l m).val,rfl,rfl⟩

 theorem bottHeadPatch_lift (i : I) (l : List I) (H : BottFlabby cs l)
    (U : Set W) (hU : BruhatUpper cs U) (m : BottSamelsonModule cs (i::l))
    (hJ : ∀ x∈simpleInter cs i U,
      bottStalkProjection cs l x (bottHeadTail cs i l m)=
        bottStalkProjection cs l x (bottHeadReflectedTail cs i l m).val) :
    ∃ n : BottSamelsonModule cs l,
      (∀ x∈U, bottStalkProjection cs l x n=bottStalkProjection cs l x (bottHeadTail cs i l m)) ∧
      (∀ x∈simplePull cs i U,
        bottStalkProjection cs l x n=bottStalkProjection cs l x (bottHeadReflectedTail cs i l m).val) := by
  classical
  obtain ⟨n,hn⟩ := H (simpleUnion cs i U) (hU.simpleUnion cs U i)
    (bottHeadPatch cs i l U m) (bottHeadPatch_compatible cs i l U hU m hJ)
  refine ⟨n,?_,?_⟩
  · intro x hx
    have hh := congrFun hn ⟨x,Or.inl hx⟩
    simpa only [CoordinateProjection.eval,LinearMap.pi_apply,bottHeadPatch,ite_eq_left hx] using hh
  · intro x hx
    have hh := congrFun hn ⟨x,Or.inr hx⟩
    by_cases hxU : x∈U
    · have hh' : bottStalkProjection cs l x n=bottStalkProjection cs l x (bottHeadTail cs i l m) := by
        simpa only [CoordinateProjection.eval,LinearMap.pi_apply,bottHeadPatch,ite_eq_left hxU] using hh
      exact hh'.trans (hJ x ⟨hxU,hx⟩)
    · simpa only [CoordinateProjection.eval,LinearMap.pi_apply,bottHeadPatch,ite_eq_right hxU] using hh

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace
open Module TensorProduct CoordinateProjection ReflectionPairTranslation
open FrobeniusDuality ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem bottSetRestrict_surjective (l : List I) {U K : Set W} (h : U⊆K) :
    Function.Surjective (bottSetRestrict cs l h) := restrict_surjective _ h

 theorem bottSeed_zero_inter (i : I) (l : List I) (U : Set W)
    (n : BottSamelsonModule cs l) (hn : bottSetProjection cs l U n=0) :
    bottSetProjection cs (i::l) (simpleInter cs i U) (bottSeed cs i l n)=0 := by
  apply (bottHeadSet_zero_iff cs i l (simpleInter cs i U) _).mpr
  have h := (bottSetProjection_zero_iff cs l U n).mp hn
  constructor
  · apply ((congrArg (bottSetProjection cs l (simpleInter cs i U))
      (bottSeed_first cs i l n)).trans ·)
    apply (bottSetProjection_zero_iff cs l (simpleInter cs i U) n).mpr
    intro x hx
    exact h x hx.1
  · apply ((congrArg (fun t => bottSetProjection cs l (simplePull cs i (simpleInter cs i U)) t.val)
      (bottSeed_second cs i l n)).trans ·)
    apply (bottSetProjection_zero_iff cs l (simplePull cs i (simpleInter cs i U)) n).mpr
    intro x hx
    exact h x (by simpa only [cs.simple_mul_simple_cancel_left] using hx.2)

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

 def bottUnionRestriction (i : I) (l : List I) (U : Set W) :
    bottSetImage cs l (simpleUnion cs i U) →ₗ[SymmetricCoefficient (M := M)] bottSetImage cs l U :=
  bottSetRestrict cs l (fun _ h => Or.inl h)

 def bottUnionPullRestriction (i : I) (l : List I) (U : Set W) :
    bottSetImage cs l (simpleUnion cs i U) →ₗ[SymmetricCoefficient (M := M)]
      bottSetImage cs l (simplePull cs i U) :=
  bottSetRestrict cs l (fun _ h => Or.inr h)

 def bottUnionKernelSecond (i : I) (l : List I) (U : Set W) :
    LinearMap.ker (bottUnionRestriction cs i l U) →ₗ[SymmetricCoefficient (M := M)]
      bottSetImage cs l (simplePull cs i U) :=
  (bottUnionPullRestriction cs i l U).comp (LinearMap.ker (bottUnionRestriction cs i l U)).subtype

 theorem bottHeadPatch_lift_of_zero_inter (i : I) (l : List I) (H : BottFlabby cs l)
    (U : Set W) (hU : BruhatUpper cs U) (m : BottSamelsonModule cs (i::l))
    (hm : bottSetProjection cs (i::l) (simpleInter cs i U) m=0) :
    ∃ n : BottSamelsonModule cs l,
      (∀ x∈U, bottStalkProjection cs l x n=bottStalkProjection cs l x (bottHeadTail cs i l m)) ∧
      (∀ x∈simplePull cs i U,
        bottStalkProjection cs l x n=bottStalkProjection cs l x (bottHeadReflectedTail cs i l m).val) := by
  apply bottHeadPatch_lift cs i l H U hU m
  have hz := (bottHeadSet_zero_iff cs i l (simpleInter cs i U) m).mp hm
  intro x hx
  apply ((bottSetProjection_zero_iff cs l (simpleInter cs i U) _).mp hz.1 x hx).trans
  exact ((bottSetProjection_zero_iff cs l (simplePull cs i (simpleInter cs i U)) _).mp hz.2 x
    ((simpleInter_stable cs i U x).mpr hx)).symm

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BalancedPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded stalk duality, integral perfect balanced all-sections pairings, recognition and top grading.
-/


section

/-! Integral realization of tensor words as ALL sections of their actual
pair-projection sheaf. This assertion alone is not a BMP summand theorem,
flabbiness/standard-filtration theorem, or EW character theorem. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph FiniteCharacterLocalization
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottVertexProjection_stable (l : List I) (u b : W)
    (a : SymmetricCoefficient (M := M)) :
    (fun x : Interval cs u b => coefficientAction cs x.val a) ∈
      stabilizer (LinearMap.range (bottVertexProjection cs l u b)) := by
  rintro z ⟨m,rfl⟩
  refine ⟨bottSamelsonRight cs l a m,?_⟩
  funext x
  exact bottStalkProjection_right cs l x.val a m

end
end KLInvariance.TitsSpace

end


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

 def SplitIn.imageTo : Hom s.projector.image B := s.projection.comp s.projector.imageInclusion

end
end KLInvariance.MomentGraph.GradedSheaf

end


end OAI
end


