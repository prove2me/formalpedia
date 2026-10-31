-- Prove2me | Definitions.Def_OAIQ124K020
-- name    : OAIQ124K020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:10:41.700153+00:00
-- url     : https://prove2.me/theorems/3405e42e-cb4a-48c6-bb66-f4781c68caf7
-- title:
--   Definitions bundle OAIQ124K020 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 32 declarations of OpenAI's Lean: 5 definitions and 27 theorems. The definitions and types are `OAI.KLInvariance.TitsSpace.bottAdjointSheaf`, `OAI.KLInvariance.TitsSpace.bottAdjointWordHom`, `OAI.KLInvariance.TitsSpace.bottEndOfSheaf`, `OAI.KLInvariance.TitsSpace.bottSectionEquiv`, `OAI.KLInvariance.TitsSpace.bottSplitAdjointSheaf`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BalancedPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BalancedPairings.lean), [`KazhdanLusztig_Frobenius`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Frobenius.lean), [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean), [`KazhdanLusztig_Support`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Support.lean).
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K016`, `OAIQ124K017` and `OAIQ124K018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K022`, `OAIQ124K023`, `OAIQ124K030` and `OAIQ124K032`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K016
import Definitions.Def_OAIQ124K017
import Definitions.Def_OAIQ124K018

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Frobenius
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_graded _root_.OAI.KLInvariance.TitsSpace.bottHeadPairAddCommGroup _root_.OAI.KLInvariance.TitsSpace.bottHeadPairModule _root_.OAI.KLInvariance.TitsSpace.bottSetImageAddCommGroup _root_.OAI.KLInvariance.TitsSpace.bottSetImageModule _root_.OAI.KLInvariance.TitsSpace.bottStalkFinite _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_graded _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coxeter Frobenius extensions, tensor duality and translation across reflection pairs.
-/


section

/-! Tensor induction of integral self-dual bimodules across a Frobenius
extension. All pairings refer to actual integral modules. -/
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
noncomputable section

attribute [instance] PairedModule.add PairedModule.module PairedModule.free PairedModule.finite

end
end KLInvariance.FrobeniusDuality

end


section

/-! The actual tensor word's integral weight-support lattice is the dual of
its integral projected stalk lattice. This is not merely a fraction-field
isomorphism. It still does NOT identify BMP sections with an indecomposable
summand of the tensor word, or prove the character theorem. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bott_supported_annihilates (l : List I) (x : W) {m : BottSamelsonModule cs l}
    (hm : m ∈ bottWeightSupported cs l x) (n : BottSamelsonModule cs l)
    (hn : bottWeightProjection cs l x n=0) : bottSamelsonDuality cs l m n=0 := by
  classical
  have hn' := (bottWeightProjection_eq_zero cs l x n).mp hn
  have hsum : ∑ e : BottIndex l, bottEvaluation cs l e n *
      bottSamelsonDuality cs l m (bottCoordinateLift cs l e) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    by_cases he : bottWeight cs l e=x
    · rw [hn' e he,zero_mul]
    · rw [bott_distinct_weight_orthogonal cs l (Ne.symm he) hm
        (bottCoordinateLift_supported cs l e),mul_zero]
  have hh := congrArg (bottSamelsonDuality cs l m) (bottCoordinateExpansion cs l n)
  simp only [map_smul,map_sum,smul_eq_mul] at hh
  rw [hsum] at hh
  exact (mul_eq_zero.mp hh).resolve_left (bottCoordinateDenominator_ne_zero cs l)

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

/-! Genuine first/reflected-tail maps on projected upper-set images. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius ReflectionPairTranslation
open CoordinateProjection ProjectiveRange
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem bottHead_components_injective (i : I) (l : List I)
    (m : BottSamelsonModule cs (i::l))
    (hp : bottHeadTail cs i l m=0) (hq : bottHeadReflectedTail cs i l m=0) : m=0 := by
  apply bottEvaluation_injective cs (i::l)
  funext e
  have hz : bottStalkProjection cs (i::l) (bottWeight cs (i::l) e) m=0 := by
    apply (bottHeadLocalPair_zero_iff cs i l _ m).mpr
    rw [bottHeadLocalPair_value,hp,hq]
    apply Prod.ext
    · exact map_zero _
    · apply Twist.ext
      exact map_zero _
  exact congrArg (fun z => z.val ⟨e,rfl⟩) hz

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

 theorem bottSeed_zero_stable (i : I) (l : List I) (U : Set W)
    (hU : ∀ x, cs.simple i*x∈U ↔ x∈U)
    (n : BottSamelsonModule cs l) (hn : bottSetProjection cs l U n=0) :
    bottSetProjection cs (i::l) U (bottSeed cs i l n)=0 := by
  apply (bottHeadSet_zero_iff cs i l U _).mpr
  constructor
  · exact (congrArg (bottSetProjection cs l U) (bottSeed_first cs i l n)).trans hn
  · apply ((congrArg (fun t => bottSetProjection cs l (simplePull cs i U) t.val)
      (bottSeed_second cs i l n)).trans ·)
    apply (bottSetProjection_zero_iff cs l (simplePull cs i U) n).mpr
    intro x hx
    exact (bottSetProjection_zero_iff cs l U n).mp hn x ((hU x).mp hx)

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

 theorem bottUnionKernelSecond_injective (i : I) (l : List I) (U : Set W) :
    Function.Injective (bottUnionKernelSecond cs i l U) := by
  apply kernel_coordinate_injective
  exact restrict_joint_injective (bottStalkProjection cs l)
    (fun _ h => Or.inl h) (fun _ h => Or.inr h) (fun _ h => h)

end
end KLInvariance.TitsSpace

end


section

/-! Projectivity on reflection-stable upper sets, via an ACTUAL tensor
splitting rather than an asserted reflexivity of a projected lattice. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection ProjectiveRange ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottTensorEnd_set_preserve (i : I) (l : List I) (U : Set W)
    (hU : ∀ x, cs.simple i*x∈U ↔ x∈U)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (he : ∀ n x, x∈U → bottStalkProjection cs l x (e n)=bottStalkProjection cs l x n)
    (m : BottSamelsonModule cs (i::l)) :
    bottSetProjection cs (i::l) U (bottTensorEnd cs i l e m)=bottSetProjection cs (i::l) U m := by
  apply Subtype.ext
  funext x
  apply (bottHeadLocalPair_eq_iff cs i l x.val _ _).mpr
  apply (bottHeadLocalPair_value cs i l x.val _).trans
  apply Eq.trans ?_ (bottHeadLocalPair_value cs i l x.val m).symm
  apply Prod.ext
  · exact (congrArg (bottStalkProjection cs l x.val) (bottTensorEnd_first cs i l e m)).trans
      (he _ x.val x.property)
  · apply Twist.ext
    exact (congrArg (fun t => bottStalkProjection cs l (cs.simple i*x.val) t.val)
      (bottTensorEnd_second cs i l e m)).trans
      (he _ (cs.simple i*x.val) ((hU x.val).mpr x.property))

 theorem bottTensorEnd_set_kills (i : I) (l : List I) (U : Set W)
    (hU : ∀ x, cs.simple i*x∈U ↔ x∈U)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (hz : ∀ n, bottSetProjection cs l U n=0 → e n=0)
    (m : BottSamelsonModule cs (i::l)) (hm : bottSetProjection cs (i::l) U m=0) :
    bottTensorEnd cs i l e m=0 := by
  have hmpq := (bottHeadSet_zero_iff cs i l U m).mp hm
  have hqzero : bottSetProjection cs l U (bottHeadReflectedTail cs i l m).val=0 := by
    apply (bottSetProjection_zero_iff cs l U _).mpr
    intro x hx
    exact (bottSetProjection_zero_iff cs l (simplePull cs i U) _).mp hmpq.2 x ((hU x).mpr hx)
  apply bottHead_components_injective cs i l
  · exact (bottTensorEnd_first cs i l e m).trans (hz _ hmpq.1)
  · apply Twist.ext
    exact (congrArg Twist.val (bottTensorEnd_second cs i l e m)).trans (hz _ hqzero)

 theorem bottStableUpper_projective (i : I) (l : List I) (U : Set W)
    (hU : ∀ x, cs.simple i*x∈U ↔ x∈U)
    [Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l U)] :
    Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs (i::l) U) := by
  obtain ⟨s,hs⟩ := Module.projective_lifting_property (bottSetProjection cs l U)
    (LinearMap.id : bottSetImage cs l U →ₗ[SymmetricCoefficient (M := M)] bottSetImage cs l U)
    (bottSetProjection_surjective cs l U)
  have hs' : ∀ p, bottSetProjection cs l U (s p)=p := LinearMap.congr_fun hs
  let e := s.comp (bottSetProjection cs l U)
  have he : ∀ n x, x∈U → bottStalkProjection cs l x (e n)=bottStalkProjection cs l x n := by
    intro n x hx
    exact congrArg (fun z : bottSetImage cs l U => z.val ⟨x,hx⟩) (hs' (bottSetProjection cs l U n))
  have hz : ∀ n, bottSetProjection cs l U n=0 → e n=0 := by
    intro n hn
    exact (congrArg s hn).trans s.map_zero
  exact projective_of_end (bottSetProjection cs (i::l) U) (bottSetProjection_surjective cs (i::l) U)
    (bottTensorEnd cs i l e) (bottTensorEnd_set_preserve cs i l U hU e he)
    (bottTensorEnd_set_kills cs i l U hU e hz)

end
end KLInvariance.TitsSpace

end


section

/-! Unconditional flabbiness of the actual integral tensor-word projection
sheaf, obtained from projectivity of every upper-coordinate image. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottSetImage_nil_projective (U : Set W) :
    Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs [] U) := by
  by_cases hU : (1 : W)∈U
  · exact Module.Projective.of_equiv (LinearEquiv.ofBijective (bottSetProjection cs [] U)
      ⟨bottSetProjection_nil_injective cs U hU,bottSetProjection_surjective cs [] U⟩)
  · let := bottSetImage_nil_subsingleton cs U hU
    infer_instance

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BalancedPairings
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded stalk duality, integral perfect balanced all-sections pairings, recognition and top grading.
-/


section

/-! The actual word adjoint preserves homogeneity. Projection kernels are
annihilators of the actual supported lattices, integrally, with no localization
or freeness assumption on the projection lattice. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bott_projection_zero_iff_annihilates_support (l : List I) (x : W)
    (m : BottSamelsonModule cs l) :
    bottStalkProjection cs l x m=0 ↔ ∀ s : bottWeightSupported cs l x,
      bottSamelsonDuality cs l s.val m=0 := by
  constructor
  · intro hm s
    exact bott_supported_annihilates cs l x s.property m
      ((bottStalkProjection_eq_zero cs l x m).mp hm)
  · intro h
    apply Subtype.ext
    funext e
    let lam : Dual (SymmetricCoefficient (M := M)) (bottStalk cs l x) :=
      (LinearMap.proj e).comp (bottStalk cs l x).subtype
    have he := h (bottStalkDualToSupport cs l x lam)
    rw [bottPairing_dualToSupport] at he
    exact he

 theorem bottAdjoint_preserves_kernel (l : List I) (x : W)
    (f : End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (hf : ∀ s, s ∈ bottWeightSupported cs l x → f s ∈ bottWeightSupported cs l x)
    (m : BottSamelsonModule cs l) (hm : bottStalkProjection cs l x m=0) :
    bottStalkProjection cs l x (bottAdjoint cs l f m)=0 := by
  apply (bott_projection_zero_iff_annihilates_support cs l x _).mpr
  intro s
  change bottSamelsonDuality cs l s.val (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) f m)=0
  rw [PerfectAdjoint.symmetric_pairing (bottSamelsonDuality cs l)
    (bottSamelson_symmetric cs l)]
  exact (bott_projection_zero_iff_annihilates_support cs l x m).mp hm ⟨f s.val,hf s.val s.property⟩

end
end KLInvariance.TitsSpace

end


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

 theorem bottSection_prime_lift (l : List I) (u b : W)
    (s : (bottProjectionSheaf cs l u b).sections Set.univ)
    (p : SymmetricCoefficient (M := M)) (hp : Prime p) (x : Interval cs u b) :
    ∃ m : BottSamelsonModule cs l, ∀ y : Interval cs u b,
      (∀ a, p ∣ coefficientAction cs x.val a-coefficientAction cs y.val a) →
      bottStalkProjection cs l y.val m=s.val y := by
  classical
  by_cases hx : ∃ y : Interval cs u b, x ≠ y ∧
      ∀ a, p ∣ coefficientAction cs x.val a-coefficientAction cs y.val a
  · obtain ⟨y,hxy,hcon⟩ := hx
    obtain ⟨t,ht,he,hclass⟩ := prime_character_class cs p hp
      (fun h => hxy (Subtype.ext h)) hcon
    obtain ⟨m,hm,hn⟩ := bottSection_pair_lift cs l u b s x y t ht he.symm
    refine ⟨m,?_⟩
    intro z hz
    rcases (hclass z.val).mp hz with hxz | hzy
    · have h : z=x := Subtype.ext hxz.symm
      subst z
      exact hm
    · have h : z=y := Subtype.ext (hzy.trans he.symm)
      subst z
      exact hn
  · obtain ⟨m,hm⟩ := bottStalkProjection_surjective cs l x.val (s.val x)
    refine ⟨m,?_⟩
    intro y hy
    have h : y=x := by
      by_contra h
      exact hx ⟨y,Ne.symm h,hy⟩
    subst y
    exact hm

 theorem bottSection_local_denominator (l : List I) (u b : W)
    (s : (bottProjectionSheaf cs l u b).sections Set.univ)
    (p : SymmetricCoefficient (M := M)) (hp : Prime p) :
    ∃ a : SymmetricCoefficient (M := M), ¬ p ∣ a ∧ a • s.val ∈
      LinearMap.range (bottVertexProjection cs l u b) := by
  classical
  let : Finite (Interval cs u b) := interval_finite cs u b
  let : Fintype (Interval cs u b) := Fintype.ofFinite _
  apply character_local_denominator (E := fun x : Interval cs u b => bottStalk cs l x.val)
    (LinearMap.range (bottVertexProjection cs l u b)) p hp
    (fun a x => coefficientAction cs x.val a) (fun a => bottVertexProjection_stable cs l u b a) s.val
  intro x
  obtain ⟨m,hm⟩ := bottSection_prime_lift cs l u b s p hp x
  exact ⟨bottVertexProjection cs l u b m,⟨m,rfl⟩,hm⟩

 theorem bottSection_surjective (l : List I) (hl : cs.IsReduced l) :
    Function.Surjective (bottSection cs l 1 (cs.wordProd l)) := by
  intro s
  let L := LinearMap.range (bottVertexProjection cs l 1 (cs.wordProd l))
  let : Module.Free (SymmetricCoefficient (M := M)) L :=
    Module.Free.of_equiv (LinearEquiv.ofInjective _ (bottVertexProjection_injective cs l hl))
  let : UniqueFactorizationMonoid (SymmetricCoefficient (M := M)) :=
    (SymmetricAlgebra.equivMvPolynomial (Module.Free.chooseBasis ℝ (Extended M))).symm.toRingEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  have h : s.val ∈ L := EdgeLattice.mem_of_prime_local_membership L s.val
    ⟨bottCoordinateDenominator cs l,bottCoordinateDenominator_ne_zero cs l,
      bottVertexProjection_scaled cs l hl s.val⟩
    (fun p hp => bottSection_local_denominator cs l 1 (cs.wordProd l) s p hp)
  obtain ⟨m,hm⟩ := h
  exact ⟨m,Subtype.ext hm⟩

 def bottSectionEquiv (l : List I) (hl : cs.IsReduced l) :
    BottSamelsonModule cs l ≃ₗ[SymmetricCoefficient (M := M)]
      (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ :=
  LinearEquiv.ofBijective (bottSection cs l 1 (cs.wordProd l))
    ⟨bottSection_injective cs l hl,bottSection_surjective cs l hl⟩

end
end KLInvariance.TitsSpace

end


section

/-! Endomorphisms of the ACTUAL graded word sheaf act on its integral tensor
module and preserve every stalk kernel and single-weight support lattice. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

 def bottEndOfSheaf (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l) :=
  (bottSectionEquiv cs l hl).symm.toLinearMap.comp
    ((h.sectionMap Set.univ).comp (bottSectionEquiv cs l hl).toLinearMap)

 theorem bottEndOfSheaf_coordinates (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (m : BottSamelsonModule cs l) (x : Interval cs 1 (cs.wordProd l)) :
    bottStalkProjection cs l x.val (bottEndOfSheaf cs basis l hl h m)=
      (h.vertex x).map (bottStalkProjection cs l x.val m) := by
  have he := congrArg (fun s : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ =>
    s.val x) ((bottSectionEquiv cs l hl).apply_symm_apply
      (h.sectionMap Set.univ ((bottSectionEquiv cs l hl) m)))
  exact he

 theorem bottEndOfSheaf_homogeneous (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (n : ℤ) (m : BottSamelsonModule cs l) (hm : m ∈ bottPiece cs basis l n) :
    bottEndOfSheaf cs basis l hl h m ∈ bottPiece cs basis l n := by
  apply (bottPiece_iff_stalks cs basis l hl n _).mpr
  intro x
  rw [bottEndOfSheaf_coordinates]
  exact (h.vertex x).graded n _ (bottStalkProjection_homogeneous cs basis l x.val n m hm)

 theorem bottEndOfSheaf_preserves_kernel (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (x : Interval cs 1 (cs.wordProd l)) (m : BottSamelsonModule cs l)
    (hm : bottStalkProjection cs l x.val m=0) :
    bottStalkProjection cs l x.val (bottEndOfSheaf cs basis l hl h m)=0 := by
  rw [bottEndOfSheaf_coordinates,hm]
  exact (h.vertex x).map.map_zero

 theorem bottEndOfSheaf_preserves_support (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (x : Interval cs 1 (cs.wordProd l)) (m : BottSamelsonModule cs l)
    (hm : m ∈ bottWeightSupported cs l x.val) :
    bottEndOfSheaf cs basis l hl h m ∈ bottWeightSupported cs l x.val := by
  intro e he
  let y : Interval cs 1 (cs.wordProd l) :=
    ⟨bottWeight cs l e,one_bruhat cs _,bottWeight_bruhat cs l hl e⟩
  have hmy : bottStalkProjection cs l y.val m=0 := by
    apply Subtype.ext
    funext f
    exact hm f.val (fun hx => he (f.property.symm.trans hx))
  have hfy := bottEndOfSheaf_preserves_kernel cs basis l hl h y m hmy
  exact congrFun (congrArg Subtype.val hfy) ⟨e,rfl⟩

end
end KLInvariance.TitsSpace

end


section

/-! The adjoint of an actual graded word-sheaf endomorphism is again an
integral graded word-sheaf endomorphism. No stalk freeness or BMP character
is used or asserted. This supplies the correct adjoint route for a future
BMP summand, instead of restricting a form to an arbitrary summand. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

 def bottAdjointWordHom (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    ModuleData.Hom (bottWordData cs basis l) (bottWordData cs basis l) where
  map := bottAdjoint cs l (bottEndOfSheaf cs basis l hl h)
  graded := bottAdjoint_homogeneous cs basis l _
    (bottEndOfSheaf_homogeneous cs basis l hl h)

 theorem bottAdjointWordHom_kernel (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (x : Interval cs 1 (cs.wordProd l)) (m : BottSamelsonModule cs l)
    (hm : bottStalkProjection cs l x.val m=0) :
    bottStalkProjection cs l x.val ((bottAdjointWordHom cs basis l hl h).map m)=0 :=
  bottAdjoint_preserves_kernel cs l x.val _
    (bottEndOfSheaf_preserves_support cs basis l hl h x) m hm

 def bottAdjointSheaf (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)) where
  vertex x := ModuleData.descended (bottAdjointWordHom cs basis l hl h)
    (bottStalkHom cs basis l x.val) (bottStalkHom_surjective cs basis l x.val)
    (bottAdjointWordHom_kernel cs basis l hl h x)
  edge e := ModuleData.descendedEdge (bottAdjointWordHom cs basis l hl h)
    (bottStalkHom cs basis l (source cs 1 (cs.wordProd l) e).val)
    (bottStalkHom cs basis l (target cs 1 (cs.wordProd l) e).val)
    (bottStalkHom_surjective cs basis l _)
    (bottStalkHom_surjective cs basis l _)
    (bottAdjointWordHom_kernel cs basis l hl h _)
    (bottAdjointWordHom_kernel cs basis l hl h _)
  lower _ x := ModuleData.descendedEdge_lower _ _ _ _ _ _ _ x
  upper _ y := ModuleData.descendedEdge_upper _ _ _ _ _ _ _ y

 theorem bottAdjointSheaf_vertex (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (x : Interval cs 1 (cs.wordProd l)) (m : BottSamelsonModule cs l) :
    ((bottAdjointSheaf cs basis l hl h).vertex x).map (bottStalkProjection cs l x.val m)=
      bottStalkProjection cs l x.val (bottAdjoint cs l (bottEndOfSheaf cs basis l hl h) m) :=
  LinearDescent.descend_apply _ _ _ _ m

 theorem bottEndOfAdjointSheaf (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    bottEndOfSheaf cs basis l hl (bottAdjointSheaf cs basis l hl h)=
      bottAdjoint cs l (bottEndOfSheaf cs basis l hl h) := by
  apply LinearMap.ext
  intro m
  apply bottVertexProjection_injective cs l hl
  funext x
  exact (bottEndOfSheaf_coordinates cs basis l hl _ m x).trans
    (bottAdjointSheaf_vertex cs basis l hl h x m)

end
end KLInvariance.TitsSpace

end


section

/-! Integral graded adjoint WORD projectors. The assumption below is only
that the GIVEN endomorphism is a projector; no existence of a BMP projector
or identification of its image with its adjoint is asserted. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottAdjointSheaf_twice_vertex (x : Interval cs 1 (cs.wordProd l))
    (v : bottStalk cs l x.val) :
    ((bottAdjointSheaf cs basis l hl (bottAdjointSheaf cs basis l hl h)).vertex x).map v=
      (h.vertex x).map v := by
  obtain ⟨m,rfl⟩ := bottStalkProjection_surjective cs l x.val v
  rw [bottAdjointSheaf_vertex,bottEndOfAdjointSheaf]
  change bottStalkProjection cs l x.val
    (PerfectAdjoint.adjoint (bottSamelsonDuality cs l)
      (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) (bottEndOfSheaf cs basis l hl h)) m)=_
  rw [PerfectAdjoint.adjoint_adjoint _ (bottSamelson_symmetric cs l)]
  exact bottEndOfSheaf_coordinates cs basis l hl h m x

end
end KLInvariance.TitsSpace

end


section

/-! Correct integral graded duality for a GIVEN word-sheaf summand: the dual
is realized by its ADJOINT image, not identified with the original summand.
The existence and BMP recognition of that summand remain separate. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : GradedSheaf (𝓐 := symmetricGrading basis) (graph cs 1 (cs.wordProd l)))
  (s : GradedSheaf.SplitIn B (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 def bottSplitAdjointSheaf : GradedSheaf (𝓐 := symmetricGrading basis)
    (graph cs 1 (cs.wordProd l)) :=
  bottImageSheaf cs basis l (bottAdjointSheaf cs basis l hl s.projector)

end
end KLInvariance.TitsSpace

end


section

/-! Integral anti-involution on the actual graded word-sheaf endomorphisms.
This is the algebra required to compare an indecomposable BMP summand to
its adjoint, not an assertion that such a summand is already recognized. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

 theorem bottEndOfSheaf_comp
    (h g : GradedSheaf.Hom
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    bottEndOfSheaf cs basis l hl (h.comp g)=
      (bottEndOfSheaf cs basis l hl h).comp (bottEndOfSheaf cs basis l hl g) := by
  apply LinearMap.ext
  intro m
  apply bottVertexProjection_injective cs l hl
  funext x
  exact (bottEndOfSheaf_coordinates cs basis l hl (h.comp g) m x).trans
    ((congrArg (h.vertex x).map (bottEndOfSheaf_coordinates cs basis l hl g m x)).symm.trans
      (bottEndOfSheaf_coordinates cs basis l hl h (bottEndOfSheaf cs basis l hl g m) x).symm)

 theorem bottAdjointSheaf_comp
    (h g : GradedSheaf.Hom
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    bottAdjointSheaf cs basis l hl (h.comp g)=
      (bottAdjointSheaf cs basis l hl g).comp (bottAdjointSheaf cs basis l hl h) := by
  apply GradedSheaf.Hom.eq_of_vertex
  · exact fun e => bottProjectionSheaf_lower_surjective cs l 1 (cs.wordProd l) e
  · intro x v
    have hs : Function.Surjective (bottStalkProjection cs l x.val) :=
      bottStalkProjection_surjective cs l x.val
    obtain ⟨m,rfl⟩ := hs v
    change ((bottAdjointSheaf cs basis l hl (h.comp g)).vertex x).map
      (bottStalkProjection cs l x.val m)=
        ((bottAdjointSheaf cs basis l hl g).vertex x).map
          (((bottAdjointSheaf cs basis l hl h).vertex x).map (bottStalkProjection cs l x.val m))
    simp only [bottAdjointSheaf_vertex]
    change bottStalkProjection cs l x.val
      (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) (bottEndOfSheaf cs basis l hl (h.comp g)) m)=
      bottStalkProjection cs l x.val
        (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) (bottEndOfSheaf cs basis l hl g)
          (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) (bottEndOfSheaf cs basis l hl h) m))
    rw [bottEndOfSheaf_comp,PerfectAdjoint.adjoint_comp]
    rfl

 theorem bottAdjointSheaf_involutive : Function.Involutive (bottAdjointSheaf cs basis l hl) := by
  intro h
  apply GradedSheaf.Hom.eq_of_vertex
  · exact fun e => bottProjectionSheaf_lower_surjective cs l 1 (cs.wordProd l) e
  · exact bottAdjointSheaf_twice_vertex cs basis l hl h

end
end KLInvariance.TitsSpace

end


section


namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

 theorem bottEndOfSheaf_zero :
    bottEndOfSheaf cs basis l hl GradedSheaf.Hom.zero=0 := by
  apply LinearMap.ext
  intro m
  apply bottVertexProjection_injective cs l hl
  funext x
  change bottStalkProjection cs l x.val _=bottStalkProjection cs l x.val 0
  rw [map_zero]
  exact bottEndOfSheaf_coordinates cs basis l hl GradedSheaf.Hom.zero m x

 theorem bottAdjointSheaf_zero :
    bottAdjointSheaf cs basis l hl GradedSheaf.Hom.zero=GradedSheaf.Hom.zero := by
  apply GradedSheaf.Hom.eq_of_vertex
  · exact fun e => bottProjectionSheaf_lower_surjective cs l 1 (cs.wordProd l) e
  · intro x v
    have hs : Function.Surjective (bottStalkProjection cs l x.val) :=
      bottStalkProjection_surjective cs l x.val
    obtain ⟨m,rfl⟩ := hs v
    change ((bottAdjointSheaf cs basis l hl GradedSheaf.Hom.zero).vertex x).map
      (bottStalkProjection cs l x.val m)=0
    rw [bottAdjointSheaf_vertex,bottEndOfSheaf_zero]
    change bottStalkProjection cs l x.val
      (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) 0 m)=0
    rw [PerfectAdjoint.adjoint_zero]
    exact map_zero _

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Support
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded unit splittings, integral support and balanced cuts, and boundary-sheaf support and recognition.
-/


section

/-! Positive triangular decomposition of the honest word's character into
actual BMP stalk characters. The KL identification is not assumed. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottPolynomialSheaf_quotient (l : List I) (u b : W) :
    (bottPolynomialSheaf cs basis l u b).UpperQuotient (polynomialLabel cs u b basis) :=
  GradedSheaf.coefficientChange_upperQuotient _ _ _ _
    (bottGradedProjectionSheaf_upperQuotient cs basis l u b)

end
end KLInvariance.TitsSpace

end


end OAI
end


