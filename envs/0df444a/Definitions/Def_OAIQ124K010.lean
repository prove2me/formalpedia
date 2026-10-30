-- Prove2me | Definitions.Def_OAIQ124K010
-- name    : OAIQ124K010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:48:21.712432+00:00
-- url     : https://prove2.me/theorems/91863188-598b-45aa-a963-28722d1200bf
-- title:
--   Definitions bundle OAIQ124K010 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 9 definitions, 1 inductive type or structure and 21 theorems. The definitions and types are `OAI.KLInvariance.BruhatGraph.boundaryFreeSheaf`, `OAI.KLInvariance.BruhatGraph.lowerIdealGraph`, `OAI.KLInvariance.BruhatGraph.lowerIntervalBoundary`, `OAI.KLInvariance.BruhatGraph.lowerIntervalMap`, `OAI.KLInvariance.MomentGraph.GradedSheaf.BoundaryModels`, `OAI.KLInvariance.MomentGraph.Sheaf.modelProduct`, `OAI.KLInvariance.TitsSpace.bottAdjoint`, `OAI.KLInvariance.TitsSpace.bottSamelsonDuality`, `OAI.KLInvariance.TitsSpace.bottSeed`, `OAI.KLInvariance.TitsSpace.bottTensorEnd`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BalancedPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BalancedPairings.lean), [`KazhdanLusztig_CharacterReciprocity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/CharacterReciprocity.lean), [`KazhdanLusztig_DihedralIntervals`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/DihedralIntervals.lean), [`KazhdanLusztig_EdgeLocalization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/EdgeLocalization.lean), [`KazhdanLusztig_Frobenius`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Frobenius.lean), [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean), [`KazhdanLusztig_MinimalExtensions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/MinimalExtensions.lean), [`KazhdanLusztig_SheafMorphisms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/SheafMorphisms.lean), [`KazhdanLusztig_TerminalKernels`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/TerminalKernels.lean).
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K004`, `OAIQ124K005` and `OAIQ124K006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K013`, `OAIQ124K014` and `OAIQ124K015`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K004
import Definitions.Def_OAIQ124K005
import Definitions.Def_OAIQ124K006

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_MinimalExtensions
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.pi_free _root_.OAI.KLInvariance.Graded.ModuleData.prod_free _root_.OAI.KLInvariance.Graded.ModuleData.shift_free
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Minimal-boundary extension sheaves, graded splittings and sheaf decomposition.
-/


section

/-! Extension by zero from a full lower ideal. Proof-indexed finite products
avoid informal identifications of the integral stalks at boundary vertices. -/
namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  (G : OrderedGraph V E) (K : Set V) (hK : IsLowerSet K)

namespace GradedSheaf
noncomputable section
attribute [local instance] Classical.propDecidable

variable {G K hK} (B : GradedSheaf (𝓐 := 𝓐) (lowerGraph G K hK))

 theorem lowerExtend_flabby (hb : B.forget.Flabby) : B.lowerExtend.forget.Flabby := by
  intro U hU f hf
  have hu : IsUpperSet (Subtype.val ⁻¹' U : Set K) := fun _ _ hab ha => hU hab ha
  obtain ⟨g,hg,hgf⟩ := hb (Subtype.val ⁻¹' U) hu (B.projectLowerAssignment f) (B.projectLower_compatible hf)
  refine ⟨B.liftLowerAssignment g,B.liftLower_compatible hg,?_⟩
  intro x hx
  funext h
  exact hgf ⟨x,h.down.down⟩ hx

end
end GradedSheaf
end KLInvariance.MomentGraph

end


section

/-! Finite sums of honest shifted normalized boundary models. A model family
is data for the decomposition lemma, not an assumption of the KL main. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}

structure BoundaryModels (α : E → A) where
  sheaf : V → GradedSheaf (𝓐 := 𝓐) G
  free : ∀ c x, Module.Free A ((sheaf c).vertex x)
  quotient : ∀ c, (sheaf c).UpperQuotient α
  generated : ∀ c, (sheaf c).forget.Generated
  flabby : ∀ c, (sheaf c).forget.Flabby
  support : ∀ c x, ¬x ≤ c → Subsingleton ((sheaf c).vertex x)
  top : ∀ c, (sheaf c).vertex c ≃ₗ[A] ModuleData.unit.{uk,ua,um} hneg
  top_graded : ∀ c n v, v ∈ ((sheaf c).vertex c).piece n → top c v ∈ (ModuleData.unit.{uk,ua,um} hneg).piece n
  minimal : ∀ c x, x ≠ c → (sheaf c).KernelMinimal x

end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue uw uf um
variable {R : Type ur} [CommRing R]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  {W : Type uw} [PartialOrder W] {F : Type uf} {H : OrderedGraph W F}
  (B : Sheaf.{ur,uw,uf,um} (R := R) H) (f : GraphMap G H)
noncomputable section

 theorem stalkMap_assignment (s : B.Assignment) (x : W) (e : Outgoing (G := H) x) :
    B.stalkMap x (s x) e = B.lower e.val (s (H.source e.val)) := by
  rcases e with ⟨e,he⟩
  subst x
  rfl

end
end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SheafMorphisms
attribute [-instance] _root_.OAI.KLInvariance.TitsSpace.simpleFixed_finite _root_.OAI.KLInvariance.TitsSpace.simpleFixed_free
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded sheaf morphisms, exact section constructions and character sums.
-/

section

namespace KLInvariance.Graded
open Polynomial
universe uk us um ui

attribute [instance] NonnegativeBasis.finite

end KLInvariance.Graded

end


section

/-! Every lower-supported model is an actual Bruhat BMP sheaf on [1,c],
pulled back by the genuine lower-interval graph isomorphism and extended by
zero. Thus its stalk character is not an abstract model selected for convenience. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 local instance instDecidable_solutions_rd386af_1 (p : Prop) : Decidable p := Classical.propDecidable p
abbrev lowerIdealGraph (c : Interval cs 1 b) :=
  lowerGraph (graph cs 1 b) (Set.Iic c) (isLowerSet_Iic c)

 def lowerIntervalMap (c : Interval cs 1 b) :
    GraphMap (lowerIdealGraph cs b c) (graph cs 1 c.val) where
  vertex x := ⟨x.val.val,x.val.property.1,x.property⟩
  edge e := ⟨(⟨(source cs 1 b e.val).val,(source cs 1 b e.val).property.1,
      bruhat_trans cs (.single e.val.property) e.property⟩,
    ⟨(target cs 1 b e.val).val,(target cs 1 b e.val).property.1,e.property⟩),e.val.property⟩
  source _ := rfl
  target _ := rfl

 omit [Fintype I] in
 theorem lowerIntervalMap_injective (c : Interval cs 1 b) :
    Function.Injective (lowerIntervalMap cs b c).vertex := by
  intro x y h
  exact Subtype.ext (Subtype.ext (show x.val.val=y.val.val from
    congrArg (fun z : Interval cs 1 c.val => z.val) h))

 omit [Fintype I] in
 theorem lowerIntervalMap_outgoing (c : Interval cs 1 b)
    (e : Edge cs 1 c.val) (x : Set.Iic c)
    (hx : (lowerIntervalMap cs b c).vertex x=source cs 1 c.val e) :
    ∃ a, (lowerIntervalMap cs b c).edge a=e ∧ (lowerIdealGraph cs b c).source a=x := by
  have hxx := congrArg Subtype.val hx
  let y : Interval cs 1 b := ⟨(target cs 1 c.val e).val,(target cs 1 c.val e).property.1,
    bruhat_trans cs (target cs 1 c.val e).property.2 c.property.2⟩
  let a : Edge cs 1 b := ⟨(x.val,y),hxx.symm ▸ e.property⟩
  refine ⟨⟨a,(target cs 1 c.val e).property.2⟩,?_,?_⟩
  · apply Subtype.ext
    exact Prod.ext hx rfl
  · rfl

 def lowerIntervalBoundary (c : Interval cs 1 b) :
    BoundarySheaf (polynomialGrading_negative ℝ σ) (lowerIdealGraph cs b c)
      (fun e => polynomialLabel cs 1 b basis e.val) ⟨c,Set.mem_Iic.mpr le_rfl⟩ :=
  (boundarySheaf cs 1 c.val basis (one_bruhat cs c.val)).pullback
    (lowerIntervalMap cs b c) (lowerIntervalMap_injective cs b c)
    (lowerIntervalMap_outgoing cs b c) ⟨c,Set.mem_Iic.mpr le_rfl⟩ rfl

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Frobenius
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

/-! Genuine tensor-defined Bott--Samelson bimodules for the extended real
Coxeter realization. The perfect pairing is integral and balanced. This
construction alone does not identify indecomposable BMP summands or prove
the Elias--Williamson character theorem. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottSamelsonDuality (l : List I) : BottSamelsonModule cs l ≃ₗ[SymmetricCoefficient (M := M)]
    Dual (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l) :=
  (bottSamelson cs l).obj.pairing

 theorem bottSamelson_symmetric (l : List I) (m n : BottSamelsonModule cs l) :
    bottSamelsonDuality cs l m n = bottSamelsonDuality cs l n m :=
  (bottSamelson cs l).symmetric m n

end
end KLInvariance.TitsSpace

end


section

/-! A grading defined by an actual homogeneous free basis, with an explicit
coefficient test. Used to put the genuine grading on tensor Bott--Samelsons. -/
namespace KLInvariance.Graded
open Module
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐]
  [SetLike.GradedMonoid 𝓐]
  {N : Type um} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  {ι : Type ui} [Fintype ι] (b : Basis ι A N) (d : ι → ℤ)
noncomputable section

omit [DirectSum.Decomposition 𝓐] in
 theorem pairing_homogeneous (p : N →ₗ[A] Dual A N) (l : ℤ)
    (hp : ∀ i j, p (b i) (b j) ∈ 𝓐 (d i+d j-l))
    {n m : ℤ} {x y : N} (hx : x ∈ basisPiece 𝓐 b d n)
    (hy : y ∈ basisPiece 𝓐 b d m) : p x y ∈ 𝓐 (n+m-l) := by
  classical
  have hexp : p x y = ∑ i, ∑ j,
      b.repr x i * b.repr y j * p (b i) (b j) := by
    conv_lhs => rw [← b.sum_repr x,← b.sum_repr y]
    simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,
      Finset.mul_sum,mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexp]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  change ∀ i, b.repr x i ∈ 𝓐 (n-d i) at hx
  change ∀ i, b.repr y i ∈ 𝓐 (m-d i) at hy
  have h := SetLike.GradedMul.mul_mem
    (SetLike.GradedMul.mul_mem (hx i) (hy j)) (hp i j)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  omega

end
end KLInvariance.Graded

end


section

/-! Faithfulness of the actual polynomial action; distinct Coxeter weights
have distinct integral polynomial characters. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem symmetricCoefficient_ι_injective :
    Function.Injective (SymmetricAlgebra.ι ℝ (Extended M)) := by
  intro x y h
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℝ (x-y)).mp
  intro f
  rw [map_sub]
  apply sub_eq_zero.mpr
  have he := congrArg (SymmetricAlgebra.lift f) h
  simpa only [SymmetricAlgebra.lift_ι_apply] using he

 theorem coefficientAction_injective : Function.Injective (coefficientAction cs) := by
  intro x y h
  apply extendedAction_injective M cs
  apply LinearEquiv.ext
  intro v
  apply symmetricCoefficient_ι_injective (M := M)
  have he := congrArg (fun g : SymmetricCoefficient (M := M) ≃ₐ[ℝ]
    SymmetricCoefficient (M := M) => g (SymmetricAlgebra.ι ℝ (Extended M) v)) h
  simpa only [coefficientAction_ι] using he

 theorem coefficientAction_separates {x y : W} (hxy : x ≠ y) :
    ∃ a : SymmetricCoefficient (M := M), coefficientAction cs x a ≠ coefficientAction cs y a := by
  by_contra! h
  apply hxy
  apply coefficientAction_injective cs
  exact AlgEquiv.ext h

end
end KLInvariance.TitsSpace

end


end OAI
end

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

/-! Range-valued projections to sets of coordinates and their natural
surjective restriction maps. -/
namespace KLInvariance.CoordinateProjection
universe ur un uv ux
variable {R : Type ur} [CommRing R] {N : Type un} [AddCommGroup N] [Module R N]
  {V : Type uv} {X : V → Type ux} [∀ x, AddCommGroup (X x)] [∀ x, Module R (X x)]
  (f : ∀ x, N →ₗ[R] X x)
noncomputable section

 theorem project_zero_iff (U : Set V) (n : N) : project f U n=0 ↔ ∀ x∈U, f x n=0 := by
  constructor
  · intro h x hx
    exact congrArg (fun z : image f U => z.val ⟨x,hx⟩) h
  · intro h
    apply Subtype.ext
    funext x
    exact h x.val x.property

 theorem restrict_surjective {U K : Set V} (h : U⊆K) : Function.Surjective (restrict f h) := by
  intro z
  obtain ⟨n,rfl⟩ := project_surjective f U z
  exact ⟨project f K n,rfl⟩

end
end KLInvariance.CoordinateProjection

end


section

/-! Upper sets and actual finite-word projection predicates. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection
universe u v
variable {I : Type u} [klPreservedInstance11 : Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 omit [Fintype I] in
 theorem BruhatUpper.mem_simpleUnion (U : Set W) (hU : BruhatUpper cs U) (i : I) (x : W) :
    x∈simpleUnion cs i U ↔ upperSimple cs i x∈U := by
  constructor
  · rintro (hx|hx)
    · exact hU (le_upperSimple cs i x) hx
    · have hh := hU (le_upperSimple cs i (cs.simple i*x)) hx
      simpa only [upperSimple_mul] using hh
  · intro hx
    classical
    unfold upperSimple at hx
    split_ifs at hx with h
    · exact Or.inl hx
    · exact Or.inr hx

include klPreservedInstance11 in
 theorem BruhatUpper.simpleUnion (U : Set W) (hU : BruhatUpper cs U) (i : I) :
    BruhatUpper cs (simpleUnion cs i U) := by
  have _ := klPreservedInstance11
  intro x y hxy hx
  exact (hU.mem_simpleUnion cs U i y).mpr
    (hU (upperSimple_mono cs i hxy) ((hU.mem_simpleUnion cs U i x).mp hx))

 omit [Fintype I] in
 theorem cross_edge_is_simple (U : Set W) (hU : BruhatUpper cs U) (i : I)
    {x y : W} (hxy : BruhatStep cs x y) (hsx : cs.simple i*x∈U)
    (hsy : cs.simple i*y∉U) : y=cs.simple i*x := by
  by_contra he
  exact hsy (hU (.single (bruhatStep_simple_mul cs hxy i he)) hsx)

end
end KLInvariance.TitsSpace

end


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

 def bottTensorEnd (i : I) (l : List I)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l)) :
    Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs (i::l)) :=
  AlgebraTensorModule.map (LinearMap.id : SymmetricCoefficient (M := M) →ₗ[
    SymmetricCoefficient (M := M)] SymmetricCoefficient (M := M)) (e.restrictScalars (simpleFixed cs i))

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

 def bottSeed (i : I) (l : List I) (n : BottSamelsonModule cs l) :
    BottSamelsonModule cs (i::l) := (1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance
universe ur um uh up us
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {H : Type uh} [AddCommGroup H] [Module R H]
  {P : Type up} [AddCommGroup P] [Module R P]
  {S : Type us} [AddCommGroup S] [Module R S]

namespace CoordinateProjection
universe uv ux
variable {V : Type uv} {X : V → Type ux} [∀ x, AddCommGroup (X x)] [∀ x, Module R (X x)]
  (f : ∀ x, M →ₗ[R] X x)
 theorem restrict_joint_injective {U V' K : Set V} (hU : U⊆K) (hV : V'⊆K)
    (hc : ∀ x∈K, x∈U ∨ x∈V') :
    Function.Injective ((restrict f hU).prod (restrict f hV)) := by
  intro p q h
  apply Subtype.ext
  funext x
  rcases hc x.val x.property with hx|hx
  · exact congrArg (fun z : image f U => z.val ⟨x.val,hx⟩) (congrArg Prod.fst h)
  · exact congrArg (fun z : image f V' => z.val ⟨x.val,hx⟩) (congrArg Prod.snd h)
end CoordinateProjection
end KLInvariance

end


section

/-! The codimension-one two-character distinction needed for integral
Bott--Samelson section realization. No BMP character or pairing is assumed. -/
namespace KLInvariance.Realization
open Module
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

 theorem orthogonal_eq_id_or_rootReflection
    (B : LinearMap.BilinForm ℝ V) (a : V) (ha : B a a=2)
    (g : V ≃ₗ[ℝ] V) (hg : ∀ v w, B (g v) (g w)=B v w)
    (hline : ∀ v, g v-v ∈ Submodule.span ℝ {a}) :
    g.toLinearMap=LinearMap.id ∨ ∀ v, g v=Module.preReflection a (B a) v := by
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp (hline a)
  have hga : g a=(1+r) • a := by rw [add_smul,one_smul,hr]; module
  have hn := hg a a
  rw [hga] at hn
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,ha] at hn
  have hr0 : r*(r+2)=0 := by nlinarith
  rcases mul_eq_zero.mp hr0 with hr | hr
  · left
    have hga' : g a=a := by simpa only [hr,add_zero,one_smul] using hga
    ext v
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hline v)
    have hgv : g v=v+c • a := by rw [hc]; module
    have h := hg a v
    rw [hga',hgv] at h
    simp only [map_add,map_smul,ha,smul_eq_mul] at h
    have hc0 : c=0 := by linarith
    change g v=v
    simpa only [hc0,zero_smul,add_zero] using hgv
  · right
    have hr' : r= -2 := by linarith
    have hga' : g a= -a := by simpa only [hr',show (1:ℝ)+ -2= -1 by norm_num,neg_one_smul] using hga
    intro v
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hline v)
    have hgv : g v=v+c • a := by rw [hc]; module
    have h := hg a v
    rw [hga',hgv] at h
    simp only [map_neg,LinearMap.neg_apply,map_add,map_smul,ha,smul_eq_mul] at h
    have hc' : c= -(B a v) := by linarith
    rw [hgv,hc',Module.preReflection_apply,neg_smul,sub_eq_add_neg]

end KLInvariance.Realization

end


section

/-! Flabbiness of the genuine interval word sheaf; the extension outside the
finite support is zero, not an extra assumption on the source interval. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 omit [Fintype I] in
 theorem intervalUpperClosure_upper (b : W) (U : Set (Interval cs 1 b)) :
    BruhatUpper cs (intervalUpperClosure cs b U) := by
  rintro x y hxy ⟨a,ha,hax⟩
  exact ⟨a,ha,bruhat_trans cs hax hxy⟩

 omit [Fintype I] in
 theorem intervalUpperClosure_member (b : W) (U : Set (Interval cs 1 b)) (hU : IsUpperSet U)
    (x : W) (hx : x∈intervalUpperClosure cs b U) (hxb : BruhatLE cs x b) :
    (⟨x,one_bruhat cs x,hxb⟩ : Interval cs 1 b)∈U := by
  obtain ⟨a,ha,hax⟩ := hx
  exact hU hax ha

end
end KLInvariance.TitsSpace

end


section


namespace KLInvariance.Graded
open Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
noncomputable section

omit [IsScalarTower k A M] in
 theorem perfect_inverse_of_homogeneous_functional
    (p : M ≃ₗ[A] Dual A M) (l : ℤ)
    (hp : ∀ i j (m n : M), m ∈ 𝓜 i → n ∈ 𝓜 j → p m n ∈ 𝓐 (i+j-l))
    (r : ℤ) (lam : Dual A M)
    (hlam : ∀ j (n : M), n ∈ 𝓜 j → lam n ∈ 𝓐 (j+r)) :
    p.symm lam ∈ 𝓜 (r+l) := by
  have hc : component 𝓜 (r+l) (p.symm lam) = p.symm lam := by
    apply p.injective
    apply LinearMap.ext
    intro y
    refine DirectSum.Decomposition.inductionOn 𝓜 ?_ ?_ ?_ y
    · simp
    · intro j v
      let f : M →ₗ[A] A :=
        { toFun := fun w => p w (v : M)
          map_add' := by intros; simp
          map_smul' := by intros; simp }
      have hh : ∀ i w, w ∈ 𝓜 i → f w ∈ 𝓐 (i+(j-l)) := by
        intro i w hw
        simpa only [f,LinearMap.coe_mk,AddHom.coe_mk,add_sub_assoc] using hp i j w v hw v.property
      have he := map_component 𝓜 𝓐 f (j-l) hh (j+r) (p.symm lam)
      have hi : j+r-(j-l)=r+l := by omega
      rw [hi] at he
      have hf : f (p.symm lam)=lam v := by
        dsimp only [f,LinearMap.coe_mk,AddHom.coe_mk]
        rw [LinearEquiv.apply_symm_apply]
      rw [hf] at he
      have hsame : component 𝓐 (j+r) (lam v)=lam v :=
        DirectSum.decompose_of_mem_same 𝓐 (hlam j v v.property)
      rw [hsame] at he
      change f (component 𝓜 (r+l) (p.symm lam)) = p (p.symm lam) v
      rw [LinearEquiv.apply_symm_apply]
      exact he.symm
    · intro x y hx hy
      simp only [map_add,hx,hy]
  rw [← hc]
  exact (DirectSum.decompose 𝓜 (p.symm lam) (r+l)).property

end
end KLInvariance.Graded

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

/-! The actual word adjoint preserves homogeneity. Projection kernels are
annihilators of the actual supported lattices, integrally, with no localization
or freeness assumption on the projection lattice. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottAdjoint (l : List I) (f : End (SymmetricCoefficient (M := M))
    (BottSamelsonModule cs l)) := PerfectAdjoint.adjoint (bottSamelsonDuality cs l) f

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CharacterReciprocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Conditional boundary-sheaf duality and stalk-character propositions, free sheaves, actual R-reciprocity and lower convolution. StalkCharacterObligation remains a Prop, not an unconditional character theorem or a premise of the R-first route.
-/


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.finiteInterval
attribute [local instance] OAI.KLInvariance.BruhatGraph.finiteEdges
attribute [local instance] OAI.KLInvariance.BruhatGraph.charDecEqC
def boundaryFreeSheaf : FreeSheaf cs 1 b basis where
  sheaf := (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf
  free := (boundarySheaf cs 1 b basis (one_bruhat cs b)).free
  quotient := (boundarySheaf cs 1 b basis (one_bruhat cs b)).quotient
  generated := (boundarySheaf cs 1 b basis (one_bruhat cs b)).generated

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DihedralIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Signed dihedral coordinates, actual dihedral intervals, exact later-edge counts and root-plane calculations.
-/


section

/-! An elementary flabbiness criterion for the exact rank-one model. Flow-down
sections with the genuine product of outgoing labels suffice. The pairwise
relative-primality condition will be instantiated by actual root labels. -/
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] [DecompositionMonoid R]
  {V : Type uv} [PartialOrder V] {E : Type ue}
  (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section
variable [Fintype E] [DecidableEq V]

def modelProduct (x : V) : R := ∏ e ∈ modelOutgoing G c x, α e

end
end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_EdgeLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bruhat sheaf localization, graded transport, local edge-image bounds and support.
-/


section

/-! A specified morphism between honest minimal free covers is an isomorphism
if it covers the identity. This will recognize the canonical restricted word
form, not merely an arbitrary choice of self-duality. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {T : ModuleData.{uk,ua,um} 𝓐}

include hneg hzero in
 theorem MinimalCover.hom_bijective (C D : MinimalCover T)
    (f : Hom C.source D.source) (hf : D.hom.map.comp f.map=C.hom.map) :
    Function.Bijective f.map := by
  let := C.free
  let := D.free
  obtain ⟨g,hg⟩ := exists_hom_lift hneg hzero C.hom C.surjective D.hom
  have hfa (v : C.source) : D.hom.map (f.map v)=C.hom.map v := LinearMap.congr_fun hf v
  have hga (v : D.source) : C.hom.map (g.map v)=D.hom.map v := LinearMap.congr_fun hg v
  have hgf : Function.Bijective (g.comp f).map := by
    apply Hom.bijective_of_mod_positive
    intro m
    apply C.minimal
    change C.hom.map (m-g.map (f.map m))=0
    rw [map_sub,hga,hfa,sub_self]
  have hfg : Function.Bijective (f.comp g).map := by
    apply Hom.bijective_of_mod_positive
    intro m
    apply D.minimal
    change D.hom.map (m-f.map (g.map m))=0
    rw [map_sub,hfa,hga,sub_self]
  exact ⟨Function.Injective.of_comp hgf.1,Function.Surjective.of_comp hfg.2⟩

end KLInvariance.Graded.ModuleData

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_TerminalKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
All-section transport, terminal kernels, scalar quotients, height-one membership in free targets and scaled edge-image inclusion.
-/


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

omit [Fintype σ] in
 theorem edgeModule_tower (e : Edge cs u b) :
    let _ := edgeModule cs u b basis hub B e
    IsScalarTower (MvPolynomial σ ℝ) (EdgeRing cs basis (root cs u b e)) (B.sheaf.edge e) := by
   dsimp only [edgeModule,Module.IsTorsionBy.module]
   exact Module.IsTorsionBySet.isScalarTower _

end
end KLInvariance.BruhatGraph

end


end OAI
end


