-- Prove2me | Definitions.Def_OAIQ66So029
-- name    : OAIQ66So029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:44:03.748869+00:00
-- url     : https://prove2.me/theorems/8473ddaa-111d-401e-8bed-2d30669578ea
-- title:
--   Definitions bundle OAIQ66So029 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 10 definitions and 8 theorems. The definitions and types are `OAI.SourceCorner.unitEmbedding`, `OAI.SteinChains.Complex.tupleModule`, `OAI.SteinChains.backHomotopy`, `OAI.SteinChains.bary`, `OAI.SteinChains.barySelect`, `OAI.SteinChains.simplexFace`, `OAI.SteinChains.unionFace`, `OAI.TwistedBrin.BrickSwap.elem`, `OAI.TwistedBrin.SimplicityProducer.KillsBrick`, `OAI.TwistedBrin.Stationary`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`FiniteType_OrderListChainsBased`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/OrderListChainsBased.lean), [`FiniteType_SourceCorner`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/SourceCorner.lean), [`FiniteType_SteinbergSixThree`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/SteinbergSixThree.lean), [`FiniteType_TwistedBrin`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrin.lean), [`FiniteType_TwistedBrinEquiv`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrinEquiv.lean), [`FiniteType_TwistedBrinRangeChartRestricts`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrinRangeChartRestricts.lean), [`FiniteType_TwistedBrinSeparated`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrinSeparated.lean).
--
--   **Imports.** It imports the bundles `OAIQ66So025` and `OAIQ66So026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So030` and `OAIQ66So031`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So025
import Definitions.Def_OAIQ66So026

section
-- module Solutions.OAIQ066_SO.FiniteType_SteinbergSixThree
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace Steinberg
variable {R : Type*} [Ring R]

lemma units_comp {S T : Type*} [Ring S] [Ring T]
    (ψ : S →ₙ+* T) (φ : R →ₙ+* S) (v : Rˣ) :
    NonunitalCompression.units ψ (NonunitalCompression.units φ v)=
      NonunitalCompression.units (ψ.comp φ) v := by
  apply Units.ext
  simp

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SourceCorner
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
namespace SourceCorner
variable {R : Type} [Ring R] {e : R} (he : IsIdempotentElem e)

def unitEmbedding : he.Cornerˣ →* Rˣ := NonunitalCompression.units (val he)
end SourceCorner

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrin
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Basis.vertexPermutationHom_ker_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

namespace Basis

lemma refines_trans {B C D : Basis ρ} (hBC : Refines ρ B C) (hCD : Refines ρ C D) :
    Refines ρ B D := by
  intro d
  obtain ⟨c,hc⟩ := hCD d
  obtain ⟨b,hb⟩ := hBC c
  exact ⟨b,GermBrick.restricts_trans ρ hc hb⟩

end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChainsBased
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.OrderChainComplex.instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise

namespace SteinChains
section
open OrderListChains
variable (V : Type*)
noncomputable def simplexFace (s : Simplex V) : Face V :=
  ⟨finiteVertices V s,finiteVertices_nonempty V s⟩

noncomputable def bary : Chain V →ₗ[ℤ] Chain (Face V) :=
  OrderBasedComplex.extend (based V) (boundary (Face V)) (augmentation (Face V))
    (fun s => contraction (Face V) (simplexFace V s))

noncomputable def unionFace (s : Simplex (Face V)) : Face V := by
  classical
  refine ⟨(finiteVertices (Face V) s).biUnion Subtype.val,?_⟩
  obtain ⟨v,hv⟩ := s.1.property
  exact ⟨v,Finset.mem_biUnion.mpr ⟨s.1,(mem_finiteVertices _ s _).mpr (head_mem_vertices _ _),hv⟩⟩

noncomputable def barySelect : Chain (Face V) →ₗ[ℤ] Chain (Face V) := (bary V).comp (select V)

noncomputable def backHomotopy : Chain (Face V) →ₗ[ℤ] Chain (Face V) :=
  OrderBasedComplex.homotopy (based (Face V)) (boundary (Face V)) (augmentation (Face V))
    (fun s => contraction (Face V) (unionFace V s)) LinearMap.id (barySelect V)

end

open OrderListChains
variable (V : Type*)

namespace Complex
variable (K : Complex V)
def tupleModule : Submodule ℤ (Chain V) :=
  Finsupp.supported ℤ ℤ {s | finiteVertices V s ∈ K.faces}
end Complex

end SteinChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinRangeChartRestricts
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Basis.vertexPermutationHom_ker_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

lemma pieces_subset_of_refines_both {B C : Basis ρ} (hBC : Refines ρ B C) (hCB : Refines ρ C B) :
    B.pieces ⊆ C.pieces := by
  intro a ha
  obtain ⟨b,hb⟩ := hCB ⟨a,ha⟩
  obtain ⟨a',ha'⟩ := hBC b
  have haa : (⟨a,ha⟩ : B) = a' :=
    refines_ancestor_unique ρ (GermBrick.restricts_refl ρ a) (GermBrick.restricts_trans ρ hb ha')
  have hae : a = a'.1 := congrArg Subtype.val haa
  have he : GermBrick.region ρ a = GermBrick.region ρ b.1 := by
    apply Set.Subset.antisymm (GermBrick.region_subset_of_restricts ρ hb)
    simpa only [hae] using GermBrick.region_subset_of_restricts ρ ha'
  have heq : a = b.1 := GermBrick.eq_of_restricts_of_region_eq ρ hb he
  rw [heq]
  exact b.property

lemma refines_antisymm {B C : Basis ρ} (hBC : Refines ρ B C) (hCB : Refines ρ C B) : B = C :=
  ext ρ (Finset.Subset.antisymm (pieces_subset_of_refines_both ρ hBC hCB)
    (pieces_subset_of_refines_both ρ hCB hBC))

end Basis

end

end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinEquiv
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped commutatorElement

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace BrickSwap
variable (p q : Prefix S) (hd : Disjoint p.brick q.brick)

def elem : localGroup ρ :=
  ⟨(involutive p q hd).toPerm,by
    intro x
    by_cases hp : x ∈ p.brick
    · exact ⟨p,q,1,hp,by intro y; change fn p q _ = _; rw [chart_left,twist_one]⟩
    by_cases hq : x ∈ q.brick
    · exact ⟨q,p,1,hq,by intro y; change fn p q _ = _; rw [chart_right p q hd,twist_one]⟩
    let b := p.lengths + q.lengths
    let r := Prefix.gridPrefix b (Prefix.gridPoint b x)
    have hr : x ∈ r.brick := Prefix.mem_gridPrefix b x
    have hpr : Disjoint p.brick r.brick := Prefix.disjoint_of_length hr hp (by
      intro s
      simp [r,b,Prefix.gridPrefix_length])
    have hqr : Disjoint q.brick r.brick := Prefix.disjoint_of_length hr hq (by
      intro s
      simp [r,b,Prefix.gridPrefix_length])
    refine ⟨r,r,1,hr,?_⟩
    intro y
    change fn p q (r.chart y) = _
    rw [outside p q _ (fun hh => Set.disjoint_left.mp hpr hh (Prefix.chart_mem_brick _ _))
      (fun hh => Set.disjoint_left.mp hqr hh (Prefix.chart_mem_brick _ _)),twist_one]⟩

@[simp] lemma elem_apply (x : Box S) : (elem ρ p q hd).val x=fn p q x := rfl

@[simp] lemma elem_left (x : Box S) : (elem ρ p q hd).val (p.chart x)=q.chart x := chart_left p q x
@[simp] lemma elem_right (x : Box S) : (elem ρ p q hd).val (q.chart x)=p.chart x := chart_right p q hd x

end BrickSwap
end TwistedBrin

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace Prefix

lemma cut_partition (s : S) : IsPartition (cut s) := by
  intro x
  refine ⟨(x s).get 0, (mem_cut_iff s _ x).mpr rfl, ?_⟩
  intro b hb
  exact ((mem_cut_iff s b x).mp hb).symm

end Prefix

def Stationary (s : S) (g : localGroup ρ) : Prop :=
  ∀ b x, g.val ((Prefix.cut s b).chart x) = (Prefix.cut s b).chart (g.val x)

end TwistedBrin

end
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinSeparated
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped commutatorElement

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace SimplicityProducer
variable {Q : Type*} [Group Q] (π : localGroup ρ →* Q)

def KillsBrick (p : Prefix S) : Prop := ∀ g : localGroup ρ, π (Localization.hom ρ p g)=1

end SimplicityProducer
end TwistedBrin

end
end

end OAI
end


