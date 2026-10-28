-- Prove2me | Definitions.Def_OAIQ66So015
-- name    : OAIQ66So015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:18:15.700214+00:00
-- url     : https://prove2.me/theorems/8cdcf684-d7bd-49fd-9d14-c724dcd084b3
-- title:
--   Definitions bundle OAIQ66So015 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 278 declarations of OpenAI's Lean: 106 definitions, 3 inductive types or structures, 5 instances and 164 theorems. The definitions and types are `OAI.SimpleFInftyOvergroups.ContextualEncoding.CodedSearch.compute`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.FamilyProgram.compute`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.ProductFamily.Key`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.ProductFamily.Letter`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.ProductFamily.combine`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.ProductFamily.cost`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.ProductFamily.wordCost`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.instPrimcodableZModOfNatNat_solutions`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.instPrimcodableZModOfNatNat_solutions_1`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.ThreeCodes.code`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.ThreeCodes.inclusion`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.ThreeCodes.search`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Array.collect`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Array.collectedKey`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Double.G₀`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Double.X₀`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Enlargement.Coeff.Name`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Enlargement.Coeff.complement`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Enlargement.Coeff.mul`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Enlargement.Coeff.one`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Enlargement.Coeff.value`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Enlargement.gcost`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Enlargement.inverse`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Enlargement.operations`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Enlargement.rootInv`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Enlargement.xcost`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixNames.partialColumnKey`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixNames.partialMatrixKey`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.column`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.gcost`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.groupValue`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.matrix`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.nameOperations`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.pairedKey`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.partialGroupKey`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.partialPointKey`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.pointValue`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.rootMatrix`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.rootValue`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.xcost` and 69 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_AscendingHNNInnerTwist`, `FiniteType_OrderChains`, `FiniteType_OrderListChainsBased`, `FiniteType_ProductGroupHomology`, `FiniteType_RingExchange`, `FiniteType_StageConstruction`, `FiniteType_SteinbergSixThree`, `FiniteType_TwistedBrin`, `FiniteType_TwistedBrinBasis`, `FiniteType_TwistedBrinBasisTranslateEquiv`, `FiniteType_TwistedBrinPatternFactor`, `FiniteType_TwistedBrinPrefix`, `FiniteType_TwistedBrinRangeChartRestricts`, `SimpleOvergroups_ActionCorner`, `SimpleOvergroups_ActionMonoid`, `SimpleOvergroups_ArrayNames`, `SimpleOvergroups_ArrayOperations`, `SimpleOvergroups_ContextualCompiler`, `SimpleOvergroups_ContextualTables`, `SimpleOvergroups_DoubleEffective`, `SimpleOvergroups_EffectiveArrays`, `SimpleOvergroups_EffectiveFamilies`, `SimpleOvergroups_EffectiveTables`, `SimpleOvergroups_EnlargementCore`, `SimpleOvergroups_EnlargementNames`, `SimpleOvergroups_FamilyProgram`, `SimpleOvergroups_FirstFamilies`, `SimpleOvergroups_MatrixEffective`, `SimpleOvergroups_MatrixNames`, `SimpleOvergroups_MatrixWords`, `SimpleOvergroups_PolynomialNames`, `SimpleOvergroups_RingAssemblyTools`, `SimpleOvergroups_SemanticActionMonoid`, `SimpleOvergroups_SemanticActions`, `SimpleOvergroups_SemanticDouble`, `SimpleOvergroups_SemanticTests`, `SimpleOvergroups_ThreeCodes`, `SimpleOvergroups_TwoEnlargements`.
--
--   **Imports.** It imports the bundles `OAIQ66So000`, `OAIQ66So001`, `OAIQ66So005`, `OAIQ66So006`, `OAIQ66So007`, `OAIQ66So008` and `OAIQ66So009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So020`, `OAIQ66So021` and `OAIQ66So022`; the statements `OAI_StageGeometry_localGroup_overgroup_of_binary_ring_data`, `OAI.TwistedBrin.Basis.CutBasis.localGroup_finitelyPresented` and `OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates`; the proofs of `OAI_TwistedBrin_Basis_CutBasis_simplex_stabilizer_products`, `OAI_TwistedBrin_Basis_CutBasis_sublevel_exact` and `OAI_TwistedBrin_localGroup_geometric_of_torus_models`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So000
import Definitions.Def_OAIQ66So001
import Definitions.Def_OAIQ66So005
import Definitions.Def_OAIQ66So006
import Definitions.Def_OAIQ66So007
import Definitions.Def_OAIQ66So008
import Definitions.Def_OAIQ66So009

section
-- module Solutions.OAIQ066_SO.FiniteType_RingExchange
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
section
variable {R : Type*} [Ring R]

def retainedIndices : Set SixIndices := fun i => match i with
  | Sum.inl (Sum.inl a) => a=0
  | Sum.inl (Sum.inr a) => a=0
  | Sum.inr _ => True

end

end Steinberg

end

end OAI
end

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
section
variable {R : Type*} [Ring R]

lemma six_three (i j : SixIndices) (_hij : i≠j) : ∃ k, i≠k ∧ j≠k := by
  let a : SixIndices := Sum.inl (Sum.inl 0)
  let b : SixIndices := Sum.inl (Sum.inl 1)
  let c : SixIndices := Sum.inr 0
  have hab : a≠b := by decide
  have hac : a≠c := by decide
  have hbc : b≠c := by decide
  by_cases hia : i=a
  · by_cases hjb : j=b
    · exact ⟨c,by rw [hia]; exact hac,by rw [hjb]; exact hbc⟩
    · exact ⟨b,by rw [hia]; exact hab,hjb⟩
  · by_cases hja : j=a
    · by_cases hib : i=b
      · exact ⟨c,by rw [hib]; exact hbc,by rw [hja]; exact hac⟩
      · exact ⟨b,hib,by rw [hja]; exact hab⟩
    · exact ⟨a,hia,hja⟩

end

variable {R S n m : Type*} [Ring R] [Ring S]

def sixEquiv : SixIndices ≃ Fin 6 :=
  (Fintype.equivFin SixIndices).trans (finCongr (by decide))

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StageConstruction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace StageConstruction
variable {R : Type*} [Ring R]
abbrev X (R : Type*) := Seven → R

def first : Seven := Sum.inr ()
def second : Seven := Sum.inl 0
lemma first_ne_second : first≠second := by decide

end StageConstruction

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingHNNInnerTwist
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise

namespace TorusStabilizer
open SequentialLimit SequentialAction AscendingHNN TorusAction HomStabilizer
variable {U X : Type*} [Group U] [MulAction U X]
variable (f : U →* U) (hf : Function.Injective f)
variable (s : X → X) (heq : ∀ g x, s (g • x)=f g • s x)
variable {J : Type*} (z : J → X) (a : U) (ha : ∀ j, a • s (z j)=z j)

def stageSubgroup : Subgroup U := fixedTuple (MulAction.toPermHom U X) z

end TorusStabilizer

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductGroupHomology
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
namespace ProductGroupHomology
open _root_.CategoryTheory CategoryTheory.Limits
attribute [-instance] AddCommGroup.toIntModule
end ProductGroupHomology

open Set Function
open scoped Pointwise

universe u v
namespace TwistedBrin
abbrev Box (S : Type u) := S → Cantor

namespace Prefix
variable {S : Type u}

def chart (p : Prefix S) : Box S → Box S := fun x s => Stream'.appendStream' (p s) (x s)
def tail (p : Prefix S) : Box S → Box S := fun x s => Stream'.drop (p s).length (x s)
def brick (p : Prefix S) : Set (Box S) := Set.range p.chart

@[simp] lemma chart_empty (x : Box S) : (empty : Prefix S).chart x = x := rfl
@[simp] lemma tail_chart (p : Prefix S) (x : Box S) : p.tail (p.chart x) = x := by
  funext s
  exact Stream'.drop_append_stream (p s) (x s)
lemma chart_injective (p : Prefix S) : Function.Injective p.chart :=
  Function.LeftInverse.injective (tail_chart p)
@[simp] lemma chart_mem_brick (p : Prefix S) (x : Box S) : p.chart x ∈ p.brick := ⟨x,rfl⟩
lemma chart_tail {p : Prefix S} {x : Box S} (h : x ∈ p.brick) : p.chart (p.tail x) = x := by
  obtain ⟨y,rfl⟩ := h
  rw [tail_chart]
lemma mem_brick_iff (p : Prefix S) (x : Box S) : x ∈ p.brick ↔
    ∀ s, Stream'.take (p s).length (x s) = p s := by
  constructor
  · rintro ⟨y,rfl⟩ s
    simpa only [chart,List.take_length] using
      Stream'.take_append_of_le_length (p s).length (p s) (y s) le_rfl
  · intro h
    refine ⟨p.tail x,?_⟩
    funext s
    change Stream'.appendStream' (p s) (Stream'.drop (p s).length (x s)) = x s
    nth_rw 1 [← h s]
    exact Stream'.append_take_drop (p s).length (x s)
@[simp] lemma brick_empty : (empty : Prefix S).brick = Set.univ := by
  ext; simp [brick]
@[simp] lemma chart_append (p q : Prefix S) (x : Box S) :
    (append p q).chart x = p.chart (q.chart x) := by
  funext s
  exact Stream'.append_append_stream (p s) (q s) (x s)

def suffix (p r : Prefix S) : Prefix S where
  word s := (r s).drop (p s).length
  finite_support := r.finite_support.subset (by
    intro s hs hz
    simp only [mem_ofPred_eq] at hs hz
    simp [hz] at hs)
@[simp] lemma suffix_apply (p r : Prefix S) (s : S) : suffix p r s = (r s).drop (p s).length := rfl

def Extends (p r : Prefix S) : Prop := ∀ s, p s <+: r s
lemma append_suffix {p r : Prefix S} (h : Extends p r) : append p (suffix p r) = r := by
  apply Prefix.ext
  intro s
  obtain ⟨l,hl⟩ := h s
  change p s ++ (r s).drop (p s).length = r s
  rw [← hl]
  simp

noncomputable def common (x : Box S) (p q : Prefix S) : Prefix S where
  word s := Stream'.take (max (p s).length (q s).length) (x s)
  finite_support := (p.finite_support.union q.finite_support).subset (by
    intro s hs
    simp only [mem_ofPred_eq, mem_union] at *
    by_contra h
    push Not at h
    simp [h.1,h.2] at hs)
@[simp] lemma common_apply (x : Box S) (p q : Prefix S) (s : S) :
    common x p q s = Stream'.take (max (p s).length (q s).length) (x s) := rfl
lemma mem_common (x : Box S) (p q : Prefix S) : x ∈ (common x p q).brick := by
  apply (mem_brick_iff _ _).mpr
  intro s
  simp
lemma extends_common_left {x : Box S} {p q : Prefix S} (hp : x ∈ p.brick) :
    Extends p (common x p q) := by
  intro s
  rw [← (mem_brick_iff p x).mp hp s]
  exact Stream'.take_prefix_take_left _ _ _ (le_max_left _ _)
lemma extends_common_right {x : Box S} {p q : Prefix S} (hq : x ∈ q.brick) :
    Extends q (common x p q) := by
  intro s
  rw [← (mem_brick_iff q x).mp hq s]
  exact Stream'.take_prefix_take_left _ _ _ (le_max_right _ _)

noncomputable def permute (σ : Equiv.Perm S) (p : Prefix S) : Prefix S where
  word s := p (σ.symm s)
  finite_support := p.finite_support.preimage σ.symm.injective.injOn
@[simp] lemma permute_apply (σ : Equiv.Perm S) (p : Prefix S) (s : S) :
    permute σ p s = p (σ.symm s) := rfl
end Prefix

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

def twist (a : A) : Equiv.Perm (Box S) where
  toFun x s := x (ρ a⁻¹ s)
  invFun x s := x (ρ a s)
  left_inv x := by funext s; simp
  right_inv x := by funext s; simp
@[simp] lemma twist_apply (a : A) (x : Box S) (s : S) : twist ρ a x s = x (ρ a⁻¹ s) := rfl
@[simp] lemma twist_one (x : Box S) : twist ρ 1 x = x := by ext; simp
lemma twist_mul (a b : A) (x : Box S) : twist ρ (a*b) x = twist ρ a (twist ρ b x) := by
  ext s n
  simp only [twist_apply,mul_inv_rev,map_mul,Equiv.Perm.coe_mul,Function.comp_apply]
lemma twist_chart (a : A) (p : Prefix S) (x : Box S) :
    twist ρ a (p.chart x) = (p.permute (ρ a)).chart (twist ρ a x) := by
  ext s n
  simp only [twist_apply,Prefix.chart,Prefix.permute_apply,map_inv,Equiv.Perm.inv_def]
lemma twist_prefix_inv (a : A) (p : Prefix S) :
    (p.permute (ρ a⁻¹)).permute (ρ a) = p := by
  apply Prefix.ext
  intro s
  simp only [Prefix.permute_apply,map_inv,Equiv.Perm.inv_def,Equiv.symm_symm,
    Equiv.apply_symm_apply]

def LocallyStandard (f : Box S → Box S) : Prop :=
  ∀ x : Box S, ∃ (p q : Prefix S) (a : A), x ∈ p.brick ∧
    ∀ y : Box S, f (p.chart y) = q.chart (twist ρ a y)

def IsLocal (f : Equiv.Perm (Box S)) : Prop := LocallyStandard ρ f

lemma isLocal_one : IsLocal ρ 1 := by
  intro x
  refine ⟨Prefix.empty,Prefix.empty,1,?_,?_⟩
  · simp
  · intro y; simp

lemma isLocal_inv {f : Equiv.Perm (Box S)} (hf : IsLocal ρ f) : IsLocal ρ f⁻¹ := by
  intro x
  obtain ⟨p,q,a,hx,h⟩ := hf (f⁻¹ x)
  have hx' : x ∈ q.brick := by
    obtain ⟨y,hy⟩ := hx
    refine ⟨twist ρ a y,?_⟩
    rw [← h,hy]
    exact f.apply_symm_apply x
  refine ⟨q,p,a⁻¹,hx',?_⟩
  intro y
  apply f.injective
  rw [Equiv.Perm.inv_def,f.apply_symm_apply,h]
  rw [← twist_mul,mul_inv_cancel,twist_one]

lemma isLocal_mul {f g : Equiv.Perm (Box S)} (hf : IsLocal ρ f) (hg : IsLocal ρ g) :
    IsLocal ρ (f*g) := by
  intro x
  obtain ⟨p,q,a,hx,hg'⟩ := hg x
  obtain ⟨r,s,b,hy,hf'⟩ := hf (g x)
  have hyq : g x ∈ q.brick := by
    obtain ⟨y,rfl⟩ := hx
    rw [hg']
    exact Prefix.chart_mem_brick _ _
  let v := Prefix.common (g x) q r
  let c := Prefix.suffix q v
  let d := Prefix.suffix r v
  have hc : Prefix.append q c = v := Prefix.append_suffix (Prefix.extends_common_left hyq)
  have hd : Prefix.append r d = v := Prefix.append_suffix (Prefix.extends_common_right hy)
  let c' := c.permute (ρ a⁻¹)
  let p' := Prefix.append p c'
  let s' := Prefix.append s (d.permute (ρ b))
  have hg_ref (y : Box S) : g (p'.chart y) = v.chart (twist ρ a y) := by
    dsimp [p']
    rw [Prefix.chart_append,hg',twist_chart,twist_prefix_inv,← Prefix.chart_append,hc]
  have hp' : x ∈ p'.brick := by
    obtain ⟨y,hy⟩ := Prefix.mem_common (g x) q r
    refine ⟨twist ρ a⁻¹ y,?_⟩
    apply g.injective
    rw [hg_ref,← twist_mul,mul_inv_cancel,twist_one,hy]
  refine ⟨p',s',b*a,hp',?_⟩
  intro y
  change f (g (p'.chart y)) = _
  rw [hg_ref,← hd,Prefix.chart_append,hf',twist_chart,← Prefix.chart_append]
  rw [twist_mul]

def localGroup : Subgroup (Equiv.Perm (Box S)) where
  carrier := IsLocal ρ
  one_mem' := isLocal_one ρ
  inv_mem' := isLocal_inv ρ
  mul_mem' := isLocal_mul ρ

end TwistedBrin

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma mem_brick_iff_get (p : Prefix S) (x : Box S) : x ∈ p.brick ↔
    ∀ s (n : ℕ) (hn : n < (p s).length), (x s).get n = (p s)[n] := by
  rw [mem_brick_iff]
  constructor
  · intro h s n hn
    have he := congrArg (fun l : List Bool => l[n]?) (h s)
    simpa only [List.getElem?_eq_getElem hn,Stream'.getElem?_take hn,Option.some.injEq] using he
  · intro h s
    apply List.ext_getElem (Stream'.length_take _ _)
    intro n hn hn'
    rw [Stream'.take_get]
    exact h s n hn'

noncomputable def lengths (p : Prefix S) : S →₀ ℕ :=
  Finsupp.ofSupportFinite (fun s => (p s).length) (by simpa [Function.support] using p.finite_support)
@[simp] lemma lengths_apply (p : Prefix S) (s : S) : p.lengths s = (p s).length := rfl

end TwistedBrin.Prefix

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrin
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma locallyStandard_id : LocallyStandard ρ id := isLocal_one ρ

lemma locallyStandard_comp {f g : Box S → Box S} (hf : LocallyStandard ρ f)
    (hg : LocallyStandard ρ g) (hgi : Function.Injective g) :
    LocallyStandard ρ (f ∘ g) := by
  intro x
  obtain ⟨p,q,a,hx,hg'⟩ := hg x
  obtain ⟨r,s,b,hy,hf'⟩ := hf (g x)
  have hyq : g x ∈ q.brick := by
    obtain ⟨y,rfl⟩ := hx
    rw [hg']
    exact Prefix.chart_mem_brick _ _
  let v := Prefix.common (g x) q r
  let c := Prefix.suffix q v
  let d := Prefix.suffix r v
  have hc : Prefix.append q c = v := Prefix.append_suffix (Prefix.extends_common_left hyq)
  have hd : Prefix.append r d = v := Prefix.append_suffix (Prefix.extends_common_right hy)
  let c' := c.permute (ρ a⁻¹)
  let p' := Prefix.append p c'
  let s' := Prefix.append s (d.permute (ρ b))
  have hg_ref (y : Box S) : g (p'.chart y) = v.chart (twist ρ a y) := by
    dsimp [p']
    rw [Prefix.chart_append,hg',twist_chart,twist_prefix_inv,← Prefix.chart_append,hc]
  have hp' : x ∈ p'.brick := by
    obtain ⟨y,hy⟩ := Prefix.mem_common (g x) q r
    refine ⟨twist ρ a⁻¹ y,?_⟩
    apply hgi
    rw [hg_ref,← twist_mul,mul_inv_cancel,twist_one,hy]
  refine ⟨p',s',b*a,hp',?_⟩
  intro y
  change f (g (p'.chart y)) = _
  rw [hg_ref,← hd,Prefix.chart_append,hf',twist_chart,← Prefix.chart_append]
  rw [twist_mul]

structure LocalEmbedding extends Box S ↪ Box S where
  locally_standard : LocallyStandard ρ toFun

namespace LocalEmbedding
instance instCoeFunForallBox : CoeFun (LocalEmbedding ρ) (fun _ => Box S → Box S) := ⟨fun h => h.toEmbedding⟩
@[ext] lemma ext {h k : LocalEmbedding ρ} (he : ∀ x, h x = k x) : h = k := by
  cases h; cases k
  simp_all only [mk.injEq]
  exact DFunLike.ext _ _ he

lemma injective (h : LocalEmbedding ρ) : Function.Injective h := h.toEmbedding.injective

def identity : LocalEmbedding ρ where
  toEmbedding := Function.Embedding.refl _
  locally_standard := locallyStandard_id ρ

@[simp] lemma identity_apply (x : Box S) : identity ρ x = x := rfl

def comp (h k : LocalEmbedding ρ) : LocalEmbedding ρ where
  toFun x := h (k x)
  inj' := h.injective.comp k.injective
  locally_standard := locallyStandard_comp ρ (f := h) (g := k)
    h.locally_standard k.locally_standard k.injective

@[simp] lemma comp_apply (h k : LocalEmbedding ρ) (x : Box S) : comp ρ h k x = h (k x) := rfl
@[simp] lemma identity_comp (h : LocalEmbedding ρ) : comp ρ (identity ρ) h = h := by ext; rfl
@[simp] lemma comp_identity (h : LocalEmbedding ρ) : comp ρ h (identity ρ) = h := by ext; rfl

def ofPrefix (p : Prefix S) : LocalEmbedding ρ where
  toEmbedding := ⟨p.chart,p.chart_injective⟩
  locally_standard := by
    intro x
    refine ⟨Prefix.empty,p,1,by simp,?_⟩
    intro y
    simp
@[simp] lemma ofPrefix_apply (p : Prefix S) (x : Box S) : ofPrefix ρ p x = p.chart x := rfl

def global (a : A) : LocalEmbedding ρ where
  toEmbedding := (twist ρ a).toEmbedding
  locally_standard := by
    intro x
    exact ⟨Prefix.empty,Prefix.empty,a,by simp,fun _ => rfl⟩
@[simp] lemma global_apply (a : A) (x : Box S) : global ρ a x = twist ρ a x := rfl
@[simp] lemma global_one : global ρ 1 = identity ρ := by ext; simp

def ofGroup (g : localGroup ρ) : LocalEmbedding ρ where
  toEmbedding := g.val.toEmbedding
  locally_standard := g.property
@[simp] lemma ofGroup_apply (g : localGroup ρ) (x : Box S) : ofGroup ρ g x = g.val x := rfl

def Gauge (h k : LocalEmbedding ρ) : Prop := ∃ a : A, h = comp ρ k (global ρ a)

lemma gauge_refl (h : LocalEmbedding ρ) : Gauge ρ h h := by
  refine ⟨1,?_⟩; simp
lemma gauge_symm {h k : LocalEmbedding ρ} (he : Gauge ρ h k) : Gauge ρ k h := by
  obtain ⟨a,rfl⟩ := he
  refine ⟨a⁻¹,?_⟩
  ext x
  simp only [comp_apply,global_apply,← twist_mul,mul_inv_cancel,twist_one]
lemma gauge_trans {h k l : LocalEmbedding ρ} (hh : Gauge ρ h k) (hk : Gauge ρ k l) :
    Gauge ρ h l := by
  obtain ⟨a,rfl⟩ := hh
  obtain ⟨b,rfl⟩ := hk
  refine ⟨b*a,?_⟩
  ext x
  simp only [comp_apply,global_apply,twist_mul]

instance gaugeSetoid : Setoid (LocalEmbedding ρ) where
  r := Gauge ρ
  iseqv := ⟨gauge_refl ρ,fun h => gauge_symm ρ h,fun h k => gauge_trans ρ h k⟩

lemma gauge_range_eq {h k : LocalEmbedding ρ} (he : Gauge ρ h k) : Set.range h = Set.range k := by
  obtain ⟨a,rfl⟩ := he
  change Set.range (k ∘ twist ρ a) = _
  rw [Set.range_comp,Set.range_eq_univ.mpr (twist ρ a).surjective,Set.image_univ]

lemma gauge_comp_left (g : LocalEmbedding ρ) {h k : LocalEmbedding ρ} (he : Gauge ρ h k) :
    Gauge ρ (comp ρ g h) (comp ρ g k) := by
  obtain ⟨a,rfl⟩ := he
  exact ⟨a,rfl⟩

end LocalEmbedding

def GermBrick := Quotient (LocalEmbedding.gaugeSetoid ρ)

namespace GermBrick

def mk (h : LocalEmbedding ρ) : GermBrick ρ := Quotient.mk' h

def region : GermBrick ρ → Set (Box S) :=
  Quotient.lift (fun h : LocalEmbedding ρ => Set.range h) (fun _ _ he => LocalEmbedding.gauge_range_eq ρ he)
@[simp] lemma region_mk (h : LocalEmbedding ρ) : region ρ (mk ρ h) = Set.range h := rfl

def map (g : LocalEmbedding ρ) : GermBrick ρ → GermBrick ρ :=
  Quotient.map (LocalEmbedding.comp ρ g) (fun _ _ he => LocalEmbedding.gauge_comp_left ρ g he)
@[simp] lemma map_mk (g h : LocalEmbedding ρ) : map ρ g (mk ρ h) = mk ρ (LocalEmbedding.comp ρ g h) := rfl

@[simp] lemma map_identity (b : GermBrick ρ) : map ρ (LocalEmbedding.identity ρ) b = b := by
  induction b using Quotient.inductionOn with | h h =>
    change mk ρ (LocalEmbedding.comp ρ (LocalEmbedding.identity ρ) h) = mk ρ h
    rw [LocalEmbedding.identity_comp]
lemma map_comp (g h : LocalEmbedding ρ) (b : GermBrick ρ) :
    map ρ (LocalEmbedding.comp ρ g h) b = map ρ g (map ρ h b) := by
  induction b using Quotient.inductionOn with | h k => rfl

lemma region_map (g : LocalEmbedding ρ) (b : GermBrick ρ) :
    region ρ (map ρ g b) = g '' region ρ b := by
  induction b using Quotient.inductionOn with | h h =>
    exact Set.range_comp g h

end GermBrick
end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace LocalEmbedding

@[simp] lemma ofGroup_one : ofGroup ρ 1 = identity ρ := rfl
lemma ofGroup_mul (g h : localGroup ρ) :
    ofGroup ρ (g*h) = comp ρ (ofGroup ρ g) (ofGroup ρ h) := rfl
@[simp] lemma ofPrefix_empty : ofPrefix ρ Prefix.empty = identity ρ := rfl

end LocalEmbedding
namespace GermBrick

noncomputable def representative (b : GermBrick ρ) : LocalEmbedding ρ := Quotient.out b
@[simp] lemma mk_representative (b : GermBrick ρ) : mk ρ (representative ρ b) = b := Quotient.out_eq b
lemma mk_eq_iff (h k : LocalEmbedding ρ) : mk ρ h = mk ρ k ↔ LocalEmbedding.Gauge ρ h k :=
  Quotient.eq

def groupEquiv (g : localGroup ρ) : Equiv.Perm (GermBrick ρ) where
  toFun := map ρ (LocalEmbedding.ofGroup ρ g)
  invFun := map ρ (LocalEmbedding.ofGroup ρ g⁻¹)
  left_inv b := by
    rw [← map_comp,← LocalEmbedding.ofGroup_mul,inv_mul_cancel,LocalEmbedding.ofGroup_one,map_identity]
  right_inv b := by
    rw [← map_comp,← LocalEmbedding.ofGroup_mul,mul_inv_cancel,LocalEmbedding.ofGroup_one,map_identity]

@[simp] lemma groupEquiv_apply (g : localGroup ρ) (b : GermBrick ρ) :
    groupEquiv ρ g b = map ρ (LocalEmbedding.ofGroup ρ g) b := rfl

lemma region_groupEquiv (g : localGroup ρ) (b : GermBrick ρ) :
    region ρ (groupEquiv ρ g b) = g.val '' region ρ b := region_map ρ _ _

end GermBrick

structure Basis where
  pieces : Finset (GermBrick ρ)
  partition : ∀ x : Box S, ∃! b : {b // b ∈ pieces}, x ∈ GermBrick.region ρ b.1

namespace Basis

instance instCoeSortType : CoeSort (Basis ρ) (Type _) := ⟨fun B => {b // b ∈ B.pieces}⟩
instance instFintypeSubtypeGermBrickMemFinsetPieces (B : Basis ρ) : Fintype B := inferInstanceAs (Fintype {b // b ∈ B.pieces})

def rank (B : Basis ρ) : ℕ := B.pieces.card

noncomputable def chart (B : Basis ρ) (b : B) : LocalEmbedding ρ :=
  GermBrick.representative ρ b.1
lemma chart_region (B : Basis ρ) (b : B) : Set.range (chart ρ B b) = GermBrick.region ρ b.1 := by
  change GermBrick.region ρ (GermBrick.mk ρ (GermBrick.representative ρ b.1)) = _
  rw [GermBrick.mk_representative]

noncomputable def evaluate (B : Basis ρ) (z : B × Box S) : Box S := chart ρ B z.1 z.2

lemma evaluate_bijective (B : Basis ρ) : Function.Bijective (evaluate ρ B) := by
  constructor
  · rintro ⟨b,x⟩ ⟨c,y⟩ h
    have hb : evaluate ρ B (b,x) ∈ GermBrick.region ρ b.1 := by
      rw [← chart_region]
      exact ⟨x,rfl⟩
    have hc : evaluate ρ B (b,x) ∈ GermBrick.region ρ c.1 := by
      rw [h,← chart_region]
      exact ⟨y,rfl⟩
    have he := (B.partition (evaluate ρ B (b,x))).unique hb hc
    subst c
    have hxy : x = y := (chart ρ B b).toEmbedding.injective h
    subst y
    rfl
  · intro x
    obtain ⟨b,hb,_⟩ := B.partition x
    rw [← chart_region ρ B b] at hb
    obtain ⟨y,rfl⟩ := hb
    exact ⟨(b,y),rfl⟩

noncomputable def equivalence (B : Basis ρ) : B × Box S ≃ Box S :=
  Equiv.ofBijective (evaluate ρ B) (evaluate_bijective ρ B)

@[simp] lemma equivalence_apply (B : Basis ρ) (z : B × Box S) :
    equivalence ρ B z = chart ρ B z.1 z.2 := rfl

noncomputable def translate (g : localGroup ρ) (B : Basis ρ) : Basis ρ := by
  classical
  exact {
    pieces := B.pieces.map (GermBrick.groupEquiv ρ g).toEmbedding
    partition := by
      intro x
      obtain ⟨b,hb,hu⟩ := B.partition (g.val.symm x)
      let c : {c // c ∈ B.pieces.map (GermBrick.groupEquiv ρ g).toEmbedding} :=
        ⟨GermBrick.groupEquiv ρ g b.1,Finset.mem_map.mpr ⟨b.1,b.property,rfl⟩⟩
      refine ⟨c,?_,?_⟩
      · change x ∈ GermBrick.region ρ (GermBrick.groupEquiv ρ g b.1)
        rw [GermBrick.region_groupEquiv]
        exact ⟨g.val.symm x,hb,g.val.apply_symm_apply x⟩
      · intro d hd
        obtain ⟨e,he,hed⟩ := Finset.mem_map.mp d.property
        have hd' : g.val.symm x ∈ GermBrick.region ρ e := by
          rw [← hed] at hd
          change x ∈ GermBrick.region ρ (GermBrick.groupEquiv ρ g e) at hd
          rw [GermBrick.region_groupEquiv] at hd
          obtain ⟨y,hy,hyx⟩ := hd
          have hey : y = g.val.symm x := (g.val.eq_symm_apply).mpr hyx
          rwa [hey] at hy
        have hh : (⟨e,he⟩ : B) = b := hu _ hd'
        apply Subtype.ext
        exact hed.symm.trans (congrArg (GermBrick.groupEquiv ρ g) (congrArg Subtype.val hh)) }

@[simp] lemma rank_translate (g : localGroup ρ) (B : Basis ρ) :
    rank ρ (translate ρ g B) = rank ρ B := Finset.card_map _

end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChainsBased
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise

namespace SteinChains
section
variable (V : Type*)

noncomputable def choose (F : Face V) : V := F.property.choose
end

end SteinChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChains
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise

namespace SteinChains
variable (V : Type*) [Fintype V]

def properInclude : ProperFace V →o Face V where
  toFun F := ⟨F.val,Finset.nonempty_iff_ne_empty.mpr F.property.1⟩
  monotone' := fun _ _ h => h

noncomputable def properProject (v : V) (hv : 1 < Fintype.card V) : Face V → ProperFace V := by
  classical
  exact fun F => if h : F.val ≠ Finset.univ then ⟨F.val,Finset.nonempty_iff_ne_empty.mp F.property,h⟩
    else ⟨{v},by
      constructor
      · exact Finset.singleton_nonempty _ |>.ne_empty
      · intro he
        have hh := congrArg Finset.card he
        simp only [Finset.card_singleton,Finset.card_univ] at hh
        omega⟩
end SteinChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinRangeChartRestricts
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

@[ext] lemma ext {B C : Basis ρ} (h : B.pieces = C.pieces) : B = C := by
  cases B; cases C
  simp_all only

end Basis

lemma locallyStandard_of_charts {I : Type*} (k h : I → LocalEmbedding ρ)
    (hk : ∀ x : Box S, ∃ i y, k i y = x) (f : Box S → Box S)
    (hf : ∀ i y, f (k i y) = h i y) : LocallyStandard ρ f := by
  intro x
  obtain ⟨i,y,rfl⟩ := hk x
  obtain ⟨p,q,a,hyp,hk'⟩ := (k i).locally_standard y
  obtain ⟨r,s,b,hyr,hh'⟩ := (h i).locally_standard y
  let v := Prefix.common y p r
  let c := p.suffix v
  let d := r.suffix v
  have hp : p.append c = v := Prefix.append_suffix (Prefix.extends_common_left hyp)
  have hr : r.append d = v := Prefix.append_suffix (Prefix.extends_common_right hyr)
  let q' := q.append (c.permute (ρ a))
  let s' := s.append (d.permute (ρ b))
  have hk_v (z : Box S) : k i (v.chart z) = q'.chart (twist ρ a z) := by
    change (k i).toFun (v.chart z) = _
    rw [← hp,Prefix.chart_append,hk',twist_chart,← Prefix.chart_append]
  have hh_v (z : Box S) : h i (v.chart z) = s'.chart (twist ρ b z) := by
    change (h i).toFun (v.chart z) = _
    rw [← hr,Prefix.chart_append,hh',twist_chart,← Prefix.chart_append]
  have hym : y ∈ v.brick := Prefix.mem_common y p r
  obtain ⟨z,hz⟩ := hym
  refine ⟨q',s',b*a⁻¹,?_,?_⟩
  · rw [← hz,hk_v]
    exact Prefix.chart_mem_brick _ _
  · intro w
    have hw : q'.chart w = k i (v.chart (twist ρ a⁻¹ w)) := by
      rw [hk_v,← twist_mul,mul_inv_cancel,twist_one]
    rw [hw,hf,hh_v,twist_mul]

end

end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasis
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.Prefix
variable {S : Type u}
open scoped Classical

noncomputable def cut (s : S) (b : Bool) : Prefix S := by
  classical
  exact ⟨fun t => if t = s then [b] else [],(Set.finite_singleton s).subset (by
    intro t ht
    by_contra hn
    simp only [Set.mem_singleton_iff] at hn
    simp only [Set.mem_ofPred_eq,ite_eq_right hn,ne_eq,not_true_eq_false] at ht)⟩

@[simp] lemma cut_apply (s t : S) (b : Bool) : cut s b t = if t = s then [b] else [] := by
  classical
  rfl

lemma mem_cut_iff (s : S) (b : Bool) (x : Box S) : x ∈ (cut s b).brick ↔ (x s).get 0 = b := by
  classical
  rw [mem_brick_iff_get]
  constructor
  · intro h
    simpa [cut_apply] using h s 0 (by simp)
  · intro h t n hn
    by_cases ht : t = s
    · subst t
      have hn' : n < 1 := by simpa [cut_apply] using hn
      have he : n = 0 := by omega
      subst n
      simpa [cut_apply] using h
    · simp only [cut_apply,ite_eq_right ht,List.length_nil] at hn
      omega

lemma mem_append_iff (p q : Prefix S) (x : Box S) : x ∈ (p.append q).brick ↔
    x ∈ p.brick ∧ p.tail x ∈ q.brick := by
  constructor
  · rintro ⟨y,rfl⟩
    rw [chart_append]
    exact ⟨chart_mem_brick _ _,by rw [tail_chart]; exact chart_mem_brick _ _⟩
  · rintro ⟨hp,y,hy⟩
    refine ⟨y,?_⟩
    rw [chart_append,hy,chart_tail hp]

end TwistedBrin.Prefix

namespace TwistedBrin

namespace Pattern
variable {S : Type u}

noncomputable def leafPrefix : (P : Pattern S) → Leaves P → Prefix S
  | .leaf, _ => Prefix.empty
  | .split s P _, .inl i => (Prefix.cut s false).append (leafPrefix P i)
  | .split s _ Q, .inr i => (Prefix.cut s true).append (leafPrefix Q i)

end Pattern
end TwistedBrin

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

noncomputable def ofChartPartition {I : Type*} [Fintype I]
    (h : I → LocalEmbedding ρ)
    (hp : ∀ x : Box S, ∃! i : I, x ∈ Set.range (h i)) : Basis ρ := by
  classical
  exact {
    pieces := Finset.univ.image (fun i => GermBrick.mk ρ (h i))
    partition := by
      intro x
      obtain ⟨i,hi,hu⟩ := hp x
      refine ⟨⟨_,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩,hi,?_⟩
      intro b hb
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp b.property
      apply Subtype.ext
      have hjx : x ∈ Set.range (h j) := by
        change x ∈ GermBrick.region ρ b.val at hb
        rwa [← hj] at hb
      exact hj.symm.trans (congrArg (fun i => GermBrick.mk ρ (h i)) (hu j hjx)) }

lemma chartPartition_injective {I : Type*} (h : I → LocalEmbedding ρ)
    (hp : ∀ x : Box S, ∃! i : I, x ∈ Set.range (h i)) :
    Function.Injective (fun i => GermBrick.mk ρ (h i)) := by
  intro i j he
  change GermBrick.mk ρ (h i) = GermBrick.mk ρ (h j) at he
  let x : Box S := h i (fun _ _ => false)
  have hi : x ∈ GermBrick.region ρ (GermBrick.mk ρ (h i)) := ⟨_,rfl⟩
  have hj : x ∈ Set.range (h j) := by
    change x ∈ GermBrick.region ρ (GermBrick.mk ρ (h j))
    rwa [← he]
  exact (hp x).unique hi hj

noncomputable def expandedChart (B : Basis ρ) (P : B → Pattern S)
    (i : Σ b : B, Pattern.Leaves (P b)) : LocalEmbedding ρ :=
  LocalEmbedding.comp ρ (chart ρ B i.1)
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (P i.1) i.2))

end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPrefix
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.Prefix
variable {S : Type u}
@[simp] lemma permute_empty (σ : Equiv.Perm S) : permute σ empty = empty := by ext; simp
@[simp] lemma permute_append (σ : Equiv.Perm S) (p q : Prefix S) :
    permute σ (p.append q) = (permute σ p).append (permute σ q) := by ext; rfl
@[simp] lemma permute_cut (σ : Equiv.Perm S) (s : S) (b : Bool) :
    permute σ (cut s b) = cut (σ s) b := by
  classical
  apply Prefix.ext
  intro t
  simp only [permute_apply,cut_apply]
  have he : σ.symm t = s ↔ t = σ s := σ.symm_apply_eq
  simp only [he]
end TwistedBrin.Prefix

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

structure Forest (B C : Basis ρ) where
  pattern : B → Pattern S
  leaves : (Σ b : B, Pattern.Leaves (pattern b)) ≃ C
  chart_eq : ∀ i, GermBrick.mk ρ (expandedChart ρ B pattern i) = (leaves i).val

def CutRefines (B C : Basis ρ) : Prop := Nonempty (Forest ρ B C)

end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisTranslateEquiv
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

noncomputable def translateEquiv (g : localGroup ρ) (B : Basis ρ) : B ≃ translate ρ g B := by
  classical
  let f : B → translate ρ g B := fun b =>
    ⟨GermBrick.groupEquiv ρ g b.val,Finset.mem_map.mpr ⟨b.val,b.property,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro b c he
    apply Subtype.ext
    exact (GermBrick.groupEquiv ρ g).injective (congrArg Subtype.val he)
  · intro c
    obtain ⟨b,hb,hbc⟩ := Finset.mem_map.mp c.property
    exact ⟨⟨b,hb⟩,Subtype.ext hbc⟩

@[simp] lemma translateEquiv_val (g : localGroup ρ) (B : Basis ρ) (b : B) :
    (translateEquiv ρ g B b).val = GermBrick.groupEquiv ρ g b.val := rfl

end TwistedBrin.Basis

namespace TwistedBrin.Prefix
variable {S : Type u}

noncomputable def splitEquiv (s : S) : Bool × Box S ≃ Box S where
  toFun z := (cut s z.1).chart z.2
  invFun x := ⟨(x s).get 0,(cut s ((x s).get 0)).tail x⟩
  left_inv := by
    rintro ⟨b,x⟩
    have hb : (((cut s b).chart x) s).get 0 = b :=
      (mem_cut_iff s b _).mp (chart_mem_brick _ _)
    simp only [hb,tail_chart]
  right_inv x := chart_tail ((mem_cut_iff s ((x s).get 0) x).mpr rfl)

@[simp] lemma splitEquiv_apply (s : S) (b : Bool) (x : Box S) :
    splitEquiv s (b,x) = (cut s b).chart x := rfl

end TwistedBrin.Prefix

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPatternFactor
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.Pattern
section
variable {S : Type u}

noncomputable def firstCoordinates (P : Pattern S) : Finset S := by
  classical
  exact (coordinates P).filter (fun s => ∀ i : Leaves P, leafPrefix P i s ≠ [])

end

end TwistedBrin.Pattern

namespace TwistedBrin.Pattern
variable {S : Type u}

@[simp] lemma firstCoordinates_leaf : firstCoordinates (.leaf : Pattern S) = ∅ := by
  classical
  simp [firstCoordinates,coordinates]

end TwistedBrin.Pattern

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ActionMonoid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SourceActionMonoid
universe u v
variable (V : Type u) (Z : Type v) [Group V] [MulAction V Z]

variable {V Z}

namespace Algorithm
variable [DecidableEq Z]

lemma eval_step (c : Generator V Z) (f : Form (V := V) (Z := Z)) :
    eval (step c f) = of c * eval f := by
  cases f with
  | none => exact (of_omega c).symm
  | some p =>
    rcases p with ⟨l, g, r⟩
    cases c with
    | zero => exact (omega_mul _).symm
    | pre z => exact (prepend_normal z l g r).symm
    | grp h =>
      cases l with
      | nil => exact (group_normal_nil h g r).symm
      | cons z l => exact (group_normal_cons h z l g r).symm
    | delete y =>
      cases l with
      | nil => exact (delete_normal_nil y g r).symm
      | cons z l =>
        by_cases h : y = z
        · subst y
          change eval (if z = z then some (l, g, r) else none) =
            delete z * normal (z :: l) g r
          rw [ite_eq_left rfl]
          exact (delete_normal_cons z l g r).symm
        · change eval (if y = z then some (l, g, r) else none) =
            delete y * normal (z :: l) g r
          rw [ite_eq_right h]
          exact (delete_normal_cons_ne y z h l g r).symm

theorem normalize_correct (w : List (Generator V Z)) :
    eval (normalize w) = PresentedMonoid.mk (Relation V Z) (FreeMonoid.ofList w) := by
  induction w with
  | nil => simp [normalize, eval, normal]
  | cons c w ih =>
    simp only [normalize, eval_step, ih, FreeMonoid.ofList_cons, map_mul]
    rfl

theorem word_eq_iff (a b : List (Generator V Z)) :
    PresentedMonoid.mk (Relation V Z) (FreeMonoid.ofList a) =
        PresentedMonoid.mk (Relation V Z) (FreeMonoid.ofList b) ↔ normalize a = normalize b := by
  rw [← normalize_correct, ← normalize_correct]
  exact eval_injective.eq_iff

end Algorithm
end SourceActionMonoid

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ActionCorner
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SimpleFInftyOvergroups.RingAssembly
open SourceActionMonoid
open scoped Classical
variable {V Y R : Type*} [Group V] [MulAction V Y] [Ring R]

attribute [local instance] OAI.SimpleFInftyOvergroups.RingAssembly.actionCornerMonoidWithZero
variable (δ : M V Y →*₀ R)

theorem corner_TS (y z : Y) : δ (delete y) * δ (prepend z)=if y=z then 1 else 0 := by
  rw [←map_mul]
  by_cases hyz : y=z
  · subst z
    rw [ite_eq_left rfl,delete_prefix,map_one]
  · rw [ite_eq_right hyz,delete_prefix_ne y z hyz]
    exact map_zero δ

end SimpleFInftyOvergroups.RingAssembly
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ArrayNames
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace SimpleFInftyOvergroups.EffectiveNames.Array
noncomputable section
open scoped Classical
variable {A X D K : Type*} [AddCommMonoid D]
variable (coeff : A → D) (index : X → K)

variable (zeroName : A) (addName : A → A → A)

variable [Primcodable A] [Primcodable X]
variable (ha : Primrec₂ addName)
variable (hx : ComputablePred (fun p : X × X => index p.1 = index p.2))
variable (hc : ComputablePred (fun p : A × A => coeff p.1 = coeff p.2))

include ha hx in
theorem computable_entry : Computable₂ (entry index zeroName addName) := by
  have hs : Computable₂ (fun (x : X) (a : A × X) =>
      if index a.2 = index x then a.1 else zeroName) := by
    refine (Computable.cond (hx.decide.comp
      ((Computable.snd.comp Computable.snd).pair Computable.fst))
      (Computable.fst.comp Computable.snd) (Computable.const zeroName)).of_eq ?_
    intro p
    simp only [Bool.cond_decide]
  have hl : Computable (fun p : Name A X × X =>
      p.1.map (fun a => if index a.2 = index p.2 then a.1 else zeroName)) :=
    (FiniteAlgebraicEnvelopes.Effect.computable_map_parameter hs).comp Computable.snd Computable.fst
  have hf : Primrec (fun l : List A => l.foldl addName zeroName) :=
    Primrec.list_foldl Primrec.id (Primrec.const zeroName)
      (ha.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact hf.to_comp.comp hl

include ha hx hc in
omit [AddCommMonoid D] in
theorem computable_entries_eq : Computable₂
    (fun (p : Name A X × Name A X) (a : A × X) =>
      decide (coeff (entry index zeroName addName p.1 a.2) =
        coeff (entry index zeroName addName p.2 a.2))) := by
  have he : Computable₂ (entry index zeroName addName) :=
    computable_entry index zeroName addName ha hx
  have hl : Computable (fun p : (Name A X × Name A X) × (A × X) =>
      entry index zeroName addName p.1.1 p.2.2) :=
    he.comp (Computable.fst.comp Computable.fst) (Computable.snd.comp Computable.snd)
  have hr : Computable (fun p : (Name A X × Name A X) × (A × X) =>
      entry index zeroName addName p.1.2 p.2.2) :=
    he.comp (Computable.snd.comp Computable.fst) (Computable.snd.comp Computable.snd)
  apply (hc.decide.comp (hl.pair hr)).of_eq
  intro p
  congr 1

include ha hx hc in
omit [AddCommMonoid D] in
theorem computable_entry_tests : Computable
    (fun p : Name A X × Name A X => (p.1++p.2).map fun a =>
      decide (coeff (entry index zeroName addName p.1 a.2) =
        coeff (entry index zeroName addName p.2 a.2))) :=
  (FiniteAlgebraicEnvelopes.Effect.computable_map_parameter
    (computable_entries_eq coeff index zeroName addName ha hx hc)).comp
      Computable.id (Primrec.list_append.to_comp.comp Computable.fst Computable.snd)

include ha hx hc in
theorem computable_value_eq (hzero : coeff zeroName = 0)
    (hadd : ∀ a b, coeff (addName a b) = coeff a + coeff b) :
    ComputablePred (fun p : Name A X × Name A X => value coeff index p.1 = value coeff index p.2) := by
  have hf : PrimrecPred (fun l : List Bool => ∀ b ∈ l, b = true) :=
    (show PrimrecPred (fun b : Bool => b = true) from
      Primrec.eq.comp Primrec.id (Primrec.const true)).forall_mem_list
  have ht := (hf.decide.to_comp.comp
    (computable_entry_tests coeff index zeroName addName ha hx hc)).computablePred
  apply ht.of_eq
  intro p
  rw [value_eq_iff]
  simp only [List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, decide_eq_true_eq, entry_correct coeff index zeroName addName hzero hadd]

end
end SimpleFInftyOvergroups.EffectiveNames.Array

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EnlargementCore
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SourceEnlargement

variable {D V Z : Type*} [Ring D] [Group V] [MulAction V Z]

@[simp] lemma value_identity (g : V) :
    value (1 : D) g = MonoidAlgebra.single g 1 := by simp [value]

lemma value_mul_orthogonal (E P : D) (hEP : E * P = 0) (g h : V) :
    value E g * value P h =
      MonoidAlgebra.single 1 (1 - (E + P)) +
        MonoidAlgebra.single h P + MonoidAlgebra.single g E := by
  have ha : (1 - E) * P = P := by rw [sub_mul, one_mul, hEP, sub_zero]
  have hb : E * (1 - P) = E := by rw [mul_sub, mul_one, hEP, sub_zero]
  simp only [value, add_mul, mul_add, MonoidAlgebra.single_mul_single,
    one_mul, mul_one, complement_product E P hEP, ha, hb, hEP,
    MonoidAlgebra.single_zero, add_zero]
  abel

lemma unitMap_commute (E P : D) (hE : E * E = E) (hP : P * P = P)
    (hEP : E * P = 0) (hPE : P * E = 0) (g h : V) :
    Commute (unitMap E hE g) (unitMap P hP h) := by
  apply Units.ext
  change value E g * value P h = value P h * value E g
  rw [value_mul_orthogonal E P hEP, value_mul_orthogonal P E hPE, add_comm P E]
  abel

lemma unitMap_add (E P : D) (hE : E * E = E) (hP : P * P = P)
    (hSum : (E + P) * (E + P) = E + P) (hEP : E * P = 0) (g : V) :
    unitMap (E + P) hSum g = unitMap E hE g * unitMap P hP g := by
  apply Units.ext
  change value (E + P) g = value E g * value P g
  rw [value_mul_orthogonal E P hEP, value, MonoidAlgebra.single_add]
  abel

lemma unitMap_basis (E : D) (hE : E * E = E) (g : V) (z : Z) :
    unitMap E hE g • Finsupp.single z (1 : D) =
      Finsupp.single z (1 - E) + Finsupp.single (g • z) E := by
  change ringAction (value E g) (Finsupp.single z (1 : D)) = _
  rw [value, map_add]
  change ringAction (MonoidAlgebra.single 1 (1 - E)) (Finsupp.single z (1 : D)) +
      ringAction (MonoidAlgebra.single g E) (Finsupp.single z (1 : D)) = _
  simp only [ringAction_single, one_smul, mul_one]

lemma unitMap_fixes (E : D) (hE : E * E = E) (g : V) (z : Z)
    (hz : g • z = z) :
    unitMap E hE g • Finsupp.single z (1 : D) = Finsupp.single z 1 := by
  rw [unitMap_basis, hz, ← Finsupp.single_add, sub_add_cancel]

variable (P : Set D) (hP : ∀ E ∈ P, E * E = E)

lemma map_identity_basis (h1 : 1 ∈ P) (g : V) (z : Z) :
    map P hP ⟨1, h1⟩ g • Finsupp.single z (1 : D) = Finsupp.single (g • z) 1 := by
  change unitMap (1 : D) (hP 1 h1) g • Finsupp.single z (1 : D) = _
  simp [unitMap_basis]

lemma map_fixes (E : P) (g : V) (z : Z) (hz : g • z = z) :
    map P hP E g • Finsupp.single z (1 : D) = Finsupp.single z 1 :=
  unitMap_fixes E.val (hP E.val E.property) g z hz

lemma map_commute (E E' : P) (hEP : E.val * E'.val = 0)
    (hPE : E'.val * E.val = 0) (g h : V) :
    Commute (map P hP E g) (map P hP E' h) := by
  apply Subtype.ext
  exact (unitMap_commute E.val E'.val (hP _ E.property) (hP _ E'.property) hEP hPE g h).eq

lemma map_add (E E' : P) (hSum : E.val + E'.val ∈ P)
    (hEP : E.val * E'.val = 0) (g : V) :
    map P hP ⟨E.val + E'.val, hSum⟩ g = map P hP E g * map P hP E' g := by
  apply Subtype.ext
  exact unitMap_add E.val E'.val (hP _ E.property) (hP _ E'.property) (hP _ hSum) hEP g

end SourceEnlargement
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ArrayOperations
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SimpleFInftyOvergroups.EffectiveNames.Array
noncomputable section
open scoped Classical
variable {A G X D V Y : Type*}

variable [Ring D] [Group V]
variable (coeff : A → D) (group : G → V)

variable [MulAction V Y] (point : X → Y)

 theorem value_action (cmul : A → A → A) (act : G → X → X)
    (hc : ∀ a b, coeff (cmul a b) = coeff a * coeff b)
    (ha : ∀ g x, point (act g x) = group g • point x) (p : Name A G) (q : Name A X) :
    value coeff point (product cmul act p q) =
      SourceEnlargement.ringAction (algebraValue coeff group p) (value coeff point q) := by
  induction p with
  | nil => simp
  | cons a p ih =>
    rw [product_cons,value_append,ih,algebraValue_cons,map_add]
    change _ = SourceEnlargement.ringAction (MonoidAlgebra.single (group a.2) (coeff a.1))
      (value coeff point q) + SourceEnlargement.ringAction (algebraValue coeff group p) (value coeff point q)
    congr 1
    clear ih
    induction q with
    | nil => simp
    | cons b q ih =>
      simp only [List.map_cons,value_cons,ih,hc,ha,map_add,SourceEnlargement.ringAction_single]

end
end SimpleFInftyOvergroups.EffectiveNames.Array

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_FirstFamilies
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes Bootstrap BoundedEncoding
noncomputable section
open scoped Classical

namespace ProductFamily
variable {A : Type*}
abbrev Letter (A : Type*) := A ⊕ PartialAffine.Letter
abbrev Key (A : Type*) := List A × List PartialAffine.Letter

def cost (c : A → ℕ) : Letter A → ℕ := Sum.elim c (fun _ => 0)
def wordCost (c : A → ℕ) (w : List (Letter A)) : ℕ := (w.map (cost c)).sum

@[simp] theorem wordCost_append (c : A → ℕ) (u v : List (Letter A)) :
    wordCost c (u++v) = wordCost c u + wordCost c v := by simp [wordCost]

theorem wordCost_projection (c : A → ℕ) (w : List (Letter A)) :
    wordCost c w = ((Projection.left w).map c).sum := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a <;> simp only [wordCost, List.map_cons, cost, Sum.elim_inl, Sum.elim_inr,
      List.sum_cons, Projection.left, List.filterMap_cons, List.map_cons, List.sum_cons, zero_add]
    · exact congrArg (c _ + ·) ih
    · exact ih

variable [DecidableEq A]
def combine (zero : List A) (q : Key A) : Option (Key A) :=
  if q.1 = zero then none else some q

end ProductFamily
end
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ContextualTables
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes.Bootstrap Relation

namespace CodeTable
variable {A S Q : Type*} {r : S → S → Prop} [Std.Trichotomous r]
variable (C : DelimiterCode A S) (E : FiniteSearch C) (wf : WellFounded r)
  (q : List A → Option Q) (z : S)

theorem decreasing (n : ℕ) : ∀ p ∈ table C E wf q z n, List.Shortlex r p.2 p.1 := by
  intro ⟨u,v⟩ hp
  obtain ⟨w,_,hwn,hne,rfl,rfl⟩ := (mem_table C E wf q z).mp hp
  by_cases hz : q w = none
  · simp only [output, ite_eq_left hz]
    apply List.Shortlex.of_length_lt
    have hw := C.length_le_encode w
    have hp : 0 < w.length := List.length_pos_iff.mpr hwn
    simp only [List.length_singleton]
    omega
  · simp only [output, ite_eq_right hz] at hne ⊢
    rcases EncodedCanonical.least_lt_or_eq C wf q w with h | h
    · exact h
    · exact (hne (by rw [h])).elim

theorem stable {k n : ℕ} (hkn : k ≤ n) :
    Selectors.BoundedEq (table C E wf q z k) (table C E wf q z n) k := by
  intro ⟨u,v⟩ hlen
  rw [mem_table, mem_table]
  constructor
  · rintro ⟨w,hw,hn,he,rfl,rfl⟩
    exact ⟨w,hw.trans hkn,hn,he,rfl,rfl⟩
  · rintro ⟨w,hw,hn,he,rfl,rfl⟩
    exact ⟨w,hlen,hn,he,rfl,rfl⟩
end CodeTable
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ThreeCodes
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
noncomputable section
open FiniteAlgebraicEnvelopes Bootstrap

namespace ThreeCodes
def inclusion (i : Fin 3) (a : Fin 4) : Alphabet := some (i,a)
theorem inclusion_injective (i : Fin 3) : Function.Injective (inclusion i) := by
  intro a b h
  exact (Prod.mk.inj (Option.some.inj h)).2

def code {A : Type*} [Encodable A] (i : Fin 3) (cost : A → ℕ) : DelimiterCode A Alphabet :=
  (PaddedCode.code cost).map (inclusion i) (inclusion_injective i)

def search {A : Type*} [Encodable A] (i : Fin 3) (cost : A → ℕ) : FiniteSearch (code i cost) where
  words := PaddedCode.words cost
  mem_words n w := by simpa only [code,DelimiterCode.map_encode,List.length_map] using PaddedCode.mem_words cost n w

theorem cost_padding {A : Type*} [Encodable A] (i : Fin 3) (cost : A → ℕ) (a : A) :
    10 * cost a + 2 ≤ ((code i cost).block a).length := by
  simpa only [code,DelimiterCode.map_block,List.length_map] using PaddedCode.cost_padding cost a

theorem zero_avoids {A : Type*} [Encodable A] (i : Fin 3) (cost : A → ℕ) :
    none ∉ (code i cost).alphabet := by
  intro h
  obtain ⟨a,ha⟩ := (PaddedCode.code cost).map_alphabet (inclusion i) (inclusion_injective i) h
  cases ha

theorem disjoint {A B : Type*} [Encodable A] [Encodable B] {i j : Fin 3}
    (hi : i ≠ j) (c : A → ℕ) (d : B → ℕ) :
    Disjoint (code i c).alphabet (code j d).alphabet := by
  apply Set.disjoint_left.mpr
  intro t ht hu
  obtain ⟨a,ha⟩ := (PaddedCode.code c).map_alphabet (inclusion i) (inclusion_injective i) ht
  obtain ⟨b,hb⟩ := (PaddedCode.code d).map_alphabet (inclusion j) (inclusion_injective j) hu
  exact hi (Prod.mk.inj (Option.some.inj (ha.trans hb.symm))).1

theorem primrec_encode {A : Type*} [Primcodable A] (i : Fin 3) (cost : A → ℕ) (hc : Primrec cost) :
    Primrec (code i cost).encode := by
  exact (Primrec.list_map (PaddedCode.primrec_encode cost hc)
    ((Primrec.dom_finite (inclusion i)).comp Primrec.snd).to₂).of_eq (fun w => (DelimiterCode.map_encode ..).symm)

theorem primrec_words {A : Type*} [Primcodable A] (i : Fin 3) (cost : A → ℕ) (hc : Primrec cost) :
    Primrec (search i cost).words := PaddedCode.primrec_words cost hc

end ThreeCodes
end
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EffectiveArrays
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Array
open FiniteAlgebraicEnvelopes
noncomputable section
open scoped Classical
variable {A X J D : Type*} [AddCommMonoid D] [Primcodable A] [Primcodable X] [Primcodable J]
  (coeff : A → D)

def collect (f : X → Part J) (p : Name A X) : Part (Name A J) :=
  Effect.traverse (fun a => (f a.2).map (fun k => (a.1,k))) p

def collectedKey (f : X → Part J) (p : Name A X) : Part ℕ :=
  (collect f p).map (key (value coeff id))

omit [Primcodable A] [Primcodable X] [Primcodable J] in
theorem collect_full (f : X → Part J) (g : X → J) (p : Name A X)
    (h : ∀ a ∈ p, g a.2 ∈ f a.2) :
    p.map (fun a => (a.1,g a.2)) ∈ collect f p := by
  apply FiniteAlgebraicEnvelopes.Bootstrap.Search.traverse_map
  intro a ha
  exact Part.mem_map _ (h a ha)

omit [Primcodable X] in
theorem collectedKey_full (hc : Function.Surjective coeff) (f : X → Part J)
    {K : Type*} (index : X → K) (g : K → J) (p : Name A X)
    (h : ∀ a ∈ p, g (index a.2) ∈ f a.2) :
    semanticKey (value coeff id) (value_surjective coeff id hc Function.surjective_id)
      (Finsupp.mapDomain g (value coeff index p)) ∈ collectedKey coeff f p := by
  rw [← value_map_index coeff index (g ∘ index) id g (fun _ => rfl) p,
    semanticKey_value]
  exact Part.mem_map _ (collect_full f (g ∘ index) p h)

variable {P : Type*} [Primcodable P] {f : P → X → Part J}

theorem partrec_collect (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => (collect (f p) : Name A X → Part (Name A J))) := by
  have hc : Partrec₂ (fun (p : P) (a : A × X) =>
      (f p a.2).map (fun k => (a.1,k))) := by
    exact ((hf.comp Computable.fst (Computable.snd.comp Computable.snd)).map
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd).to₂).to₂
  exact Effect.partrec_traverse_parameter hc

theorem partrec_collectedKey (heq : ComputablePred
    (fun p : Name A J × Name A J => value coeff id p.1 = value coeff id p.2))
    (hf : Partrec₂ f) : Partrec₂ (fun p : P => collectedKey coeff (f p)) := by
  exact (partrec_collect hf).map (((computable_key (value coeff id) heq).comp Computable.snd).to₂)

end
end SimpleFInftyOvergroups.EffectiveNames.Array

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EnlargementNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Enlargement
open BoundedEncoding NamedAction
noncomputable section
namespace Coeff
open BinaryPrefixOperators.Arithmetic
abbrev Name (k : Type*) := Lists.Poly k
variable {k : Type*} [CommRing k]
abbrev value := Lists.value (K:=k)
abbrev one := Lists.oneName (K:=k)
abbrev mul := Lists.product (K:=k)
def complement (a : Name k) : Name k := one ++ Lists.negate a
@[simp] theorem value_one : value (one (k:=k)) = 1 := Lists.value_oneName
end Coeff
open scoped Classical
variable {G X P k : Type*} [CommRing k] (N : Operations G X)

def rootInv (a : P × G) : P × G := (a.1,N.inv a.2)
def inverse (w : Word P G) : Word P G := w.reverse.map (rootInv N)
def gcost (w : Word P G) : ℕ := (w.map fun a => N.gcost a.2).sum
def xcost (x : Point P G X) : ℕ := gcost N x.1 + N.xcost x.2
@[simp] theorem inverse_nil : inverse N ([] : Word P G) = [] := rfl
@[simp] theorem inverse_cons (a : P × G) (w : Word P G) :
    inverse N (a::w) = inverse N w ++ [rootInv N a] := by simp [inverse]
@[simp] theorem gcost_nil : gcost N ([] : Word P G) = 0 := rfl
@[simp] theorem gcost_cons (a : P × G) (w : Word P G) :
    gcost N (a::w) = N.gcost a.2 + gcost N w := rfl
@[simp] theorem gcost_append (u v : Word P G) : gcost N (u++v) = gcost N u + gcost N v := by simp [gcost]
@[simp] theorem gcost_inverse (w : Word P G) : gcost N (inverse N w) = gcost N w := by
  simp [gcost,inverse,List.map_map,Function.comp_def,rootInv,N.cost_inv]

def operations : Operations (Word P G) (Point P G X) where
  one := []
  mul := (·++·)
  inv := inverse N
  act w x := (w++x.1,x.2)
  gcost := gcost N
  xcost := xcost N
  cost_one := rfl
  cost_mul := gcost_append N
  cost_inv := gcost_inverse N
  cost_act := by intros; simp [xcost,Nat.add_assoc]

end
end SimpleFInftyOvergroups.EffectiveNames.Enlargement

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_PolynomialNames
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace SimpleFInftyOvergroups.EffectiveNames.Polynomial
open BoundedEncoding
noncomputable section
open scoped Classical

variable {A k : Type*} [CommSemiring k]

variable {m : ℕ} (C : WordCalculus (FreeMonoid A) m)

variable [Primcodable A] [Primcodable k] [Finite k]

def partialCollect (omega : List A) (f : List A → Part (List A)) (p : Name k A) : Part (Name k A) :=
  (FiniteAlgebraicEnvelopes.Effect.traverse (fun a : k × List A =>
    (f a.2).map fun w => if w = omega then [] else [(a.1,w)]) p).map List.flatten

omit [CommSemiring k] [Primcodable A] [Primcodable k] [Finite k] in
theorem partialCollect_full (omega : List A) (f : List A → Part (List A))
    (normal : List A → List A) (p : Name k A) (h : ∀ a ∈ p, normal a.2 ∈ f a.2) :
    collectName omega normal p ∈ partialCollect omega f p := by
  have ht := FiniteAlgebraicEnvelopes.Bootstrap.Search.traverse_map
    (f := fun a : k × List A => (f a.2).map fun w => if w = omega then [] else [(a.1,w)])
    (g := fun a => if normal a.2 = omega then [] else [(a.1,normal a.2)])
    p (by intro a ha; exact Part.mem_map _ (h a ha))
  simpa only [partialCollect,collectName,List.flatMap] using Part.mem_map List.flatten ht

 theorem computable_value_eq : ComputablePred
    (fun p : Name k A × Name k A => value p.1 = value p.2) := by
  have he := Array.computable_value_eq (id : k → k) (id : List A → List A) 0 (·+·)
    (Primrec.dom_finite (fun p : k × k => p.1+p.2))
    Primrec.eq.computablePred Primrec.eq.computablePred rfl (by intros; rfl)
  exact he.of_eq (fun p => (value_eq_iff_arrays p.1 p.2).symm)

def partialKey (omega : List A) (f : List A → Part (List A)) (p : Name k A) : Part ℕ :=
  (partialCollect omega f p).map (key value)

variable {P : Type*} [Primcodable P] {f : P → List A → Part (List A)}
omit [CommSemiring k] [Finite k] in
 theorem partrec_partialCollect (omega : List A) (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => partialCollect (k:=k) omega (f p)) := by
  have hc : Partrec₂ (fun (p : P) (a : k × List A) =>
      (f p a.2).map fun w => if w = omega then [] else [(a.1,w)]) := by
    have hmap : Computable₂ (fun (p : P × (k × List A)) (w : List A) =>
        if w = omega then [] else [(p.2.1,w)]) := by
      refine (Computable.cond (Primrec.eq.decide.to_comp.comp
        Computable.snd (Computable.const omega)) (Computable.const [])
        (Primrec.list_cons.to_comp.comp
          ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)
          (Computable.const []))).of_eq ?_
      intro p
      simp only [Bool.cond_decide]
    exact ((hf.comp Computable.fst (Computable.snd.comp Computable.snd)).map hmap).to₂
  exact (FiniteAlgebraicEnvelopes.Effect.partrec_traverse_parameter hc).map
    (Primrec.list_flatten.to_comp.comp Computable.snd).to₂
 theorem partrec_partialKey (omega : List A) (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => partialKey (k:=k) omega (f p)) :=
  (partrec_partialCollect omega hf).map
    ((computable_key value computable_value_eq).comp Computable.snd).to₂
end
end SimpleFInftyOvergroups.EffectiveNames.Polynomial

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_MatrixNames
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.MatrixNames
open BoundedEncoding
noncomputable section
open scoped Classical
variable {A k : Type*} [CommRing k] {n : ℕ}

variable {m : ℕ} (C : WordCalculus (FreeMonoid A) m)

variable [Primcodable A] [Primcodable k] [Finite k]

def partialColumnKey (omega : List A) (f : List A → Part (List A)) (x : Column k A n) :
    Part (Fin n → ℕ) := Finite.traverse (Polynomial.partialKey omega f) x

def partialMatrixKey (omega : List A) (f : List A → Part (List A)) (a : Name k A n) :
    Part (Fin n → Fin n → ℕ) := Finite.traverse (partialColumnKey omega f) a

variable {P : Type*} [Primcodable P] {f : P → List A → Part (List A)}

 theorem partrec_partialColumnKey (omega : List A) (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => partialColumnKey (k:=k) (n:=n) omega (f p)) :=
  Finite.partrec_traverse (Polynomial.partrec_partialKey omega hf)

 theorem partrec_partialMatrixKey (omega : List A) (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => partialMatrixKey (k:=k) (n:=n) omega (f p)) :=
  Finite.partrec_traverse (partrec_partialColumnKey omega hf)

end
end SimpleFInftyOvergroups.EffectiveNames.MatrixNames

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_MatrixWords
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.MatrixWords
open BoundedEncoding MatrixNames
noncomputable section
open scoped Classical
variable {A k : Type*} [CommRing k] {n : ℕ}

def rootValue (r : Root k A n) : V k A n :=
  if h : r.1 ≠ r.2.1 then FiniteAlgebraicEnvelopes.Steinberg.elementary r.1 r.2.1 h (Polynomial.value r.2.2)
  else 1

def groupValue (w : Word k A n) : V k A n := (w.map rootValue).prod

@[simp] theorem groupValue_nil : groupValue ([] : Word k A n) = 1 := rfl
@[simp] theorem groupValue_cons (r : Root k A n) (w : Word k A n) :
    groupValue (r::w) = rootValue r * groupValue w := rfl
@[simp] theorem groupValue_append (a b : Word k A n) :
    groupValue (a++b) = groupValue a * groupValue b := by simp [groupValue]

@[simp] theorem rootValue_inv (r : Root k A n) : rootValue (rootInv r) = (rootValue r)⁻¹ := by
  by_cases h : r.1 ≠ r.2.1
  · simp only [rootValue,rootInv,dite_eq_left h,Polynomial.value_negate]
    apply Units.ext
    simp only [FiniteAlgebraicEnvelopes.Steinberg.elementary_val,
      FiniteAlgebraicEnvelopes.Steinberg.elementary_inv_val,
      Matrix.single_neg,sub_eq_add_neg]
  · simp [rootValue,rootInv,h]

@[simp] theorem inverse_nil : inverse ([] : Word k A n) = [] := rfl
@[simp] theorem inverse_cons (r : Root k A n) (w : Word k A n) :
    inverse (r::w) = inverse w ++ [rootInv r] := by simp [inverse]

@[simp] theorem groupValue_inverse (w : Word k A n) : groupValue (inverse w) = (groupValue w)⁻¹ := by
  induction w with
  | nil => simp
  | cons r w ih => simp [ih,mul_inv_rev]

def gcost (grade : List A → ℕ) (w : Word k A n) : ℕ :=
  (w.map (fun r => Polynomial.cost grade r.2.2)).sum

def xcost (grade : List A → ℕ) (x : Point k A n) : ℕ :=
  gcost grade x.1 + columnCost grade x.2

omit [CommRing k] in
@[simp] theorem gcost_nil [CommRing k] (grade : List A → ℕ) : gcost grade ([] : Word k A n) = 0 := rfl
omit [CommRing k] in
@[simp] theorem gcost_cons [CommRing k] (grade : List A → ℕ) (r : Root k A n) (w : Word k A n) :
    gcost grade (r::w) = Polynomial.cost grade r.2.2 + gcost grade w := rfl
omit [CommRing k] in
@[simp] theorem gcost_append [CommRing k] (grade : List A → ℕ) (a b : Word k A n) :
    gcost grade (a++b) = gcost grade a + gcost grade b := by simp [gcost]
@[simp] theorem gcost_inverse (grade : List A → ℕ) (w : Word k A n) :
    gcost grade (inverse w) = gcost grade w := by
  simp [gcost,inverse,List.map_map,Function.comp_def,rootInv]

def nameOperations (grade : List A → ℕ) : NamedAction.Operations (Word k A n) (Point k A n) where
  one := []
  mul := (·++·)
  inv := inverse
  act := fun g x => (g++x.1,x.2)
  gcost := gcost grade
  xcost := xcost grade
  cost_one := rfl
  cost_mul := gcost_append grade
  cost_inv := gcost_inverse grade
  cost_act := by intros; simp [xcost,gcost_append,Nat.add_assoc]

attribute [local instance] WordCalculus.rawMatrixAction

def pointValue (x : Point k A n) : Fin n → Raw k A := groupValue x.1 • columnValue x.2

@[simp] theorem pointValue_act (g : Word k A n) (x : Point k A n) :
    pointValue (g++x.1,x.2) = groupValue g • pointValue x := by
  simp only [pointValue,groupValue_append,mul_smul]

def rootMatrix (r : Root k A n) : Name k A n := fun i j =>
  oneName i j ++ if r.1 ≠ r.2.1 ∧ r.1=i ∧ r.2.1=j then r.2.2 else []

def matrix (w : Word k A n) : Name k A n := w.foldr (fun r a => product (rootMatrix r) a) oneName

def column (x : Point k A n) : Column k A n := mulVec (matrix x.1) x.2

@[simp] theorem value_rootMatrix (r : Root k A n) : value (rootMatrix r) = (rootValue r).val := by
  funext i j
  change Polynomial.value (oneName i j ++ _) = _
  rw [Polynomial.value_append]
  have hh : Polynomial.value (oneName (k:=k) (A:=A) i j) = (1 : Matrix (Fin n) (Fin n) (Raw k A)) i j :=
    congrFun (congrFun value_oneName i) j
  rw [hh]
  by_cases h : r.1 ≠ r.2.1
  · simp only [rootValue,dite_eq_left h,FiniteAlgebraicEnvelopes.Steinberg.elementary_val,
      Matrix.add_apply,Matrix.single_apply]
    by_cases he : r.1=i ∧ r.2.1=j
    · rw [ite_eq_left ⟨h,he⟩,ite_eq_left he]
    · rw [ite_eq_right (fun hh => he hh.2),ite_eq_right he]
      rfl
  · simp [rootValue,h]

@[simp] theorem value_matrix (w : Word k A n) : value (matrix w) = (groupValue w).val := by
  induction w with
  | nil => exact value_oneName
  | cons r w ih =>
    change value (product (rootMatrix r) (matrix w)) = _
    simp only [value_product,value_rootMatrix,ih,groupValue_cons,Units.val_mul]

@[simp] theorem value_column (x : Point k A n) : columnValue (column x) = pointValue x := by
  simp only [column,value_mulVec,value_matrix]
  rfl

 theorem cost_rootMatrix (grade : List A → ℕ) (h0 : grade [] = 0) (r : Root k A n) :
    cost grade (rootMatrix r) ≤ Polynomial.cost grade r.2.2 := by
  rw [cost,maximum_le_iff]
  intro i
  rw [columnCost,maximum_le_iff]
  intro j
  change Polynomial.cost grade (oneName i j ++ _) ≤ _
  rw [Polynomial.cost_append,max_le_iff]
  constructor
  · have hh := entry_cost_le grade (oneName : Name k A n) i j
    rw [cost_oneName grade h0] at hh
    omega
  · split_ifs <;> simp

 theorem cost_matrix (grade : List A → ℕ) (h0 : grade [] = 0)
    (ha : ∀ u v, grade (u++v) = grade u + grade v) (w : Word k A n) :
    cost grade (matrix w) ≤ gcost grade w := by
  induction w with
  | nil => simpa [matrix] using (cost_oneName (k:=k) (n:=n) grade h0).le
  | cons r w ih =>
    change cost grade (product (rootMatrix r) (matrix w)) ≤
      Polynomial.cost grade r.2.2 + gcost grade w
    exact (cost_product_le grade ha _ _).trans (Nat.add_le_add (cost_rootMatrix grade h0 r) ih)

 theorem cost_column (grade : List A → ℕ) (h0 : grade [] = 0)
    (ha : ∀ u v, grade (u++v) = grade u + grade v) (x : Point k A n) :
    columnCost grade (column x) ≤ xcost grade x :=
  (cost_mulVec_le grade ha _ _).trans
    (Nat.add_le_add_right (cost_matrix grade h0 ha x.1) _)

end
end SimpleFInftyOvergroups.EffectiveNames.MatrixWords

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_MatrixEffective
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.MatrixWords
open BoundedEncoding MatrixNames
noncomputable section
open scoped Classical
variable {A k : Type*} [CommRing k] {n m : ℕ}
variable [Primcodable A] [Primcodable k] [Finite k]
attribute [local instance] WordCalculus.rawMatrixAction

def pairedKey (x : Matrix (Fin n) (Fin n) (Raw k A) × Matrix (Fin n) (Fin n) (Raw k A)) :=
  (matrixKey x.1,matrixKey x.2)

omit [Finite k] in
 theorem pairedKey_injective [Finite k] : Function.Injective (pairedKey (k:=k) (A:=A) (n:=n)) := by
  intro x y h
  exact Prod.ext (matrixKey_injective (congrArg Prod.fst h))
    (matrixKey_injective (congrArg Prod.snd h))

def partialGroupKey (omega : List A) (f : List A → Part (List A)) (w : Word k A n) :
    Part ((Fin n → Fin n → ℕ) × (Fin n → Fin n → ℕ)) :=
  (partialMatrixKey omega f (matrix w)).bind fun a =>
    (partialMatrixKey omega f (matrix (inverse w))).map (fun b => (a,b))

def partialPointKey (omega : List A) (f : List A → Part (List A)) (x : Point k A n) :
    Part (Fin n → ℕ) := partialColumnKey omega f (column x)

 theorem primrec_rootInv : Primrec (rootInv (k:=k) (A:=A) (n:=n)) :=
  Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
    (Polynomial.primrec_negate.comp (Primrec.snd.comp Primrec.snd)))

 theorem primrec_inverse : Primrec (inverse (k:=k) (A:=A) (n:=n)) :=
  Primrec.list_map Primrec.list_reverse (primrec_rootInv.comp Primrec.snd).to₂

omit [Finite k] in
 theorem primrec_rootMatrix [Finite k] : Primrec (rootMatrix (k:=k) (A:=A) (n:=n)) := by
  apply Finite.primrec_function
  intro i
  apply Finite.primrec_function
  intro j
  have ht : PrimrecPred (fun r : Root k A n => r.1 ≠ r.2.1 ∧ r.1=i ∧ r.2.1=j) :=
    ((Primrec.dom_finite fun p : Fin n × Fin n => decide (p.1 ≠ p.2 ∧ p.1=i ∧ p.2=j)).comp
      (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))).primrecPred
  exact Primrec.list_append.comp (Primrec.const (oneName i j))
    (Primrec.ite ht (Primrec.snd.comp Primrec.snd) (Primrec.const []))

 theorem primrec_matrix : Primrec (matrix (k:=k) (A:=A) (n:=n)) :=
  Primrec.list_foldr Primrec.id (Primrec.const oneName)
    (MatrixNames.primrec_product.comp (primrec_rootMatrix.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

 theorem primrec_column : Primrec (column (k:=k) (A:=A) (n:=n)) :=
  primrec_mulVec.comp (primrec_matrix.comp Primrec.fst) Primrec.snd

omit [CommRing k] [Finite k] in
 theorem primrec_gcost [CommRing k] [Finite k] {grade : List A → ℕ} (hg : Primrec grade) :
    Primrec (gcost (k:=k) (n:=n) grade) := by
  have hs : Primrec (fun l : List ℕ => l.sum) :=
    (Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      (fun _ => rfl)
  exact hs.comp (Primrec.list_map Primrec.id
    ((Polynomial.primrec_cost hg).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂)

 theorem primrec_xcost {grade : List A → ℕ} (hg : Primrec grade) :
    Primrec (xcost (k:=k) (n:=n) grade) :=
  Primrec.nat_add.comp ((primrec_gcost hg).comp Primrec.fst)
    ((primrec_columnCost hg).comp Primrec.snd)

variable {P : Type*} [Primcodable P] {f : P → List A → Part (List A)}
 theorem partrec_partialGroupKey (omega : List A) (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => partialGroupKey (k:=k) (n:=n) omega (f p)) := by
  have hp : Partrec (fun p : P × Word k A n => partialMatrixKey omega (f p.1) (matrix p.2)) :=
    (partrec_partialMatrixKey omega hf).comp Computable.fst (primrec_matrix.to_comp.comp Computable.snd)
  apply hp.bind
  have hi : Partrec (fun p : (P × Word k A n) × (Fin n → Fin n → ℕ) =>
      partialMatrixKey omega (f p.1.1) (matrix (inverse p.1.2))) :=
    (partrec_partialMatrixKey omega hf).comp (Computable.fst.comp Computable.fst)
      (primrec_matrix.to_comp.comp (primrec_inverse.to_comp.comp (Computable.snd.comp Computable.fst)))
  exact (hi.map ((Computable.snd.comp Computable.fst).pair Computable.snd).to₂).to₂

 theorem partrec_partialPointKey (omega : List A) (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => partialPointKey (k:=k) (n:=n) omega (f p)) :=
  (partrec_partialColumnKey omega hf).comp Computable.fst (primrec_column.to_comp.comp Computable.snd)

end
end SimpleFInftyOvergroups.EffectiveNames.MatrixWords

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_DoubleEffective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Double
open BoundedEncoding NamedAction
noncomputable section
open scoped Classical

variable {A k₀ k₁ k₂ P₁ P₂ : Type*}
  [CommRing k₀] [CommRing k₁] [CommRing k₂]
  [Primcodable A] [Primcodable k₀] [Primcodable k₁] [Primcodable k₂]
  [Finite k₀] [Finite k₁] [Finite k₂]
  [Primcodable P₁] [Primcodable P₂] [Finite P₁] [Finite P₂]
  {n : ℕ}

abbrev G₀ (k A : Type*) (n : ℕ) := MatrixWords.Word k A n
abbrev X₀ (k A : Type*) (n : ℕ) := MatrixWords.Point k A n
attribute [local instance] WordCalculus.rawMatrixAction

end
end SimpleFInftyOvergroups.EffectiveNames.Double

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EffectiveTables
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes FiniteAlgebraicEnvelopes.Bootstrap

namespace CodedSearch
variable {A S Q : Type*} [DecidableEq S] [DecidableEq Q]
variable {r : S → S → Prop} [DecidableRel (List.Shortlex r)]
variable (C : DelimiterCode A S)

def compute (E : FiniteSearch C) (z : S) (f : List A → Part (Option Q)) (n : ℕ) :
    Part (List (List S × List S)) :=
  (Effect.traverse (fun w => (f w).map (w,·)) (E.words n)).map
    (Uniform.table C.encode (lt (r := r) C) z)

variable (wf : WellFounded r) [Std.Trichotomous r] (q : List A → Option Q)

omit [DecidableEq S] [Std.Trichotomous r] in
theorem pick_class {ps : List (List A × Option Q)} {w v : List A}
    (hps : ∀ p ∈ ps, p.2 = q p.1) (hv : q v = q w) :
    q (Uniform.pick (lt (r := r) C) ps v (q w)) = q w := by
  induction ps generalizing v with
  | nil => exact hv
  | cons p ps ih =>
    simp only [Uniform.pick, List.foldl_cons]
    apply ih (fun p hp => hps p (List.mem_cons_of_mem _ hp))
    simp only [Uniform.pickStep]
    split
    next h => exact (hps p List.mem_cons_self).symm.trans h.1
    next h => exact hv

omit [DecidableEq S] in
theorem pick_least_fixed {ps : List (List A × Option Q)} {w : List A}
    (hps : ∀ p ∈ ps, p.2 = q p.1) :
    Uniform.pick (lt (r := r) C) ps (EncodedCanonical.least C wf q w) (q w) =
      EncodedCanonical.least C wf q w := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hh : ¬ (p.2 = q w ∧ lt (r := r) C p.1 (EncodedCanonical.least C wf q w) = true) := by
      rintro ⟨hq, hr⟩
      exact EncodedCanonical.least_global_min C wf q
        ((hps p List.mem_cons_self).symm.trans hq) (of_decide_eq_true hr)
    simp only [Uniform.pick, List.foldl_cons, Uniform.pickStep, ite_eq_right hh]
    exact ih (fun p hp => hps p (List.mem_cons_of_mem _ hp))

omit [DecidableEq S] in
theorem pick_eq_least {ps : List (List A × Option Q)} {w : List A}
    (hps : ∀ p ∈ ps, p.2 = q p.1)
    (hm : (EncodedCanonical.least C wf q w, q w) ∈ ps) :
    Uniform.pick (lt (r := r) C) ps w (q w) = EncodedCanonical.least C wf q w := by
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp hm
  have hb : ∀ p ∈ before, p.2 = q p.1 := fun p hp => hps p (List.mem_append_left _ hp)
  have ha : ∀ p ∈ after, p.2 = q p.1 := fun p hp =>
    hps p (List.mem_append_right _ (List.mem_cons_of_mem _ hp))
  have hclass := pick_class (r := r) C q hb (w := w) rfl
  have hsel : Uniform.pickStep (lt (r := r) C) (q w)
      (Uniform.pick (lt (r := r) C) before w (q w))
      (EncodedCanonical.least C wf q w, q w) = EncodedCanonical.least C wf q w := by
    unfold Uniform.pickStep
    simp only [true_and, lt, decide_eq_true_eq]
    split
    · rfl
    next h =>
      apply C.encode_injective
      exact Std.Trichotomous.trichotomous _ _
        (EncodedCanonical.least_global_min C wf q hclass) h
  simp only [Uniform.pick, List.foldl_append, List.foldl_cons]
  change after.foldl (Uniform.pickStep (lt (r := r) C) (q w))
    (Uniform.pickStep (lt (r := r) C) (q w)
      (Uniform.pick (lt (r := r) C) before w (q w))
      (EncodedCanonical.least C wf q w, q w)) = _
  rw [hsel]
  exact pick_least_fixed C wf q ha

variable (E : FiniteSearch C) (z : S)

omit [DecidableEq S] in
theorem output_full {n : ℕ} {w : List A} (hw : (C.encode w).length ≤ n) :
    Uniform.output C.encode (lt (r := r) C) z
      ((E.words n).map fun v => (v,q v)) (w,q w) = CodeTable.output C wf q z w := by
  have hps : ∀ p ∈ (E.words n).map (fun v => (v,q v)), p.2 = q p.1 := by
    intro p hp
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hp
    rfl
  have hm : (EncodedCanonical.least C wf q w, q w) ∈ (E.words n).map (fun v => (v,q v)) :=
    List.mem_map.mpr ⟨EncodedCanonical.least C wf q w, (E.mem_words _ _).mpr
      ((EncodedCanonical.least_length C wf q w).trans hw), by simp [EncodedCanonical.least_class]⟩
  simp only [Uniform.output, CodeTable.output, pick_eq_least C wf q hps hm]

theorem table_full (n : ℕ) :
    Uniform.table C.encode (lt (r := r) C) z ((E.words n).map fun v => (v,q v)) =
      CodeTable.table C E wf q z n := by
  classical
  unfold Uniform.table CodeTable.table
  rw [List.flatMap_map]
  have hh : ∀ w ∈ E.words n,
      (if w ≠ [] ∧ Uniform.output C.encode (lt (r := r) C) z
        ((E.words n).map fun v => (v,q v)) (w,q w) ≠ C.encode w
        then [(C.encode w, Uniform.output C.encode (lt (r := r) C) z
          ((E.words n).map fun v => (v,q v)) (w,q w))] else []) =
      (if w ≠ [] ∧ CodeTable.output C wf q z w ≠ C.encode w
        then [(C.encode w, CodeTable.output C wf q z w)] else []) := by
    intro w hw
    rw [output_full C wf q E z ((E.mem_words _ _).mp hw)]
  rw [List.flatMap_congr hh]
  have he (l : List (List A)) :
      l.flatMap (fun w => if w ≠ [] ∧ CodeTable.output C wf q z w ≠ C.encode w
        then [(C.encode w, CodeTable.output C wf q z w)] else []) =
      (l.filter fun w => w ≠ [] ∧ CodeTable.output C wf q z w ≠ C.encode w).map
        (fun w => (C.encode w, CodeTable.output C wf q z w)) := by
    induction l with
    | nil => rfl
    | cons w l ih =>
      by_cases h : w ≠ [] ∧ CodeTable.output C wf q z w ≠ C.encode w
      · simp only [List.flatMap_cons, List.filter_cons, decide_eq_true_eq, ite_eq_left h,
          List.map_cons, List.singleton_append, ih]
      · simp only [List.flatMap_cons, List.filter_cons, decide_eq_true_eq, ite_eq_right h,
          List.nil_append, ih]
  refine (he _).trans ?_
  congr 1
  apply List.filter_congr
  intro w hw
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

theorem compute_full {f : List A → Part (Option Q)} {n : ℕ}
    (h : ∀ w, (C.encode w).length ≤ n → q w ∈ f w) :
    CodeTable.table C E wf q z n ∈ compute (r := r) C E z f n := by
  apply (Part.mem_map_iff _).mpr
  refine ⟨(E.words n).map (fun w => (w,q w)), ?_, table_full C wf q E z n⟩
  apply Search.traverse_map
  intro w hw
  exact (Part.mem_map_iff _).mpr ⟨_, h w ((E.mem_words _ _).mp hw), rfl⟩

omit [Std.Trichotomous r] in
theorem compute_domain {f : List A → Part (Option Q)} {n : ℕ}
    (hc : (compute (r := r) C E z f n).Dom) :
    ∀ w, (C.encode w).length ≤ n → (f w).Dom := by
  obtain ⟨rs, hrs⟩ := Part.dom_iff_mem.mp hc
  obtain ⟨ps, hps, _⟩ := (Part.mem_map_iff _).mp hrs
  have ht := Effect.traverse_domain hps.1
  intro w hw
  obtain ⟨p, hp⟩ := Part.dom_iff_mem.mp (ht w ((E.mem_words _ _).mpr hw))
  obtain ⟨v, hv, _⟩ := (Part.mem_map_iff _).mp hp
  exact hv.1

end CodedSearch

end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_FamilyProgram
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes FiniteAlgebraicEnvelopes.Bootstrap

namespace FamilyProgram
variable {I S : Type*} {A Q : I → Type*} [Fintype I] [Fintype S]
  [DecidableEq S] [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (Q i)]
variable {r : S → S → Prop} [DecidableRel (List.Shortlex r)]
variable (C : ∀ i, DelimiterCode (A i) S) (E : ∀ i, FiniteSearch (C i))
  (z : S) (f : ∀ i, List (A i) → Part (Option (Q i)))

noncomputable def compute (n : ℕ) : Part (List (List S × List S)) :=
  if n = 0 then Part.some (Base.absorption z) else
    (Effect.traverse (fun i => CodedSearch.compute (r := r) (C i) (E i) z (f i) n)
      (Static.letters I)).map (fun rs => Base.absorption z ++ rs.flatten)

omit [∀ index, DecidableEq (A index)] in
@[simp] theorem compute_zero [∀ index, DecidableEq (A index)] :
    compute (r := r) C E z f 0 = Part.some (Base.absorption z) := by
  simp [compute]

variable (wf : WellFounded r) [Std.Trichotomous r]

omit [∀ index, DecidableEq (A index)] [Std.Trichotomous r] in
theorem compute_domain [∀ index, DecidableEq (A index)] [Std.Trichotomous r]
    {n : ℕ} (hn : n ≠ 0)
    (h : (compute (r := r) C E z f n).Dom) :
    ∀ i w, (C i |>.encode w).length ≤ n → (f i w).Dom := by
  rw [compute, ite_eq_right hn] at h
  obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp h
  obtain ⟨rs, hrs, _⟩ := (Part.mem_map_iff _).mp ho
  intro i
  exact CodedSearch.compute_domain (C i) (E i) z
    (Effect.traverse_domain hrs.1 i (by simp [Static.letters]))

end FamilyProgram
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EffectiveFamilies
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes Bootstrap
noncomputable section
open scoped Classical

namespace FiniteParameter
variable {I X Y : Type*} [Primcodable I] [Primcodable X] [Primcodable Y]
  [DecidableEq I] (f : I → X → Part Y)

theorem partrec₂ [Fintype I] (hf : ∀ i, Partrec (f i)) : Partrec₂ f :=
  (select_partrec f hf (Static.letters I)).of_eq (fun p => select_mem f _ p (by simp [Static.letters]))
end FiniteParameter

end
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ContextualCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding.Source
noncomputable section
open FiniteAlgebraicEnvelopes Bootstrap Compiler Compiler.Simulator MachineRealization
open BoundedEncoding NamedAction
open scoped Classical

variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable {Γ Q P₁ P₂ : Type} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q] [Primcodable P₁] [Primcodable P₂] [Finite P₁] [Finite P₂]

local instance instPrimcodableZModOfNatNat_solutions : Primcodable (ZMod 2) := Effect.finitePrimcodable _
local instance instPrimcodableZModOfNatNat_solutions_1 : Primcodable (ZMod 3) := Effect.finitePrimcodable _

end
end SimpleFInftyOvergroups.ContextualEncoding.Source

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_RingAssemblyTools
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Contracted.countableAlgebra _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SimpleFInftyOvergroups.RingAssembly
open scoped Classical TensorProduct
open FiniteAlgebraicEnvelopes

section Contracted
variable {k M : Type*} [CommRing k] [Nontrivial k] [MonoidWithZero M]

 theorem monoidBasis_injective : Function.Injective (ContractedPresentation.monoidBasis k (M:=M)) := by
  intro x y hxy
  change Contracted.basis k M x 1=Contracted.basis k M y 1 at hxy
  by_contra hne
  by_cases hx : x=0
  · have hy : y≠0 := by intro hy; exact hne (hx.trans hy.symm)
    have hh := congrArg (Contracted.coefficient (k:=k) y hy) hxy
    simp [Contracted.coefficient_basis,Ne.symm hne] at hh
  · have hh := congrArg (Contracted.coefficient (k:=k) x hx) hxy
    simp [Contracted.coefficient_basis,hne] at hh

def monoidBasis₀ : M →*₀ Contracted.Algebra k M :=
  { ContractedPresentation.monoidBasis k with map_zero' := Contracted.basis_zero k M 1 }
end Contracted

end SimpleFInftyOvergroups.RingAssembly
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SemanticActionMonoid
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical
namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding NamedAction
namespace SemanticActionMonoid

variable {G X V Y K L : Type*} [Group V] [MulAction V Y] {m : ℕ}
  {N : Operations G X} {C : ActionCalculus V Y K L m} (I : Interpretation N C)

abbrev groupValue (g : G) : V := (I.group g).val
abbrev pointValue (x : X) : Y := (I.point x).val

def letter : Letter G X → SourceActionMonoid.Generator V Y
  | .inl g => .grp (groupValue I g)
  | .inr (.inl x) => .pre (pointValue I x)
  | .inr (.inr (some x)) => .delete (pointValue I x)
  | .inr (.inr none) => .zero

def wordMap : FreeMonoid (Letter G X) →* SourceActionMonoid.M V Y :=
  (PresentedMonoid.mk (SourceActionMonoid.Relation V Y)).comp
    (FreeMonoid.lift (fun a => FreeMonoid.of (letter I a)))

def formValue : Form G X → SourceActionMonoid.Algorithm.Form (V:=V) (Z:=Y) :=
  Operations.formKey (groupValue I) (pointValue I)

 theorem formKey_injective {G X : Type*} {kg : G → K} {kx : X → L}
    (hg : Function.Injective kg) (hx : Function.Injective kx) :
    Function.Injective (Operations.formKey kg kx) := by
  apply Option.map_injective
  intro a b h
  apply Prod.ext
  · exact (List.map_injective_iff.mpr hx) (congrArg Prod.fst h)
  · apply Prod.ext
    · exact hg (congrArg (fun p => p.2.1) h)
    · exact (List.map_injective_iff.mpr hx) (congrArg (fun p => p.2.2) h)

 theorem formKey_comp (f : Form G X) :
    Operations.formKey C.group.key C.point.key (formValue I f) =
      Operations.formKey I.gkey I.xkey f := by
  cases f with
  | none => rfl
  | some p => simp only [Operations.formKey,formValue,Option.map_some,List.map_map]; rfl

variable [DecidableEq L]

 theorem formValue_step (hx : Function.Injective C.point.key)
    (a : Letter G X) (f : Form G X) :
    formValue I (N.totalStep I.xkey a f) =
      SourceActionMonoid.Algorithm.step (letter I a) (formValue I f) := by
  have hone : groupValue I N.one = 1 := congrArg WithBound.val I.one
  have hmul g h : groupValue I (N.mul g h) = groupValue I g * groupValue I h :=
    congrArg WithBound.val (I.mul g h)
  have hinv g : groupValue I (N.inv g) = (groupValue I g)⁻¹ :=
    congrArg WithBound.val (I.inv g)
  have hact g x : pointValue I (N.act g x) = groupValue I g • pointValue I x :=
    congrArg WithBound.val (I.act g x)
  have hkey x y : I.xkey x = I.xkey y ↔ pointValue I x = pointValue I y := hx.eq_iff
  cases f with
  | none => cases a <;> rfl
  | some p =>
    rcases p with ⟨l,g,r⟩
    rcases a with h | (x | y)
    · cases l <;> simp [Operations.totalStep,Operations.plan,formValue,Operations.formKey,
        letter,SourceActionMonoid.Algorithm.step,hmul,hact]
    · rfl
    · cases y with
      | none => rfl
      | some y =>
        cases l with
        | nil => simp [Operations.totalStep,Operations.plan,formValue,Operations.formKey,
            letter,SourceActionMonoid.Algorithm.step,hone,hact,hinv]
        | cons x l =>
          by_cases h : I.xkey y = I.xkey x
          · simp [Operations.totalStep,Operations.plan,formValue,Operations.formKey,
              letter,SourceActionMonoid.Algorithm.step,h,(hkey y x).mp h]
          · simp [Operations.totalStep,Operations.plan,formValue,Operations.formKey,
              letter,SourceActionMonoid.Algorithm.step,h,mt (hkey y x).mpr h]

 theorem formValue_normalize (hx : Function.Injective C.point.key) (w : List (Letter G X)) :
    formValue I (N.totalNormalize I.xkey w) = SourceActionMonoid.Algorithm.normalize (w.map (letter I)) := by
  induction w with
  | nil =>
    change some ([],groupValue I N.one,[]) = some ([],1,[])
    rw [show groupValue I N.one = 1 from congrArg WithBound.val I.one]
  | cons a w ih =>
    change formValue I (N.totalStep I.xkey a (N.totalNormalize I.xkey w)) = _
    rw [formValue_step I hx,ih]
    rfl

omit [DecidableEq L] in
 theorem wordMap_ofList (w : List (Letter G X)) :
    wordMap I (FreeMonoid.ofList w) =
      PresentedMonoid.mk (SourceActionMonoid.Relation V Y) (FreeMonoid.ofList (w.map (letter I))) := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [FreeMonoid.ofList_cons,map_mul,List.map_cons,ih]; rfl

 theorem totalTest_eq_iff (hg : Function.Injective C.group.key) (hx : Function.Injective C.point.key)
    (u v : List (Letter G X)) :
    N.totalTest I.gkey I.xkey u = N.totalTest I.gkey I.xkey v ↔
      wordMap I (FreeMonoid.ofList u) = wordMap I (FreeMonoid.ofList v) := by
  change Operations.formKey I.gkey I.xkey _ = Operations.formKey I.gkey I.xkey _ ↔ _
  rw [← formKey_comp I,← formKey_comp I,(formKey_injective hg hx).eq_iff,
    formValue_normalize I hx,formValue_normalize I hx,wordMap_ofList,wordMap_ofList]
  exact (SourceActionMonoid.Algorithm.word_eq_iff _ _).symm

omit [DecidableEq L] in
 theorem wordMap_surjective (hg : Function.Surjective (groupValue I))
    (hx : Function.Surjective (pointValue I)) : Function.Surjective (wordMap I) := by
  have hl : Function.Surjective (letter I) := by
    intro a
    cases a with
    | grp g => obtain ⟨a,rfl⟩ := hg g; exact ⟨.inl a,rfl⟩
    | pre y => obtain ⟨a,rfl⟩ := hx y; exact ⟨.inr (.inl a),rfl⟩
    | delete y => obtain ⟨a,rfl⟩ := hx y; exact ⟨.inr (.inr (some a)),rfl⟩
    | zero => exact ⟨.inr (.inr none),rfl⟩
  intro z
  obtain ⟨v,rfl⟩ := PresentedMonoid.surjective_mk z
  obtain ⟨w,hw⟩ := (List.map_surjective_iff.mpr hl) v.toList
  refine ⟨FreeMonoid.ofList w,?_⟩
  rw [wordMap_ofList,hw,FreeMonoid.ofList_toList]

end SemanticActionMonoid
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SemanticActions
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical
namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding EffectiveNames

def globalCalculus {V Y K L : Type*} [Group V] [MulAction V Y]
    (kg : V → K) (kx : Y → L) (hg : Function.Injective kg) (hx : Function.Injective kx)
    (m : ℕ) : ActionCalculus V Y K L m where
  group := ⟨fun _ => Set.univ, fun _ _ _ => Set.Subset.refl _, kg⟩
  point := ⟨fun _ => Set.univ, fun _ _ _ => Set.Subset.refl _, kx⟩
  one_mem _ := Set.mem_univ _
  inv_mem _ := Set.mem_univ _
  mul_mem _ _ := Set.mem_univ _
  smul_mem _ _ := Set.mem_univ _
  inv_congr h := congrArg (fun v => kg v⁻¹) (hg h)
  mul_congr _ _ _ _ _ _ h h' := by rw [hg h,hg h']
  smul_congr _ _ _ _ _ _ h h' := by rw [hg h,hx h']

end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_TwoEnlargements
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SourceEnlargement

section OneLayer
variable (K : Type) [CommRing K]
variable (V Z : Type) [Group V] [MulAction V Z]

abbrev enlargedSet := Z →₀ BinaryPrefixOperators.algebra K

variable {V Z}

def pointEmbedding (z : Z) : enlargedSet K Z := Finsupp.single z 1

end OneLayer

namespace Saturation
variable {W X Y : Type} [Group W] [MulAction W Y] (t : X → Y)

def point (x : X) : carrier (W := W) t := ⟨t x, 1, x, one_smul W (t x)⟩

end Saturation

namespace Double
variable (Q X : Type) [Group Q] [MulAction Q X]

abbrev Y₁ := enlargedSet (ZMod 2) X
abbrev AmbientY := enlargedSet (ZMod 3) (Y₁ X)

variable {Q X}

def ambientPoint (x : X) : AmbientY X :=
  pointEmbedding (ZMod 3) (pointEmbedding (ZMod 2) x)

end Double
end SourceEnlargement
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SemanticDouble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical
namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding EffectiveNames NamedAction SourceEnlargement
namespace SemanticDouble

local instance instPrimcodableZModOfNatNat_solutions : Primcodable (ZMod 2) := FiniteAlgebraicEnvelopes.Effect.finitePrimcodable _
local instance instPrimcodableZModOfNatNat_solutions_1 : Primcodable (ZMod 3) := FiniteAlgebraicEnvelopes.Effect.finitePrimcodable _

end SemanticDouble
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SemanticTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical

namespace SourceActionMonoid
variable {V Y : Type*} [Group V] [MulAction V Y]
instance monoidWithZero : MonoidWithZero (M V Y) where
  __ := (inferInstance : Monoid (M V Y))
  zero := omega
  zero_mul := omega_mul
  mul_zero := mul_omega
end SourceActionMonoid

namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding EffectiveNames NamedAction StageConstruction
namespace SemanticTests
local instance instPrimcodableZModOfNatNat_solutions : Primcodable (ZMod 2) := FiniteAlgebraicEnvelopes.Effect.finitePrimcodable _
local instance instPrimcodableZModOfNatNat_solutions_1 : Primcodable (ZMod 3) := FiniteAlgebraicEnvelopes.Effect.finitePrimcodable _

end SemanticTests
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
end


