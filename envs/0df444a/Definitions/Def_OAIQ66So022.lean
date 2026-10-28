-- Prove2me | Definitions.Def_OAIQ66So022
-- name    : OAIQ66So022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:27:39.052379+00:00
-- url     : https://prove2.me/theorems/3fd2a169-383d-40b0-a3d3-0bad353481f5
-- title:
--   Definitions bundle OAIQ66So022 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 8 definitions, 1 inductive type or structure and 10 theorems. The definitions and types are `OAI.TwistedBrin.Basis.grid`, `OAI.TwistedBrin.Basis.ofPartition`, `OAI.TwistedBrin.Basis.transition`, `OAI.TwistedBrin.Basis.transitionElement`, `OAI.TwistedBrin.HasTable`, `OAI.TwistedBrin.IsPartition`, `OAI.TwistedBrin.Prefix.gridPoint`, `OAI.TwistedBrin.Prefix.gridPrefix`, `OAI.TwistedBrin.Table`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`FiniteType_ProductGroupHomology`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/ProductGroupHomology.lean), [`FiniteType_TwistedBrinRangeChartRestricts`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrinRangeChartRestricts.lean).
--
--   **Imports.** It imports the bundles `OAIQ66So002` and `OAIQ66So015` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ66So026`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So002
import Definitions.Def_OAIQ66So015

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductGroupHomology
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.LocalEmbedding.instCoeFunForallBox
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

namespace Prefix
variable {S : Type u}
lemma brick_append_subset (p q : Prefix S) : (append p q).brick ⊆ p.brick := by
  rintro _ ⟨x,rfl⟩
  rw [chart_append]
  exact chart_mem_brick _ _

lemma brick_subset_of_extends {p r : Prefix S} (h : Extends p r) : r.brick ⊆ p.brick := by
  rw [← append_suffix h]
  exact brick_append_subset p (suffix p r)

end Prefix

end TwistedBrin

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma extends_of_mem_of_length_le {p r : Prefix S} {x : Box S}
    (hp : x ∈ p.brick) (hr : x ∈ r.brick) (hl : ∀ s, (p s).length ≤ (r s).length) :
    Extends p r := by
  intro s
  have hp' := (mem_brick_iff p x).mp hp s
  have hr' := (mem_brick_iff r x).mp hr s
  rw [← hp',← hr']
  exact Stream'.take_prefix_take_left _ _ _ (hl s)

end TwistedBrin.Prefix

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

def IsPartition {I : Type*} (p : I → Prefix S) : Prop :=
  ∀ x : Box S, ∃! i : I, x ∈ (p i).brick

structure Table where
  size : ℕ
  dom : Fin size → Prefix S
  ran : Fin size → Prefix S
  label : Fin size → A
  dom_partition : IsPartition dom
  ran_partition : IsPartition ran

def HasTable (f : Equiv.Perm (Box S)) : Prop :=
  ∃ T : Table (A := A) (S := S), ∀ i y,
    f ((T.dom i).chart y) = (T.ran i).chart (twist ρ (T.label i) y)

end

end TwistedBrin

namespace TwistedBrin.Prefix
variable {S : Type u}

noncomputable def gridPrefix (b : S →₀ ℕ) (z : Grid b) : Prefix S := by
  classical
  exact {
    word := fun s => if hs : s ∈ b.support then List.ofFn (z ⟨s,hs⟩) else []
    finite_support := b.support.finite_toSet.subset (by
      intro s hs
      change s ∈ b.support
      by_contra hn
      change (if h : s ∈ b.support then List.ofFn (z ⟨s,h⟩) else []) ≠ [] at hs
      rw [dite_eq_right hn] at hs
      exact hs rfl) }

lemma gridPrefix_length (b : S →₀ ℕ) (z : Grid b) (s : S) :
    (gridPrefix b z s).length = b s := by
  classical
  by_cases hs : s ∈ b.support
  · simp only [gridPrefix,dite_eq_left hs,List.length_ofFn]
  · simp only [gridPrefix,dite_eq_right hs,List.length_nil,Finsupp.notMem_support_iff.mp hs]

lemma gridPrefix_get (b : S →₀ ℕ) (z : Grid b) (s : b.support) (n : Fin (b s)) :
    (gridPrefix b z s)[n.val]'(by rw [gridPrefix_length]; exact n.isLt) = z s n := by
  classical
  simp only [gridPrefix,dite_eq_left s.property,List.getElem_ofFn]

noncomputable def gridPoint (b : S →₀ ℕ) (x : Box S) : Grid b :=
  fun s n => (x s).get n

lemma mem_gridPrefix (b : S →₀ ℕ) (x : Box S) :
    x ∈ (gridPrefix b (gridPoint b x)).brick := by
  classical
  apply (mem_brick_iff_get _ _).mpr
  intro s n hn
  have hn' : n < b s := by simpa only [gridPrefix_length] using hn
  have hs : s ∈ b.support := Finsupp.mem_support_iff.mpr (by omega)
  exact (gridPrefix_get b (gridPoint b x) ⟨s,hs⟩ ⟨n,hn'⟩).symm

lemma eq_gridPoint_of_mem {b : S →₀ ℕ} {z : Grid b} {x : Box S}
    (hx : x ∈ (gridPrefix b z).brick) : z = gridPoint b x := by
  funext s n
  have h := (mem_brick_iff_get _ _).mp hx s n (by rw [gridPrefix_length]; exact n.isLt)
  rw [gridPrefix_get] at h
  exact h.symm

lemma grid_partition (b : S →₀ ℕ) : TwistedBrin.IsPartition (gridPrefix b) := by
  intro x
  exact ⟨gridPoint b x,mem_gridPrefix b x,fun z hz => eq_gridPoint_of_mem hz⟩

end TwistedBrin.Prefix

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
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

noncomputable def ofPartition {I : Type*} [Fintype I] (p : I → Prefix S)
    (hp : IsPartition p) : Basis ρ := by
  classical
  let j := fun i => GermBrick.mk ρ (LocalEmbedding.ofPrefix ρ (p i))
  exact {
    pieces := Finset.univ.image j
    partition := by
      intro x
      obtain ⟨i,hi,hu⟩ := hp x
      refine ⟨⟨j i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩,hi,?_⟩
      intro b hb
      obtain ⟨k,_,hk⟩ := Finset.mem_image.mp b.property
      apply Subtype.ext
      have hb' : x ∈ (p k).brick := by
        change x ∈ GermBrick.region ρ b.1 at hb
        rwa [← hk] at hb
      exact hk.symm.trans (congrArg j (hu k hb')) }

noncomputable def grid (b : S →₀ ℕ) : Basis ρ :=
  ofPartition ρ (Prefix.gridPrefix b) (Prefix.grid_partition b)

end Basis
end TwistedBrin

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

namespace Basis

noncomputable def transition {B C : Basis ρ} (e : B ≃ C) : Equiv.Perm (Box S) :=
  (equivalence ρ B).symm.trans ((Equiv.prodCongr e (Equiv.refl _)).trans (equivalence ρ C))

lemma transition_chart {B C : Basis ρ} (e : B ≃ C) (b : B) (x : Box S) :
    transition ρ e (chart ρ B b x) = chart ρ C (e b) x := by
  change equivalence ρ C ((Equiv.prodCongr e (Equiv.refl _))
    ((equivalence ρ B).symm (equivalence ρ B (b,x)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma transition_isLocal {B C : Basis ρ} (e : B ≃ C) : IsLocal ρ (transition ρ e) := by
  apply locallyStandard_of_charts ρ (chart ρ B) (fun b => chart ρ C (e b))
  · intro x
    obtain ⟨⟨b,y⟩,hy⟩ := (equivalence ρ B).surjective x
    exact ⟨b,y,hy⟩
  · exact transition_chart ρ e

noncomputable def transitionElement {B C : Basis ρ} (e : B ≃ C) : localGroup ρ :=
  ⟨transition ρ e,transition_isLocal ρ e⟩

end Basis
end

end TwistedBrin

end

end OAI
end


