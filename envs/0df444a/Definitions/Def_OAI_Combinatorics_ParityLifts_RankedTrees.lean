-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
-- name    : OAI_Combinatorics_ParityLifts_RankedTrees
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:15:04.356568+00:00
-- url     : https://prove2.me/theorems/5590318e-7a87-4716-b332-17ee623a6343
-- title:
--   Ranked trees, ranked bag trees and their topological reindexing
-- statement:
--   This file provides a flexible presentation of rooted trees and tree decompositions on an arbitrary node type, and converts it into the indexed form, with nodes numbered parent-before-child, used by the separator argument.
--
--   1. **Ranked trees.** A ranked tree on a node type $N$ consists of a root $\rho\in N$, a parent map $\mathrm{par}\colon N\to N$ and a rank function $\mathrm{rk}\colon N\to\mathbb{N}$ with $\mathrm{rk}(\mathrm{par}(i))<\mathrm{rk}(i)$ for every $i\ne\rho$. The ancestor relation is defined inductively by $i\preceq i$, and $i\preceq j$ whenever $j\ne\rho$ and $i\preceq\mathrm{par}(j)$. It is transitive, $\rho\preceq j$ for every $j$, and a map $f\colon N\to M$ into another ranked tree preserves $\preceq$ as soon as $f(\mathrm{par}(j))\preceq f(j)$ for every $j\ne\rho$.
--   2. **Topological reindexing.** For finite $N$, the nodes are linearly ordered lexicographically by rank and then by position in a fixed enumeration of $N$. The resulting order isomorphism $\{0,\dots,|N|-1\}\cong N$ turns the ranked tree into an indexed tree in which every parent has a smaller index than its children, and $\preceq$ is both preserved and reflected by this reindexing.
--   3. **Ranked bag trees.** For a relation $R$ on a set $W$ and $t\in\mathbb{N}$, a ranked bag tree is a ranked tree on $N$ together with finite bags $B_i\subseteq W$ and a map $\mathrm{top}\colon W\to N$ such that $x\in B_{\mathrm{top}(x)}$; $x\in B_i$ implies $\mathrm{top}(x)\preceq i$; $\mathrm{top}(x)\preceq i\preceq j$ and $x\in B_j$ imply $x\in B_i$; every pair $x,y$ with $R(x,y)$ lies in a common bag; and
--   $$
--   |B_i|\le t\quad\text{for all } i,\qquad |B_i\cap B_{\mathrm{par}(i)}|<t\quad\text{for all } i\ne\rho .
--   $$
--   4. **Conversion.** For finite $W$ and $N$ and a graph $F$ on $W$, a ranked bag tree for the adjacency relation of $F$ becomes, after topological reindexing of its nodes, a reduced bag tree of $F$ with the same bags.
--
--   Ranks are convenient when trees are assembled from pieces, for example by gluing several trees at a new root, where no global numbering of the nodes is available; the conversion then feeds the result into the cut-based separator argument. Allowing an arbitrary relation $R$, which may have loops, makes the same notion usable for the sources of rooted homomorphism tests. The bag axioms carry no parity or Weisfeiler–Leman condition.
--
--   **Formalization Note** The structures are `RankedTree N` (with `RankedTree.Ancestor`) and `RankedBagTree R t`, whose fields beyond the tree are `bag`, `top`, `top_mem`, `top_ancestor`, `interval_mem`, `edge_cover`, `width`, `intersection`. Item 2 is `nodeOrder`, `enumeration` and `indexed`, with `ancestor_indexed` and `indexed_ancestor`; item 4 is `RankedBagTree.toIndexed`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/RankedTrees.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/RankedTrees.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ParityLifts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection

namespace OAI

namespace ParityWL

open scoped BigOperators

section RankedTrees

open scoped Classical

structure RankedTree (N : Type) where
  root : N
  parent : N → N
  rank : N → ℕ
  parent_lt : ∀ i, i ≠ root → rank (parent i) < rank i

inductive RankedTree.Ancestor {N : Type} (D : RankedTree N) (i : N) : N → Prop
  | refl : D.Ancestor i i
  | step {j : N} (hj : j ≠ D.root) : D.Ancestor i (D.parent j) → D.Ancestor i j

namespace RankedTree

variable {N : Type} (D : RankedTree N)

lemma Ancestor.trans {i j k : N} (h : D.Ancestor i j) (g : D.Ancestor j k) :
    D.Ancestor i k := by
  induction g with
  | refl => exact h
  | step hk g ih => exact .step hk ih

lemma Ancestor.cases' {i j : N} (h : D.Ancestor i j) :
    i = j ∨ (j ≠ D.root ∧ D.Ancestor i (D.parent j)) := by
  cases h with
  | refl => exact Or.inl rfl
  | step h g => exact Or.inr ⟨h, g⟩

lemma root_ancestor (j : N) : D.Ancestor D.root j := by
  by_cases h : j = D.root
  · subst j; exact .refl
  · exact .step h (root_ancestor (D.parent j))
termination_by D.rank j
decreasing_by exact D.parent_lt j h

theorem Ancestor.map {M : Type} (E : RankedTree M) (f : N → M)
    (hstep : ∀ j, j ≠ D.root → E.Ancestor (f (D.parent j)) (f j))
    {i j : N} (h : D.Ancestor i j) : E.Ancestor (f i) (f j) := by
  induction h with
  | refl => exact .refl
  | @step j hj h ih => exact ih.trans E (hstep j hj)

variable [Fintype N]

@[instance_reducible] noncomputable def nodeOrder : LinearOrder N :=
  LinearOrder.lift' (fun i => (toLex (D.rank i, (Fintype.equivFin N i).val))) (by
    intro i j h
    have he : Fintype.equivFin N i = Fintype.equivFin N j := Fin.ext
      (congrArg (fun p : Lex (ℕ × ℕ) => (ofLex p).2) h)
    exact (Fintype.equivFin N).injective he)

noncomputable def enumeration : Fin (Fintype.card N) ≃ N := by
  letI := D.nodeOrder
  exact (Fintype.orderIsoFinOfCardEq N rfl).toEquiv

noncomputable def indexed : IndexedTree where
  nodes := Fintype.card N
  root := D.enumeration.symm D.root
  parent i := D.enumeration.symm (D.parent (D.enumeration i))
  parent_lt i hi := by
    let := D.nodeOrder
    change (Fintype.orderIsoFinOfCardEq N rfl).symm
      (D.parent ((Fintype.orderIsoFinOfCardEq N rfl) i)) < i
    rw [OrderIso.symm_apply_lt]
    change Prod.Lex (· < ·) (· < ·)
      (D.rank (D.parent _), _) (D.rank _, _)
    apply Prod.Lex.left
    apply D.parent_lt
    intro he
    apply hi
    apply D.enumeration.injective
    simpa only [enumeration, Equiv.apply_symm_apply, OrderIso.coe_toEquiv] using he

lemma ancestor_indexed {i j : N} (h : D.Ancestor i j) :
    D.indexed.Ancestor (D.enumeration.symm i) (D.enumeration.symm j) := by
  induction h with
  | refl => exact .refl
  | @step j hj h ih =>
    apply IndexedTree.Ancestor.step
    · intro he
      apply hj
      exact D.enumeration.symm.injective he
    · simpa only [indexed, Equiv.apply_symm_apply] using ih

lemma indexed_ancestor {i j : Fin (Fintype.card N)} (h : D.indexed.Ancestor i j) :
    D.Ancestor (D.enumeration i) (D.enumeration j) := by
  have hm : ∀ (T : IndexedTree) (f : Fin T.nodes → N),
      (∀ j, j ≠ T.root → D.Ancestor (f (T.parent j)) (f j)) →
      ∀ i j, T.Ancestor i j → D.Ancestor (f i) (f j) := by
    intro T f hf i j h
    induction h with
    | refl => exact .refl
    | @step j hj h ih => exact ih.trans D (hf j hj)
  apply hm D.indexed D.enumeration _ i j h
  intro j hj
  apply Ancestor.step
  · intro he
    apply hj
    apply D.enumeration.injective
    simpa only [indexed, Equiv.apply_symm_apply] using he
  · simp only [indexed, Equiv.apply_symm_apply]
    exact .refl

end RankedTree

/-- This records ordinary bag axioms, not lift solvability or any WL promise. -/
structure RankedBagTree {W N : Type} (R : W → W → Prop) (t : ℕ) extends RankedTree N where
  bag : N → Finset W
  top : W → N
  top_mem : ∀ x, x ∈ bag (top x)
  top_ancestor : ∀ x i, x ∈ bag i → toRankedTree.Ancestor (top x) i
  interval_mem : ∀ x i j, toRankedTree.Ancestor (top x) i →
    toRankedTree.Ancestor i j → x ∈ bag j → x ∈ bag i
  edge_cover : ∀ x y, R x y → ∃ i, x ∈ bag i ∧ y ∈ bag i
  width : ∀ i, (bag i).card ≤ t
  intersection : ∀ i, i ≠ root → (bag i ∩ bag (parent i)).card < t

namespace RankedBagTree

variable {W N : Type} [Fintype W] [Fintype N] {F : SimpleGraph W} {t : ℕ}

noncomputable def toIndexed (D : RankedBagTree (N := N) F.Adj t) : ReducedBagTree F t where
  toIndexedTree := D.toRankedTree.indexed
  bag i := D.bag (D.toRankedTree.enumeration i)
  top x := D.toRankedTree.enumeration.symm (D.top x)
  top_mem x := by simp only [Equiv.apply_symm_apply]; exact D.top_mem x
  top_ancestor x i hx := by
    change Fin (Fintype.card N) at i
    simpa only [RankedTree.indexed, Equiv.symm_apply_apply] using
      D.toRankedTree.ancestor_indexed (D.top_ancestor x _ hx)
  interval_mem x i j hi hij hx := by
    apply D.interval_mem x _ _ _ (D.toRankedTree.indexed_ancestor hij) hx
    simpa only [Equiv.apply_symm_apply] using D.toRankedTree.indexed_ancestor hi
  edge_cover x y h := by
    obtain ⟨i, hx, hy⟩ := D.edge_cover x y h
    exact ⟨D.toRankedTree.enumeration.symm i, by simpa, by simpa⟩
  width i := D.width _
  intersection i hi := by
    simp only [RankedTree.indexed, Equiv.apply_symm_apply]
    apply D.intersection
    intro he
    apply hi
    apply D.toRankedTree.enumeration.injective
    simpa only [RankedTree.indexed, Equiv.apply_symm_apply] using he

end RankedBagTree

end RankedTrees

end ParityWL

end OAI


