-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
-- name    : OAI_Combinatorics_ParityLifts_BagTrees
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:10:07.560984+00:00
-- url     : https://prove2.me/theorems/2d294da1-9394-4b96-81b5-b9fc692e6419
-- title:
--   Rooted bag trees and their reduced cut decompositions
-- statement:
--   This file defines tree decompositions on rooted trees listed in topological order, and converts them into reduced cut decompositions.
--
--   1. **Indexed trees.** An indexed tree has nodes $[N]=\{0,\dots,N-1\}$, a root $\rho$ and a parent map with $\mathrm{par}(i)<i$ for every $i\ne\rho$. The ancestor relation $i\preceq j$ is defined inductively: $i\preceq i$, and if $j\ne\rho$ and $i\preceq\mathrm{par}(j)$ then $i\preceq j$. The file proves that $i\preceq j$ implies $i\le j$; that $\preceq$ is transitive; that $\rho\preceq j$ for all $j$; that two ancestors of a common node are comparable; that if $i\preceq v$ and $i\ne v$, then some child $j$ of $i$ (i.e. $j\ne\rho$, $\mathrm{par}(j)=i$) satisfies $j\preceq v$; and that such a child is unique.
--   2. **Reduced bag trees.** For a graph $F$ on a finite set $W$ and $t\in\mathbb{N}$, a reduced bag tree of $F$ is an indexed tree with bags $B_i\subseteq W$ and a map $\mathrm{top}\colon W\to[N]$ such that
--      - $x\in B_{\mathrm{top}(x)}$ for every $x$, and $x\in B_i$ implies $\mathrm{top}(x)\preceq i$;
--      - if $\mathrm{top}(x)\preceq i\preceq j$ and $x\in B_j$, then $x\in B_i$;
--      - both ends of every edge of $F$ lie in a common bag;
--      - $|B_i|\le t$ for every $i$, and $|B_i\cap B_{\mathrm{par}(i)}|<t$ for every $i\ne\rho$.
--
--      The first two conditions say that the nodes whose bags contain $x$ form a subtree with highest node $\mathrm{top}(x)$, so this is a tree decomposition with bags of size at most $t$ in which adjacent bags share fewer than $t$ vertices.
--   3. **Outer sides.**
--   $$
--   \mathrm{out}(i)=\{x\in W:\ i\preceq\mathrm{top}(x)\},
--   $$
--   the set of vertices whose highest occurrence lies in the subtree rooted at $i$.
--   4. **Associated cut decomposition.** Keeping the tree and the bags and taking the sides $A_i=\mathrm{out}(i)$ gives a reduced cut decomposition of $F$ of width $t$. The verification proved here: for $i\ne\rho$, $\mathrm{out}(i)$ is disjoint from $S_i=B_i\cap B_{\mathrm{par}(i)}$ and all of its outside neighbours lie in $S_i$; and at each node $i$, the bag $B_i$, the parent branch (empty if $i=\rho$, and $W\setminus(S_i\cup\mathrm{out}(i))$ otherwise) and the child branches $\mathrm{out}(j)$ with $\mathrm{par}(j)=i$ are pairwise disjoint and cover $W$.
--
--   Using the highest occurrence $\mathrm{top}(x)$, each vertex is assigned to exactly one side at every node, however many bags contain it. This is how an ordinary tree decomposition of a source graph, with bags of size at most $t$ and adjacent intersections below $t$, enters the separator argument for weighted witnesses.
--
--   **Formalization Note** The structures are `IndexedTree` (with `IndexedTree.Ancestor`) and `ReducedBagTree F t`, whose fields are `bag`, `top`, `top_mem`, `top_ancestor`, `interval_mem`, `edge_cover`, `width`, `intersection`. Item 3 is `ReducedBagTree.outer`, the cut system is `ReducedBagTree.cuts`, and the decomposition of item 4 is `ReducedBagTree.toReducedCuts`; the remaining lemmas are its verification. The private lemmas `ite_eq_left` and `ite_eq_right` are compatibility shims.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/BagTrees.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/BagTrees.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace ParityWL

open scoped BigOperators

section BagTrees

open scoped Classical

/-- An ordinary finite rooted tree in topological node order. -/
structure IndexedTree where
  nodes : ℕ
  root : Fin nodes
  parent : Fin nodes → Fin nodes
  parent_lt : ∀ i, i ≠ root → parent i < i

inductive IndexedTree.Ancestor (D : IndexedTree) (i : Fin D.nodes) : Fin D.nodes → Prop
  | refl : D.Ancestor i i
  | step {j : Fin D.nodes} (hj : j ≠ D.root) :
      D.Ancestor i (D.parent j) → D.Ancestor i j

namespace IndexedTree

variable (D : IndexedTree)

lemma Ancestor.le {i j : Fin D.nodes} (h : D.Ancestor i j) : i ≤ j := by
  induction h with
  | refl => exact le_rfl
  | @step j hj h ih => exact ih.trans (D.parent_lt j hj).le

lemma Ancestor.trans {i j k : Fin D.nodes} (h : D.Ancestor i j)
    (g : D.Ancestor j k) : D.Ancestor i k := by
  induction g with
  | refl => exact h
  | step hk g ih => exact .step hk ih

lemma Ancestor.cases' {i j : Fin D.nodes} (h : D.Ancestor i j) :
    i = j ∨ (j ≠ D.root ∧ D.Ancestor i (D.parent j)) := by
  cases h with
  | refl => exact Or.inl rfl
  | step hj h => exact Or.inr ⟨hj, h⟩

lemma Ancestor.parent {i j : Fin D.nodes} (h : D.Ancestor i j) (hne : i ≠ j) :
    j ≠ D.root ∧ D.Ancestor i (D.parent j) := (h.cases' D).resolve_left hne

lemma root_ancestor (j : Fin D.nodes) : D.Ancestor D.root j := by
  by_cases h : j = D.root
  · subst j; exact .refl
  · exact .step h (root_ancestor (D.parent j))
termination_by j.val
decreasing_by exact D.parent_lt j h

lemma ancestor_chain {i j v : Fin D.nodes} (hi : D.Ancestor i v)
    (hj : D.Ancestor j v) : D.Ancestor i j ∨ D.Ancestor j i := by
  by_cases hiv : i = v
  · subst i; exact Or.inr hj
  by_cases hjv : j = v
  · subst j; exact Or.inl hi
  have hip := hi.parent D hiv
  have hjp := hj.parent D hjv
  exact ancestor_chain hip.2 hjp.2
termination_by v.val
decreasing_by exact D.parent_lt v hip.1

lemma ancestor_child {i v : Fin D.nodes} (hi : D.Ancestor i v) (hne : i ≠ v) :
    ∃ j, j ≠ D.root ∧ D.parent j = i ∧ D.Ancestor j v := by
  have hp := hi.parent D hne
  by_cases hpi : D.parent v = i
  · exact ⟨v, hp.1, hpi, .refl⟩
  obtain ⟨j, hj, hji, hjp⟩ := ancestor_child hp.2 (Ne.symm hpi)
  exact ⟨j, hj, hji, .step hp.1 hjp⟩
termination_by v.val
decreasing_by exact D.parent_lt v hp.1

lemma children_eq {i j k v : Fin D.nodes}
    (hj : j ≠ D.root) (hji : D.parent j = i)
    (hk : k ≠ D.root) (hki : D.parent k = i)
    (hjv : D.Ancestor j v) (hkv : D.Ancestor k v) : j = k := by
  by_contra hne
  have hij : i < j := hji ▸ D.parent_lt j hj
  have hik : i < k := hki ▸ D.parent_lt k hk
  rcases D.ancestor_chain hjv hkv with h | h
  · have hh := (h.parent D hne).2.le D
    rw [hki] at hh
    exact (not_le_of_gt hij) hh
  · have hh := (h.parent D (Ne.symm hne)).2.le D
    rw [hji] at hh
    exact (not_le_of_gt hik) hh

end IndexedTree

variable {W : Type} [Fintype W] {F : SimpleGraph W} {t : ℕ}

/-- Bags on a finite tree. Occurrences form the subtree above their unique
highest occurrence `top`; the interval axiom is precisely subtree convexity.
The intersections on nonroot edges have size strictly below the bag bound;
this is the exact reduction property needed by the orientation argument. -/
structure ReducedBagTree (F : SimpleGraph W) (t : ℕ) extends IndexedTree where
  bag : Fin nodes → Finset W
  top : W → Fin nodes
  top_mem : ∀ x, x ∈ bag (top x)
  top_ancestor : ∀ x i, x ∈ bag i → toIndexedTree.Ancestor (top x) i
  interval_mem : ∀ x i j, toIndexedTree.Ancestor (top x) i →
    toIndexedTree.Ancestor i j → x ∈ bag j → x ∈ bag i
  edge_cover : ∀ x y, F.Adj x y → ∃ i, x ∈ bag i ∧ y ∈ bag i
  width : ∀ i, (bag i).card ≤ t
  intersection : ∀ i, i ≠ root → (bag i ∩ bag (parent i)).card < t

namespace ReducedBagTree

variable (D : ReducedBagTree F t)

noncomputable def outer (i : Fin D.nodes) : Finset W :=
  Finset.univ.filter (fun x => D.toIndexedTree.Ancestor i (D.top x))

noncomputable def cuts : RootedCuts W where
  nodes := D.nodes
  root := D.root
  parent := D.parent
  parent_lt := D.parent_lt
  bag := D.bag
  side := D.outer

lemma mem_outer {i : Fin D.nodes} {x : W} :
    x ∈ D.outer i ↔ D.toIndexedTree.Ancestor i (D.top x) := by
  simp [outer]

lemma mem_cut_separator {i : Fin D.nodes} {x : W} :
    x ∈ D.cuts.separator i ↔ x ∈ D.bag i ∧ x ∈ D.bag (D.parent i) := by
  simp [cuts, RootedCuts.separator]

lemma outer_disjoint (i : Fin D.nodes) (hi : i ≠ D.root) :
    Disjoint (D.outer i) (D.cuts.separator i) := by
  apply Finset.disjoint_left.mpr
  intro x hx hs
  have h1 := (D.mem_outer.mp hx).trans D.toIndexedTree
    (D.top_ancestor x (D.parent i) (D.mem_cut_separator.mp hs).2)
  exact (not_le_of_gt (D.parent_lt i hi)) (h1.le D.toIndexedTree)

lemma outside_boundary (i : Fin D.nodes) (hi : i ≠ D.root)
    (x : W) (hx : x ∈ D.outer i) (y : W) (hxy : F.Adj x y)
    (hy : y ∉ D.outer i) : y ∈ D.cuts.separator i := by
  obtain ⟨v, hxv, hyv⟩ := D.edge_cover x y hxy
  have hiv := (D.mem_outer.mp hx).trans D.toIndexedTree (D.top_ancestor x v hxv)
  have htyi : D.toIndexedTree.Ancestor (D.top y) i := by
    rcases D.toIndexedTree.ancestor_chain (D.top_ancestor y v hyv) hiv with h | h
    · exact h
    · exact (hy (D.mem_outer.mpr h)).elim
  have hne : D.top y ≠ i := by
    intro h
    apply hy
    apply D.mem_outer.mpr
    rw [h]
    exact .refl
  apply D.mem_cut_separator.mpr
  exact ⟨D.interval_mem y i v htyi hiv hyv,
    D.interval_mem y (D.parent i) v (htyi.parent D.toIndexedTree hne).2
      ((IndexedTree.Ancestor.step hi (.refl)).trans D.toIndexedTree hiv) hyv⟩

lemma bag_subset_cut (i : Fin D.nodes) (x : W) (hx : x ∈ D.bag i) :
    x ∈ D.cuts.separator i ∨ x ∈ D.outer i := by
  by_cases h : D.top x = i
  · right
    apply D.mem_outer.mpr
    rw [h]
    exact .refl
  · left
    have ht := (D.top_ancestor x i hx).parent D.toIndexedTree h
    exact D.mem_cut_separator.mpr ⟨hx,
      D.interval_mem x (D.parent i) i ht.2 (.step ht.1 (.refl)) hx⟩

lemma child_outer_disjoint_bag (i j : Fin D.nodes) (hj : j ≠ D.root)
    (hp : D.parent j = i) : Disjoint (D.bag i) (D.outer j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have h := (D.mem_outer.mp hy).trans D.toIndexedTree (D.top_ancestor x i hx)
  have hij : i < j := hp ▸ D.parent_lt j hj
  exact (not_le_of_gt hij) (h.le D.toIndexedTree)

lemma child_outer_subset (i j : Fin D.nodes) (hj : j ≠ D.root)
    (hp : D.parent j = i) : D.outer j ⊆ D.outer i := by
  intro x hx
  apply D.mem_outer.mpr
  have h : D.toIndexedTree.Ancestor i j := by
    rw [← hp]
    exact .step hj (.refl)
  exact h.trans D.toIndexedTree (D.mem_outer.mp hx)

lemma branch_disjoint_bag (i j : Fin D.nodes) : Disjoint (D.bag i) (D.cuts.branch i j) := by
  unfold RootedCuts.branch
  split_ifs with hji hir hp
  · simp
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have hmem := D.bag_subset_cut i x hx
    have hn := (Finset.mem_sdiff.mp hy).2
    exact hn (Finset.mem_union.mpr hmem)
  · exact D.child_outer_disjoint_bag i j hp.1 hp.2
  · simp

lemma branch_eq (i j : Fin D.nodes) : D.cuts.branch i j =
    if j = i then (if i = D.root then ∅ else D.cuts.reverseSide i)
    else if j ≠ D.root ∧ D.parent j = i then D.outer j else ∅ := rfl

lemma reverse_disjoint_child (i j : Fin D.nodes) (hj : j ≠ D.root)
    (hp : D.parent j = i) : Disjoint (D.cuts.reverseSide i) (D.outer j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact (Finset.mem_sdiff.mp hx).2
    (Finset.mem_union.mpr (Or.inr (D.child_outer_subset i j hj hp hy)))

lemma branches_disjoint (i j k : Fin D.nodes) (hjk : j ≠ k) :
    Disjoint (D.cuts.branch i j) (D.cuts.branch i k) := by
  rw [D.branch_eq, D.branch_eq]
  by_cases hji : j = i
  · subst j
    rw [ite_eq_left rfl, ite_eq_right (Ne.symm hjk)]
    by_cases hir : i = D.root
    · rw [ite_eq_left hir]; simp
    · rw [ite_eq_right hir]
      by_cases hpk : k ≠ D.root ∧ D.parent k = i
      · rw [ite_eq_left hpk]
        exact D.reverse_disjoint_child i k hpk.1 hpk.2
      · rw [ite_eq_right hpk]; simp
  · rw [ite_eq_right hji]
    by_cases hki : k = i
    · subst k
      rw [ite_eq_left rfl]
      split_ifs with hp hir
      · simp
      · exact (D.reverse_disjoint_child i j hp.1 hp.2).symm
      · simp
      · simp
    · rw [ite_eq_right hki]
      split_ifs with hp hpk
      · apply Finset.disjoint_left.mpr
        intro x hx hy
        exact hjk (D.toIndexedTree.children_eq hp.1 hp.2 hpk.1 hpk.2
          (D.mem_outer.mp hx) (D.mem_outer.mp hy))
      · simp
      · simp
      · simp

lemma branch_cover (i : Fin D.nodes) (x : W) :
    x ∈ D.bag i ∨ ∃ j, x ∈ D.cuts.branch i j := by
  by_cases hx : x ∈ D.bag i
  · exact Or.inl hx
  right
  by_cases hi : D.toIndexedTree.Ancestor i (D.top x)
  · have hne : i ≠ D.top x := by
      intro h
      exact hx (h ▸ D.top_mem x)
    obtain ⟨j, hj, hp, hjx⟩ := D.toIndexedTree.ancestor_child hi hne
    have hji : j ≠ i := by
      have hlt : i < j := hp ▸ D.parent_lt j hj
      exact ne_of_gt hlt
    refine ⟨j, ?_⟩
    rw [D.branch_eq, ite_eq_right hji, ite_eq_left ⟨hj, hp⟩]
    exact D.mem_outer.mpr hjx
  · have hir : i ≠ D.root := by
      intro h
      apply hi
      rw [h]
      exact D.toIndexedTree.root_ancestor _
    refine ⟨i, ?_⟩
    rw [D.branch_eq, ite_eq_left rfl, ite_eq_right hir]
    change x ∈ Finset.univ \ (D.cuts.separator i ∪ D.outer i)
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro h
    rcases Finset.mem_union.mp h with hs | hs
    · exact hx (D.mem_cut_separator.mp hs).1
    · exact hi (D.mem_outer.mp hs)

/-- Extract the actual shores and local vertex partitions from the occurrence
subtrees; vertices are not double-counted even if they occur in many bags. -/
noncomputable def toReducedCuts : ReducedCutDecomposition F t where
  toRootedCuts := D.cuts
  width := D.width
  intersection := D.intersection
  side_disjoint := D.outer_disjoint
  boundary := D.outside_boundary
  bag_disjoint := D.branch_disjoint_bag
  branch_disjoint := D.branches_disjoint
  vertex_cover := D.branch_cover

end ReducedBagTree

end BagTrees

end ParityWL

end OAI


