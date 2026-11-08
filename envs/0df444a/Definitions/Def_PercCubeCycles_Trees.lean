-- Prove2me | Definitions.Def_PercCubeCycles_Trees
-- name    : PercCubeCycles_Trees
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:24.202182+00:00
-- url     : https://prove2.me/theorems/59784891-7616-42fa-a904-7b424d05d680
-- title:
--   Marked trees and special $(a,b)$-trees (§3; Definition 6.1)
-- statement:
--   Given a graph $G$, a **marked tree** is a triple $B=(T,S_1,S_2)$ with $T\subseteq G$ a tree and $S_1,S_2\subseteq V(T)$ non-empty and disjoint. Its **length** is
--   $$d(B)=\min\{d_T(x,y): x\in S_1,\ y\in S_2\}.$$
--
--   For a tree $T$ on at least three vertices, $A(T)$ is the set of leaves whose unique neighbour in $T$ has degree at least three, and $B(T)$ is the set of remaining leaves. For $H\supseteq T$, the tree $T$ is an **$H$-special $(a,b)$-tree** if $|A(T)|=a$, $|B(T)|=b$, and every leaf in $B(T)$ is incident to an edge of $E(H[V(T)])\setminus E(T)$.
--
--   $T$ is **interior-closed** in $H$ if $N_H(v)\subseteq V(T)$ for every non-leaf $v$ of $T$, and **almost interior-closed** if this holds for every non-leaf that is not a neighbour of a leaf in $T$. $\ell(T)$ is the number of leaves.
--
--   Marked trees carry the joining argument of Proposition 3.1, and special trees carry the expansion estimates of §6.
--
--   **Formalization Note** A tree in $G$ is a `G.Subgraph` whose coercion is a tree.
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), §3, p.9; Definition 6.1, p.19

import Mathlib
import Definitions.Def_PercCubeCycles_GraphNotation

set_option autoImplicit false

namespace PercCubeCycles

/-!
# Marked trees and special trees

Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…): marked trees, §3, p.9; Definition 6.1, p.19.

**Formalization Note.** A tree `T ⊆ G` is a `T : G.Subgraph` with `T.coe.IsTree`, so two trees with
the same vertices and different edges are different. A tree inside `C₂` is a subgraph of the
graph `coreGraph G L`; the class of special trees also takes the ambient graph `H` in which surplus
edges are counted, which is `Q^d_p` in Lemmas 6.3 and 6.5.
-/

variable {V : Type*}

/-- The degree of `v` in the subgraph `T`. -/
noncomputable def treeDeg [Fintype V] {G : SimpleGraph V} (T : G.Subgraph) (v : V) : ℕ :=
  deg T.spanningCoe v

open scoped Classical in
/-- The leaves of `T`. -/
noncomputable def leaves [Fintype V] {G : SimpleGraph V} (T : G.Subgraph) : Finset V :=
  Finset.univ.filter fun v => v ∈ T.verts ∧ treeDeg T v = 1

/-- Definition 6.1, p.19: `ℓ(T)`, the number of leaves of `T`. -/
noncomputable def leafCount [Fintype V] {G : SimpleGraph V} (T : G.Subgraph) : ℕ :=
  (leaves T).card

open scoped Classical in
/-- Definition 6.1, p.19: `A(T)`, the leaves of `T` whose unique neighbour in `T` has degree at
least three. -/
noncomputable def leafA [Fintype V] {G : SimpleGraph V} (T : G.Subgraph) : Finset V :=
  (leaves T).filter fun v => ∃ u, T.Adj v u ∧ 3 ≤ treeDeg T u

open scoped Classical in
/-- Definition 6.1, p.19: `B(T)`, the remaining leaves of `T`. -/
noncomputable def leafB [Fintype V] {G : SimpleGraph V} (T : G.Subgraph) : Finset V :=
  leaves T \ leafA T

/-- Definition 6.1, p.19: `T` is an `H`-special `(a, b)`-tree: a tree on at least three vertices with
`|A(T)| = a`, `|B(T)| = b`, and every leaf in `B(T)` incident to an edge of `E(H[V(T)]) ∖ E(T)`. -/
def IsSpecial [Fintype V] {G : SimpleGraph V} (H : SimpleGraph V) (T : G.Subgraph) (a b : ℕ) : Prop :=
  T.coe.IsTree ∧ 3 ≤ T.verts.ncard ∧ (leafA T).card = a ∧ (leafB T).card = b ∧
    ∀ v ∈ leafB T, ∃ u ∈ T.verts, H.Adj v u ∧ ¬ T.Adj v u

/-- Definition 6.1, p.19: `T` is interior-closed in `H`: `N_H(v) ⊆ V(T)` for every non-leaf `v` of `T`. -/
def IsInteriorClosed [Fintype V] {G : SimpleGraph V} (H : SimpleGraph V) (T : G.Subgraph) : Prop :=
  ∀ v ∈ T.verts, v ∉ leaves T → ∀ u, H.Adj v u → u ∈ T.verts

/-- Definition 6.1, p.19: `T` is almost interior-closed in `H`: `N_H(v) ⊆ V(T)` for every non-leaf
`v` of `T` that is not a neighbour of a leaf in `T`. -/
def IsAlmostInteriorClosed [Fintype V] {G : SimpleGraph V} (H : SimpleGraph V) (T : G.Subgraph) :
    Prop :=
  ∀ v ∈ T.verts, v ∉ leaves T → (∀ l ∈ leaves T, ¬ T.Adj v l) → ∀ u, H.Adj v u → u ∈ T.verts

/-- p.9: `B = (T, S₁, S₂)` is a marked tree: `T` is a tree, `S₁, S₂ ⊆ V(T)` are non-empty and
`S₁ ∩ S₂ = ∅`. -/
def IsMarkedTree {G : SimpleGraph V} (T : G.Subgraph) (S₁ S₂ : Finset V) : Prop :=
  T.coe.IsTree ∧ S₁.Nonempty ∧ S₂.Nonempty ∧ (S₁ : Set V) ⊆ T.verts ∧ (S₂ : Set V) ⊆ T.verts ∧
    Disjoint S₁ S₂

/-- p.9: the length `d(B) = min{d_T(x, y) : x ∈ S₁, y ∈ S₂}` of a marked tree. The minimum is over a
nonempty set on a marked tree. -/
noncomputable def markedLength {G : SimpleGraph V} (T : G.Subgraph) (S₁ S₂ : Finset V) : ℕ :=
  sInf {n | ∃ x ∈ S₁, ∃ y ∈ S₂, T.spanningCoe.dist x y = n}

end PercCubeCycles


