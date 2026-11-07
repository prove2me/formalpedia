-- Prove2me | Definitions.Def_PredAdvice_RootedTree
-- name    : PredAdvice_RootedTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:55.180194+00:00
-- url     : https://prove2.me/theorems/0543e9eb-f9ed-4b9f-8831-1377d0d56aac
-- title:
--   Rooted trees and shortest-path trees directed toward or away from the root
-- statement:
--   A **rooted tree** on a subset of $V$ is given by a root, a vertex set $V(T)$ and a parent map; it has $|E(T)|=|V(T)|-1$ edges, one from each nonroot vertex to its parent.
--
--   1. $T$ is a **shortest-path tree directed toward its root** $r$ if $r\in V(T)$ and every nonroot $x\in V(T)$ has $\mathrm{parent}(x)\in V(T)$, an edge $(x,\mathrm{parent}(x))\in E$, and $\mathrm{dist}(x,r)=\mathrm{dist}(\mathrm{parent}(x),r)+1<\infty$.
--   2. $T$ is a **shortest-path tree directed away from its root** $r$ if the same holds with the edge $(\mathrm{parent}(x),x)$ and $\mathrm{dist}(r,x)=\mathrm{dist}(r,\mathrm{parent}(x))+1<\infty$.
--
--   Following parents gives the tree path, which is a shortest path of $G$. "A shortest-path tree may span only a subset of $V$, but its paths to or from the root must be shortest paths in $G$" (p.10). The module also has the two tags *toward* and *away* used for a tree cover.
--
--   **Formalization Note** The distance condition makes the parent structure acyclic.
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), §2, p.10; §4, p.19; App. B, p.29

import Mathlib
import Definitions.Def_PredAdvice_dist

set_option autoImplicit false

namespace PredAdvice

/-- A rooted tree on a subset of the vertex set `V`, stored by parent pointers (Kopelowitz, Korin,
Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript
sha256 0ae8a68d…), §2, p.10: "A shortest-path tree may span only a subset of V"; App. B, p.29:
"Store the parent of each nonroot vertex"): a root, a finite vertex set `V(T)` and a parent map.
Which values of `parent` matter (the nonroot vertices of `V(T)`) is fixed by the predicates below. -/
structure RootedTree (V : Type*) where
  root : V
  verts : Finset V
  parent : V → V

/-- The number of edges `|E(T)|` of a rooted tree: one edge from every nonroot vertex to its parent,
i.e. `|V(T)| − 1`. -/
def RootedTree.edges {V : Type*} (T : RootedTree V) : ℕ :=
  T.verts.card - 1

/-- `T` is a **shortest-path tree of `G` directed toward its root** (§2, p.10; §4, p.19): the root
is in `V(T)`, and every nonroot vertex `x ∈ V(T)` has its parent in `V(T)`, an edge `(x, parent x)`
of `G`, and `dist(x, root) = dist(parent x, root) + 1 < ∞`. Following parents from `u ∈ V(T)` is the
tree path from `u` to the root; it is a shortest `u`–root path of `G`.

**Formalization Note** The distance condition makes the parent structure acyclic, so `T` is a
tree; its edges are the pairs `(x, parent x)` for nonroot `x ∈ V(T)`. -/
def IsTowardTree {V : Type*} (G : Digraph V) (T : RootedTree V) : Prop :=
  T.root ∈ T.verts ∧ ∀ x ∈ T.verts, x ≠ T.root →
    T.parent x ∈ T.verts ∧ G.Adj x (T.parent x) ∧ Reachable G x T.root ∧
      dist G x T.root = dist G (T.parent x) T.root + 1

/-- `T` is a **shortest-path tree of `G` directed away from its root** (§2, p.10; §4, p.19): the
root is in `V(T)`, and every nonroot vertex `x ∈ V(T)` has its parent in `V(T)`, an edge
`(parent x, x)` of `G`, and `dist(root, x) = dist(root, parent x) + 1 < ∞`. The tree path from the
root to `v ∈ V(T)` is a shortest root–`v` path of `G`. -/
def IsAwayTree {V : Type*} (G : Digraph V) (T : RootedTree V) : Prop :=
  T.root ∈ T.verts ∧ ∀ x ∈ T.verts, x ≠ T.root →
    T.parent x ∈ T.verts ∧ G.Adj (T.parent x) x ∧ Reachable G T.root x ∧
      dist G T.root x = dist G T.root (T.parent x) + 1

/-- The two kinds of trees of a tree cover (§4.3, p.22): directed toward the root (`T⁻`) or away
from it (`T⁺`). -/
inductive TreeKind where
  | toward
  | away
  deriving DecidableEq

end PredAdvice


