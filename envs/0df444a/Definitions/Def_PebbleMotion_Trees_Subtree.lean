-- Prove2me | Definitions.Def_PebbleMotion_Trees_Subtree
-- name    : PebbleMotion_Trees_Subtree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:37:28.397378+00:00
-- url     : https://prove2.me/theorems/80ed5ae3-b064-4481-8fb2-f684592b870e
-- title:
--   Subtrees, components of $T-v$ and $T-e$, centroid vertices and centroid edges
-- statement:
--   A **subtree** of a tree $T$ is given by its vertex set $S$: the subgraph induced by $S$ is connected (so $S\neq\emptyset$). In a tree a connected subgraph on $S$ is exactly the induced subgraph, so this is no restriction; its order is $|S|$.
--
--   For a vertex $v$ and $a\ne v$, the component of $T-v$ containing $a$ is the set of vertices reachable from $a$ by a walk avoiding $v$; for an edge $e$, the component of $T-e$ containing $a$ is the set reachable from $a$ by a walk not using $e$.
--
--   A **centroid vertex** of $T$ is a vertex $v$ such that every connected component of $T-v$ has order at most $(|V(T)|-1)/2$. A **centroid edge** is an edge $uv$ such that both components of $T-uv$ have order exactly $|V(T)|/2$.
-- source:
--   Nakamigawa and Sakuma, Structural Origins of Cubic Complexity in Pebble Motion, arXiv:2503.20550 (held revision dated 2026-11-03), §5, centroid paragraph and Lemmas 12–14, p.14–15, PDF SHA256 efd330453039630e97e2ef1029ef0b2b3ac5a16bd700a2c5fad226582870f412

import Mathlib

set_option autoImplicit false

namespace PebbleMotion.Trees

variable {V : Type*}

/-- `S` is the vertex set of a **subtree** of the tree `T` (Nakamigawa–Sakuma, §5, pp.14–15): the
subgraph of `T` induced by `S` is connected (in particular `S` is nonempty). In a tree, a connected
subgraph with vertex set `S` is exactly the induced subgraph `T[S]`, so a subtree is determined by
its vertex set; its order is `S.card`. -/
def IsSubtreeSet (T : SimpleGraph V) (S : Finset V) : Prop :=
  (T.induce (S : Set V)).Connected

/-- The vertex set of the connected component of `T − v` that contains `a` (for `a ≠ v`): the
vertices `b` joined to `a` by a walk of `T` that avoids `v`. -/
def componentAvoidingVertex (T : SimpleGraph V) (v a : V) : Set V :=
  {b | ∃ p : T.Walk a b, v ∉ p.support}

/-- The vertex set of the connected component of `T − e` that contains `a`: the vertices `b`
joined to `a` by a walk of `T` that does not use the edge `e`. -/
def componentAvoidingEdge (T : SimpleGraph V) (e : Sym2 V) (a : V) : Set V :=
  {b | ∃ p : T.Walk a b, e ∉ p.edges}

/-- A **centroid vertex** of the tree `T` (p.14): every connected component of `T − v` has order at
most `(|V(T)| − 1)/2`. -/
def IsCentroidVertex [Fintype V] (T : SimpleGraph V) (v : V) : Prop :=
  ∀ a : V, a ≠ v →
    ((componentAvoidingVertex T v a).ncard : ℝ) ≤ ((Fintype.card V : ℝ) - 1) / 2

/-- A **centroid edge** `uv` of the tree `T` (p.14): `uv` is an edge and each of the two connected
components of `T − uv` (the one containing `u` and the one containing `v`) has order exactly
`|V(T)|/2`. -/
def IsCentroidEdge [Fintype V] (T : SimpleGraph V) (u v : V) : Prop :=
  T.Adj u v ∧
    ((componentAvoidingEdge T s(u, v) u).ncard : ℝ) = (Fintype.card V : ℝ) / 2 ∧
    ((componentAvoidingEdge T s(u, v) v).ncard : ℝ) = (Fintype.card V : ℝ) / 2

end PebbleMotion.Trees


