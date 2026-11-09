-- Prove2me | Definitions.Def_MetricTSPSublinear_SteinerTree
-- name    : MetricTSPSublinear_SteinerTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:24:02.259764+00:00
-- url     : https://prove2.me/theorems/a82e4ef5-4828-4530-89e3-a1508968f762
-- title:
--   Weighted Steiner trees on a point set
-- statement:
--   Let $S\subseteq V$. A **weighted Steiner tree on $S$** is a finite tree $F$ whose node set contains $S$ (distinct points are distinct nodes), with nonnegative edge weights $w_F$, all of whose leaves are points of $S$. Its weight is $w(F)=\sum_{e\in F}w_F(e)$, and $d_F(u,v)$ denotes the weight of the $u$–$v$ path in $F$.
--
--   Steiner trees are the paper's representation of dual solutions of the cut LP: dominated Steiner trees and feasible dual solutions correspond (Claim 4.1, Lemma 4.2).
--
--   **Formalization Note.** The nodes are $\{0,\dots,m-1\}$ for a number $m$ that is part of the data, with an embedding of the points injective on $S$. The weighted tree and its path distance $d_F$ are the published `TreeCoverLB.WeightedTree` and its `dist`. A leaf is a node with at most one neighbour, so the only node of a one-node tree must be a point of $S$; there is no Steiner tree on $S=\emptyset$.
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §4.1, p.12 (PDF p.14); §2.1, pp.4–5 (PDF pp.6–7)

import Mathlib
import Definitions.Def_TreeCoverLB_WeightedTree

open scoped Classical

namespace MetricTSPSublinear

/-- **A weighted Steiner tree on a point set `S`.**
Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §4.1, p.12 (PDF p.14): "weighted Steiner trees whose vertex set contains V, and whose leaves are
members of V"; §2.1, pp.4–5 (PDF pp.6–7).

A Steiner tree on `S ⊆ Fin n` has
* `m` nodes `Fin m`, and an embedding `ι` of the points, injective on `S` (the node set contains `S`);
* a weighted tree `T` on the nodes: the published `TreeCoverLB.WeightedTree`, a tree `T.G` (connected and acyclic)
  with edge weights `T.w`, nonnegative on its edges;
* every leaf in `S`: a node with at most one neighbour is `ι s` for some `s ∈ S`.

**Formalization Note.** The node type is `Fin m` with `m` a field, so that a structure instance has no universe
parameter. `ι` is defined on all of `Fin n`; only its values on `S` matter. "Leaf" is read as "at most one
neighbour", so the only node of a one-node tree must be a point of `S`; for `|S| ≥ 2` a tree has no isolated node and
this is the usual "degree one". There is no Steiner tree on `S = ∅`. The weights of non-edges are irrelevant. -/
structure SteinerTree {n : ℕ} (S : Finset (Fin n)) where
  /-- The number of nodes. -/
  m : ℕ
  /-- The embedding of the points into the nodes. -/
  ι : Fin n → Fin m
  /-- Distinct points of `S` are distinct nodes. -/
  inj : Set.InjOn ι S
  /-- The weighted tree on the nodes (published `TreeCoverLB.WeightedTree`: a tree `T.G`, weights `T.w ≥ 0` on its
  edges, tree distance `T.dist`). -/
  T : TreeCoverLB.WeightedTree (Fin m)
  /-- Every leaf is a point of `S`. -/
  leaves : ∀ a : Fin m, (∀ b c, T.G.Adj a b → T.G.Adj a c → b = c) → ∃ s ∈ S, ι s = a

namespace SteinerTree

variable {n : ℕ} {S : Finset (Fin n)}

/-- `d_F(a, b)`: the weight of the path from `a` to `b` in `F` (the published tree distance). -/
noncomputable def pathWt (F : SteinerTree S) (a b : Fin F.m) : ℝ :=
  F.T.dist a b

/-- The edges of `F` as a finite set. -/
noncomputable def edges (F : SteinerTree S) : Finset (Sym2 (Fin F.m)) :=
  Finset.univ.filter (fun e => e ∈ F.T.G.edgeSet)

/-- `w(F)`: the total weight of the edges of `F`. -/
noncomputable def weight (F : SteinerTree S) : ℝ :=
  ∑ e ∈ F.edges, F.T.w e

end SteinerTree

end MetricTSPSublinear


