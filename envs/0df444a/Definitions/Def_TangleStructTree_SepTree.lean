-- Prove2me | Definitions.Def_TangleStructTree_SepTree
-- name    : TangleStructTree_SepTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:18.007195+00:00
-- url     : https://prove2.me/theorems/8d42d768-b0c3-4ef6-9fec-548846542a93
-- title:
--   Separation trees on $\vec S$
-- statement:
--   Let $(\vec S,\le,{}^*)$ be a separation system. A rooted tree $(T,r)$ carries the tree order $x\le_r y$ ($x$ lies on the path from $r$ to $y$); its maximal elements are the **leaves**, the direct successors of a node are its children, and $E_v$ is the set of edges from $v$ to its children.
--
--   **Definition 3.1.** A **separation tree** $(T,r,\beta)$ on $\vec S$ is a rooted tree $(T,r)$ with an edge labelling $\beta:E(T)\to\vec S$ such that for every non-leaf $v$ there is a separation $s_v\in S$ such that $\beta$ restricts to a bijection $E_v\to\{\vec s_v,\overleftarrow{s}_v\}$, and $s_u\ne s_v$ whenever $u<_r v$.
--
--   For a node $v$, $\beta_v$ is the set of edge labels on the path from $r$ to $v$.
--
--   Separation trees are the data structure of the mission: each root–leaf path orients a set of separations, and each non-leaf branches on the two orientations of one new separation.
--
--   **Formalization Note** A finite rooted edge-labelled tree is encoded by the finite, prefix-closed set of its root-path label lists (newest label first): the root is `[]` and the children of `v` are the lists `x :: v`. Since the labels on the edges from one node to its children are distinct, this set determines the tree up to root- and label-preserving isomorphism, and two separation trees are equal as `SepTree`s exactly when they are isomorphic in this sense. A degenerate $s_v$ gives a node with one child. Trees are finite, as in the graph terminology the paper adopts. `labels v` is $\beta_v$; `IsLeaf` is "node without children".
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §3, p.6 (PDF 17), Definition 3.1

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem

namespace TangleStructTree

open SepSystem

/-- **Definition 3.1** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, p.6 (PDF 17)): a **separation
tree** `(T, r, β)` on `S⃗` is a rooted tree `(T, r)` with an edge labelling `β : E(T) → S⃗` such
that for every non-leaf `v` there is a separation `s_v ∈ S` such that `β` restricts to a bijection
from the edges `E_v` from `v` to its children onto `{s⃗_v, s⃖_v}`, and `s_u ≠ s_v` whenever
`u <_r v`.

**Formalization Note** (encoding of rooted edge-labelled trees)
1. A node `v` is recorded as the list of edge labels on the path `rTv`, newest first: the root is
   `[]`, and the children of `v` are the nodes `x :: v`, where `x` is the label of the edge from
   `v` to that child. The tree is its finite, prefix-closed set `nodes` of such lists. Because the
   labels of the edges from a node to its children are distinct (`β` is a bijection on `E_v`),
   this set determines the rooted labelled tree up to root- and label-preserving isomorphism, and
   every finite separation tree arises; two separation trees are equal as `SepTree`s iff they are
   isomorphic in this sense.
2. `split`: if `v` has a child, there is `s` (an orientation `s⃗_v` of `s_v`) such that the child
   labels of `v` are exactly `s` and `s∗` (one child if `s_v` is degenerate), and no label on the
   path `rTv` is an orientation of `s_v`. Each label on `rTv` is an orientation of `s_u` for
   some `u <_r v`, so this is `s_u ≠ s_v` for all `u <_r v`.
3. Trees are finite, as in the graph-theoretic terminology of [11] that the paper adopts. -/
structure SepTree (E : Type*) [PartialOrder E] [SepSystem E] where
  /-- The nodes, each recorded as its root path's edge labels, newest first. -/
  nodes : Finset (List E)
  /-- The root `[]` is a node. -/
  root_mem : [] ∈ nodes
  /-- The parent of a node is a node. -/
  parent_mem : ∀ (x : E) (v : List E), x :: v ∈ nodes → v ∈ nodes
  /-- Every non-leaf `v` splits along one separation `s_v`, new on the path `rTv`. -/
  split : ∀ v ∈ nodes, (∃ x : E, x :: v ∈ nodes) →
    ∃ s : E, (∀ x : E, x :: v ∈ nodes ↔ (x = s ∨ x = rev s)) ∧
      (∀ y ∈ v, y ≠ s ∧ y ≠ rev s)

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- `β_v`, the set of edge labels on the path `rTv` (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version,
§3, p.6 (PDF 17)), for the node recorded by the list `v`. -/
def labels (v : List E) : Set E :=
  {y | y ∈ v}

/-- `v` is a **leaf** of `T`: a node with no child (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version,
§3, p.6 (PDF 17); the root is a leaf if `|T| = 1`). -/
def SepTree.IsLeaf (T : SepTree E) (v : List E) : Prop :=
  v ∈ T.nodes ∧ ∀ x : E, x :: v ∉ T.nodes

end TangleStructTree


