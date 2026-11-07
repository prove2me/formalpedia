-- Prove2me | Definitions.Def_RGMISFast_AdmissibleTree
-- name    : RGMISFast_AdmissibleTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:42.219933+00:00
-- url     : https://prove2.me/theorems/1247654d-361a-48ff-b044-39578dfeee99
-- title:
--   Admissible trees and their prefixes $T_t$
-- statement:
--   Let $G$ be a finite simple graph with ranks $r$ and root $u^*$. A rooted tree $T$ is **admissible** if its nodes are distinct vertices of $G$, its root is $u^*$, and every child $w$ of a node $v$ satisfies
--   $$
--   w\in N(v)\qquad\text{and}\qquad r(w)\le\tau(v).
--   $$
--   For $w\neq u^*$ in $T$, $\mathrm{par}[w]$ denotes its parent. For $t\in[0,\infty]$, the **prefix** $T_t$ is the set of nodes of $T$ that are active at time $t$, i.e. with $t\le\tau(v)$.
--
--   By Observation 2.2 the query tree of Procedure 1.1 is admissible; the mission bounds the size of every admissible tree.
--
--   **Formalization Note** The tree is a finite node set containing $u^*$ together with a parent map and a depth map: every node $w\neq u^*$ has its parent in the tree, adjacent to $w$, with $r(w)\le\tau(\mathrm{par}[w])$ and strictly smaller depth. The depth condition excludes cycles of the parent map, so the parent edges form a tree rooted at $u^*$.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Definition 2.3, p.11 (PDF p.13); T_t, p.11

import Mathlib
import Definitions.Def_RGMISFast_tau

set_option autoImplicit false

namespace RGMISFast

/-- An admissible tree (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy
MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), Definition 2.3,
p.11): "A rooted tree T is admissible if its nodes are distinct vertices of G, its root is u∗,
and every child w of a node v satisfies w ∈ N(v) and r(w) ≤ τ(v). For a vertex w ≠ u∗ in an
admissible tree T, we write par[w] for its parent in T."

**Formalization Note** The tree is given by its finite node set `nodes ∋ u` (so nodes are
distinct vertices), a parent map `par` and a depth map `depth`. Every node `w ≠ u` has its parent
in the tree, adjacent to it in `G`, with `r w ≤ τ(par w)`, and of strictly smaller depth. The
depth condition makes the parent relation acyclic, so following parents from any node reaches
the root `u`, the only node without a parent: the nodes with the edges `{par w, w}` form a tree
rooted at `u`. The values of `par` and `depth` off `nodes ∖ {u}` play no role. -/
structure AdmissibleTree {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {α : Type*} [LinearOrder α] (r : V → α) (u : V) where
  nodes : Finset V
  root_mem : u ∈ nodes
  par : V → V
  depth : V → ℕ
  par_mem : ∀ w ∈ nodes, w ≠ u → par w ∈ nodes
  par_adj : ∀ w ∈ nodes, w ≠ u → G.Adj (par w) w
  rank_le : ∀ w ∈ nodes, w ≠ u → r w ≤ tau G r (par w)
  depth_lt : ∀ w ∈ nodes, w ≠ u → depth (par w) < depth w

/-- The prefix `T_t` of an admissible tree (Dalirrooyfard, Makarychev, Mitrović, Ramachandran,
*Randomized Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256
e93cdfec…), §2, p.11): "For every t ∈ [0, ∞], define T_t to be the subtree of an admissible tree
T induced by the vertices that are active at time t", i.e. the nodes `v` with `t ≤ τ(v)`. -/
def AdmissibleTree.prefix {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {α : Type*} [LinearOrder α] {r : V → α} {u : V}
    (T : AdmissibleTree G r u) (t : α) : Finset V :=
  T.nodes.filter (fun v => t ≤ tau G r v)

end RGMISFast


