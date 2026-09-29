-- Prove2me | Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn
-- name    : NagamochiIbaraki_EdgeConn_localEdgeConn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:00:56.166254+00:00
-- url     : https://prove2.me/theorems/7cc98a74-dbf8-4ffb-9b5e-bd2e78e12b0d
-- title:
--   Local edge-connectivity λ(x, y; F): the minimum number of edges of F whose removal separates x and y
-- statement:
--   Let $G = (V, E)$ be a finite multigraph and $F \subseteq E$ an edge subset. The **local edge-connectivity** between nodes $x$ and $y$ in the spanning subgraph $(V, F)$ is
--
--   $$
--   \lambda(x, y; F) \;=\; \min\bigl\{\, |W| \;:\; W \subseteq F,\ x \text{ and } y \text{ are not connected by a path in } (V, F \setminus W) \,\bigr\},
--   $$
--
--   the minimum size of an edge cut separating $x$ from $y$. Parallel edges are counted with multiplicity: each of them has to be removed separately. By Menger's theorem this is the maximum number of pairwise edge-disjoint paths between $x$ and $y$, the reading the paper uses on p. 594.
--
--   The value is taken in $\mathbb{N} \cup \{\infty\}$. When $x = y$ no edge set separates $x$ from itself, the set of cuts is empty, and $\lambda(x, x; F) = \infty$; this makes statements "for all $x, y \in V$" hold trivially on the diagonal, as intended by the paper. When $x \ne y$ are already disconnected in $(V, F)$, $\lambda(x, y; F) = 0$.
--
--   This is the quantity $\lambda(x, y; H)$ of inequality (2.1), which Theorem 2.1 and Lemma 2.1 compare between $G$ and the sparse subgraphs $G_i$.
--
--   **Formalization Note** The minimum is an infimum in `ℕ∞` over the finite family of separating edge sets; it is attained whenever $x \ne y$, because $W = F$ always separates distinct nodes.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), p. 584, Lemma 2.1 (λ(x, y; H) and its proof's minimal cut set); p. 594, §4 (Menger's theorem)

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph

namespace NagamochiIbaraki.EdgeConn

variable {V E : Type*}

/-- The local edge-connectivity `λ(x, y; (V, F))` of the nodes `x, y` in the spanning subgraph
`(V, F)` of a multigraph: the minimum number of edges `W ⊆ F` whose removal leaves no path
between `x` and `y` in `(V, F \ W)`. Parallel edges are counted separately. The value lies in
`ℕ∞`; it is `⊤` exactly when `x = y` (no edge set separates a node from itself), and `0` when
`x` and `y` are already disconnected in `(V, F)`. -/
noncomputable def localEdgeConn [DecidableEq E] (ends : E → Sym2 V) (F : Finset E) (x y : V) : ℕ∞ :=
  ⨅ W ∈ {W : Finset E | W ⊆ F ∧ ¬ (edgeGraph ends (F \ W)).Reachable x y}, (W.card : ℕ∞)

end NagamochiIbaraki.EdgeConn


