-- Prove2me | Definitions.Def_EuclidKSteiner_Supplement_IntWeightSteiner
-- name    : EuclidKSteiner_Supplement_IntWeightSteiner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:56:03.301907+00:00
-- url     : https://prove2.me/theorems/f77f5181-3483-40ea-a4a9-09873dcfd02d
-- title:
--   Theorem 1.2 setting — connected $G[P]$, Steiner edges, trees spanning $P$ with at most $b$ Steiner edges, and the input layout
-- statement:
--   Let $G$ be a graph on the vertex set $V(G)=\{0,\dots,n_V-1\}$ with a finite edge set $E$, and let $P\subseteq V(G)$ be the **terminal set**; the remaining vertices $Q=V(G)\setminus P$ are the **candidates**.
--
--   1. The **induced subgraph** $G[P]$ has vertex set $P$ and the edges of $G$ with both endpoints in $P$. It is **connected** when $P\neq\emptyset$ and any two terminals are joined by a walk using only such edges.
--   2. The **Steiner edges** of an edge set $T$ are the edges of $T$ with an endpoint outside $P$, i.e. the edges incident to selected candidates.
--   3. An edge set $T\subseteq E$ is a **feasible tree with budget $b$** if it is a tree on some vertex set $X\supseteq P$ (so $X=P\cup S$ with $S\subseteq Q$ the selected candidates; for $|P|=1$ the empty tree on $X=P$ is allowed) and has at most $b$ Steiner edges. The number $|S|$ of selected candidates is not bounded separately.
--   4. The **machine input** is the list of reals $n_V,\ |E|,\ b$, then the terminal flag of each vertex ($1$ for a terminal, $0$ for a candidate), then each edge as the triple $(u,v,w(uv))$.
--
--   These are the objects of Theorem 1.2 (integer edge weights): a minimum-weight feasible tree is computed in $2^{O(b)}(|G|+W)^{O(1)}$ time.
--
--   **Formalization Note** "Tree" uses the published `EuclidKSteiner.IsSpanningTree` (edges from $E$, no loops, endpoints in $X$, $X$ connected by $T$, $|T|+1=|X|$). The edge list is the published `edgeCells`; the listing names each edge once (`IsEdgeListing`). Connectedness of $G[P]$ includes nonemptiness, the standard convention.
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Theorem 1.2, p.3 (PDF p.5); proof pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_EuclidKSteiner_SpanningTree
import Definitions.Def_EuclidKSteiner_Layouts

set_option autoImplicit false

namespace EuclidKSteiner

namespace Supplement

open Classical

/-!
# Theorem 1.2: graphs with a terminal set, feasible trees with a Steiner-edge budget, input layout

Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean k-Steiner Tree*,
STOC 2027 submission (manuscript sha256 75361687…), Theorem 1.2, p.3 (PDF p.5): "Let G be a graph
with integer edge weights in [0, W], a terminal set P, and a candidate set Q = V(G) \ P, with G[P]
connected. Given a nonnegative integer b, a minimum-weight tree spanning P, with at most b edges in
total incident to the selected candidates, can be found deterministically in 2^{O(b)}(|G| + W)^{O(1)}
time." Proof: p.19–20 (PDF pp.21–22).

**Formalization Note**
* The graph has vertex set `Fin nV` and a finite edge set `E` of unordered pairs (the published
  `IsEdgeListing` lists each edge once). Loops are excluded where the theorem is stated.
* `G[P]` is the graph on `P` with the edges of `G` inside `P`. "Connected" is read in the standard
  sense, which includes nonemptiness (a graph with no vertex is not connected).
* A feasible solution is an edge set `T ⊆ E(G)` forming a tree on a vertex set `X ⊇ P`
  (`X = P ∪ S`, `S ⊆ Q` the selected candidates; the published `IsSpanningTree`, so `|T| + 1 = |X|`,
  and for `|P| = 1` the empty tree on `X = P`) with at most `b` edges having an endpoint outside `P`
  (the edges incident to the selected candidates). There is no separate bound on `|S|`.
-/

/-- The edges of `G` with both endpoints in `P`: the edge set of the induced subgraph `G[P]`. -/
def inducedEdges {nV : ℕ} (E : Finset (Sym2 (Fin nV))) (P : Finset (Fin nV)) :
    Finset (Sym2 (Fin nV)) :=
  E.filter (fun e => ∀ x ∈ e, x ∈ P)

/-- `G[P]` is **connected**: `P` is nonempty and any two vertices of `P` are joined by a walk
using only edges of `G` inside `P`.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, Theorem 1.2, p.3 (PDF p.5): "with G[P] connected". -/
def InducedConnected {nV : ℕ} (E : Finset (Sym2 (Fin nV))) (P : Finset (Fin nV)) : Prop :=
  P.Nonempty ∧ ∀ u ∈ P, ∀ v ∈ P,
    (SimpleGraph.fromEdgeSet ((inducedEdges E P : Finset (Sym2 (Fin nV))) : Set (Sym2 (Fin nV)))).Reachable u v

/-- The **Steiner edges** of an edge set `T`: its edges with an endpoint outside the terminal set
`P`, i.e. the edges incident to a selected candidate.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, Theorem 1.2, p.3 (PDF p.5); §2.1, p.2 (PDF p.4). -/
def steinerEdges {nV : ℕ} (P : Finset (Fin nV)) (T : Finset (Sym2 (Fin nV))) :
    Finset (Sym2 (Fin nV)) :=
  T.filter (fun e => ∃ x ∈ e, x ∉ P)

/-- `T` is a **feasible tree** for Theorem 1.2: a tree of `G` (edges from `E`) on some vertex set
`X ⊇ P` with at most `b` edges incident to the selected candidates `X \ P`.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, Theorem 1.2, p.3 (PDF p.5): "a minimum-weight tree
spanning P, with at most b edges in total incident to the selected candidates". -/
def IsBudgetTree {nV : ℕ} (E : Finset (Sym2 (Fin nV))) (P : Finset (Fin nV)) (b : ℕ)
    (T : Finset (Sym2 (Fin nV))) : Prop :=
  (∃ X : Finset (Fin nV), P ⊆ X ∧ IsSpanningTree X id E T) ∧ (steinerEdges P T).card ≤ b

/-- **Input of Theorem 1.2** for the real RAM: the reals `|V(G)|, |E(G)|, b`; the terminal flag of
each vertex `0, …, nV − 1` (`1` for a terminal, `0` for a candidate); each edge as
`(u, v, w(uv))` in the order of the listing `Ls` (the published `edgeCells`). -/
noncomputable def budgetLayout {nV : ℕ} (P : Finset (Fin nV)) (w : Sym2 (Fin nV) → ℝ)
    (Ls : List (Fin nV × Fin nV)) (b : ℕ) : List ℝ :=
  (nV : ℝ) :: (Ls.length : ℝ) :: (b : ℝ) ::
    ((List.finRange nV).map (fun v => if v ∈ P then (1 : ℝ) else 0) ++ edgeCells w Ls)

end Supplement

end EuclidKSteiner


