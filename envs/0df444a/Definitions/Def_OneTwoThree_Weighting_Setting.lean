-- Prove2me | Definitions.Def_OneTwoThree_Weighting_Setting
-- name    : OneTwoThree_Weighting_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:24.997824+00:00
-- url     : https://prove2.me/theorems/e64f17bf-866d-4fb8-96e4-afa45e6a4c44
-- title:
--   pp. 1, 2, 7 — edge-weightings, the weighted degree $s_\omega$, vertex-coloring weightings, components $K_2$, good R-B-partitions
-- statement:
--   This file fixes the objects of Keusch's solution of the 1-2-3 Conjecture. Throughout, $G=(V,E)$ is a finite simple graph and $N(v)$ is the neighbourhood of a vertex $v$.
--
--   1. **Edge-weightings.** A $k$-edge-weighting of $G$ is a function $\omega:E\to\{1,\dots,k\}$.
--   2. **Weighted degree.** For a vertex $v$, its weighted degree is
--   $$s_\omega(v)=\sum_{w\in N(v)}\omega(\{v,w\}).$$
--   3. **Vertex-coloring weightings.** Two vertices $v,w$ have a *coloring conflict* if $\{v,w\}\in E$ and $s_\omega(v)=s_\omega(w)$. The weighting $\omega$ is *vertex-coloring* if there is no coloring conflict, i.e. the weighted degrees form a proper vertex coloring of $G$.
--   4. **No component $K_2$.** $G$ has no connected component isomorphic to $K_2$, the graph consisting of a single edge.
--   5. **Good R-B-partitions (Definition 6).** Let $U\subseteq V$. A pair $(R,B)$ of disjoint vertex sets with $R\cup B=U$ is a *good R-B-partition* of the induced subgraph $G[U]$ if $R$ is an independent set, the bipartite subgraph $G(R,B)$ (vertex set $R\cup B$, edge set the edges of $G$ with one end in $R$ and the other in $B$) is connected, and $|B|\equiv 0\pmod 2$. For $U=V$ this is Definition 6 for $G$; for $U=V\setminus\{v_0\}$ it is a good R-B-partition of $G[V\setminus\{v_0\}]$, as used in Lemmas 8 and 9.
--
--   These are the objects of §1 (p. 1) and §§2–3 (pp. 2, 7) of the paper; every statement of the mission is phrased with them.
--
--   **Formalization Note** The vertex type is finite (weighted degrees are finite sums). An edge-weighting is a function $\omega$ on all unordered pairs `Sym2 V → ℕ`; the predicate `IsWeighting G k ω` constrains only its values on edges of $G$ to lie in $\{1,\dots,k\}$, and the values on non-edges never enter any statement. Since $\{v,w\}=\{w,v\}$ in `Sym2`, the single sum `wdeg` equals both $\sum_{w\in N(v)}\omega(\{v,w\})$ and $\sum_{u\in N(v)}\omega(\{u,v\})$. A component isomorphic to $K_2$ is expressed with Mathlib's connected components (`C.toSimpleGraph`, the subgraph induced on the component) and graph isomorphism with the complete graph on two vertices. In a good R-B-partition, connectivity is that of $G(R,B)$ induced on the vertex set $R\cup B$ (Mathlib's `Connected` includes nonemptiness), and independence of $R$ in $G$ coincides with independence in $G[U]$ because $R\subseteq U$.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 1, §1 (k-edge-weighting, weighted degree, coloring conflict, vertex-coloring); p. 2, Theorem 1 (no component isomorphic to K2) and §2 notation (G(S,T), deg_W); p. 7, Definition 6 (good R-B-partition)

import Mathlib

namespace OneTwoThree.Weighting

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weighted degree `s_ω(v) = ∑_{w ∈ N(v)} ω({v, w})` of a vertex `v` under an edge-weighting
`ω` (Keusch, p. 1). The weighting is a function on unordered pairs; only its values on edges of `G`
enter the sum. -/
def wdeg (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → ℕ) (v : V) : ℕ :=
  ∑ w ∈ G.neighborFinset v, ω s(v, w)

/-- `ω` is a `k`-edge-weighting of `G`: every edge of `G` receives a weight in `{1, …, k}`.
Values of `ω` on pairs that are not edges of `G` are unconstrained and irrelevant (p. 1). -/
def IsWeighting (G : SimpleGraph V) (k : ℕ) (ω : Sym2 V → ℕ) : Prop :=
  ∀ e ∈ G.edgeSet, ω e ∈ Finset.Icc 1 k

/-- `ω` is vertex-coloring: no edge `{v, w}` of `G` is a coloring conflict, i.e. adjacent vertices
have different weighted degrees (p. 1). -/
def IsVertexColoring (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → ℕ) : Prop :=
  ∀ v w, G.Adj v w → wdeg G ω v ≠ wdeg G ω w

/-- No connected component of `G` is isomorphic to `K₂` (the hypothesis of Theorem 1, p. 2). -/
def NoK2Component (G : SimpleGraph V) : Prop :=
  ∀ C : G.ConnectedComponent, IsEmpty (C.toSimpleGraph ≃g (⊤ : SimpleGraph (Fin 2)))

/-- Definition 6 (p. 7), stated relative to a vertex set `U`: `(R, B)` is a good R-B-partition of
the induced subgraph `G[U]` if `R` and `B` are disjoint with union `U`, `R` is independent, the
bipartite subgraph `G(R, B)` (vertex set `R ∪ B`, edges of `G` between `R` and `B`) is connected,
and `|B|` is even. `U = univ` gives Definition 6 for `G` itself; `U = {v₀}ᶜ` gives a good
R-B-partition of `G[V ∖ {v₀}]`. -/
def IsGoodPartition (G : SimpleGraph V) (U R B : Finset V) : Prop :=
  Disjoint R B ∧ R ∪ B = U ∧ G.IsIndepSet (R : Set V) ∧
    ((G.between (R : Set V) (B : Set V)).induce ((R ∪ B : Finset V) : Set V)).Connected ∧
    Even #B

end OneTwoThree.Weighting


