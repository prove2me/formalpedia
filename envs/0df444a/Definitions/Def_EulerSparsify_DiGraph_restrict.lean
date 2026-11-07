-- Prove2me | Definitions.Def_EulerSparsify_DiGraph_restrict
-- name    : EulerSparsify_DiGraph_restrict
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:22.94502+00:00
-- url     : https://prove2.me/theorems/e2aa886d-2773-4244-bd2b-29e00c19ca6a
-- title:
--   Subgraphs $G_F$, unweighted copies $\widehat G_F$ and induced edge sets $E(G[U])$
-- statement:
--   For an edge set $F\subseteq E$:
--
--   1. the **subgraph** $G_F$ keeps the weight of every edge of $F$ and gives weight $0$ to every other edge (same weights as $G$ on $F$);
--   2. the **unweighted copy** $\widehat G_F$ (the paper's $\widehat K$, "$K$ without weight") gives weight $1$ to every edge of $F$ and $0$ to the others;
--   3. for a vertex set $U$, the **induced edge set** $E(G[U])$ consists of the edges with both endpoints in $U$; the induced subgraph is $G[U]=G_{E(G[U])}$.
--
--   **Formalization Note** A subgraph lives on the full vertex set; vertices outside its own vertex set are isolated, which changes neither its Laplacian on its vertices nor the effective resistances among them.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §3, Graphs, pp.8–9 (PDF pp.10–11); Definition 2.1 item 2, p.4

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph

namespace EulerSparsify

/-- **Subgraph with edge set `F`** (§3, "Graphs", p.8, PDF p.10).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), p.8: "We say H is a subgraph of G if the edges and vertices of H are subsets of the edges
and vertices of G (with the same weights), denoting H = G_F if E(H) = F."

`G.restrict F` keeps the weight of every edge of `F` and sets every other weight to `0`.

**Formalization Note.** A subgraph lives on the full vertex type `V`; vertices outside its vertex
set are isolated, which changes neither its Laplacian on its own vertices nor effective resistances
between them. -/
noncomputable def DiGraph.restrict {V E : Type} [DecidableEq E] (G : DiGraph V E)
    (F : Finset E) : DiGraph V E :=
  G.withWeights fun e => if e ∈ F then G.w e else 0

/-- **Unweighted copy of the subgraph with edge set `F`** (`bK`, `bG_F`; Definition 2.1 item 2,
p.4; §5.1.1, p.16): weight `1` on every edge of `F`, `0` elsewhere. -/
noncomputable def DiGraph.unitOn {V E : Type} [DecidableEq E] (G : DiGraph V E)
    (F : Finset E) : DiGraph V E :=
  G.withWeights fun e => if e ∈ F then 1 else 0

/-- **Induced edge set** `E(G[U])` (§3, p.9, PDF p.11): "For U ⊆ V, we let G[U] denote the induced
subgraph of G on U (i.e., keeping all of the edges within U)." The edges with both endpoints in
`U`; the induced subgraph is `G.restrict (G.inducedEdges U)`. -/
def DiGraph.inducedEdges {V E : Type} [Fintype E] [DecidableEq V] (G : DiGraph V E)
    (U : Finset V) : Finset E :=
  Finset.univ.filter fun e => G.head e ∈ U ∧ G.tail e ∈ U

end EulerSparsify


