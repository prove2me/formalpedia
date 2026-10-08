-- Prove2me | Definitions.Def_MetricGenerators_FewComponents_TJoin
-- name    : MetricGenerators_FewComponents_TJoin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:44.861663+00:00
-- url     : https://prove2.me/theorems/658afbb3-731d-4c10-b74c-cebbdeba46d4
-- title:
--   T-joins (§3, p. 389): F ⊆ E(G) with deg_F(v) odd exactly when v ∈ T; minimum T-joins; connected components of an edge set
-- statement:
--   Let $G=(V,E)$ be a graph and $T\subseteq V$. For a set $F\subseteq E$ of edges and a vertex $v$, write $\deg_F(v)$ for the number of edges of $F$ incident to $v$. Following Sebő and Tannier, $F$ is a **$T$-join** of $G$ if
--
--   $$F\subseteq E(G)\qquad\text{and}\qquad \deg_F(v)\ \text{is odd}\iff v\in T\quad\text{for every } v\in V.$$
--
--   A **minimum $T$-join** is a $T$-join $F$ with $|F|\le|F'|$ for every $T$-join $F'$ of $G$; its size is $\tau(G,T)$.
--
--   The **connected components of $F$** are the connected components of the graph $(V(F),F)$, where $V(F)$ is the set of endpoints of edges of $F$. Their number is written $\#\mathrm{comp}(F)$; the empty edge set has no components.
--
--   These notions underlie the problem MTSC of the paper: given $G$, $T$ and $k$, decide whether some minimum $T$-join has at most $k$ connected components.
--
--   **Formalization Note.** Edges are unordered pairs (`Sym2 V`) and $F$ is a `Finset` with $F\subseteq E(G)$. The paper's standing hypotheses ($G$ connected, $|T|$ even) are not part of the definition. Minimality is stated as "$|F|\le|F'|$ for every $T$-join $F'$", not as an infimum on $\mathbb N$. A component of $F$ is a connected component of the graph with edge set $F$ on the whole vertex type that contains an endpoint of an edge of $F$, so vertices not touched by $F$ are not counted. Two endpoints are in the same such component exactly when they are in the same component of $(V(F),F)$. The count is `Nat.card`, which is the true number for finite $V$.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 389, §3 (T-join); p. 390, §3 (minimum T-join, connected components, problem MTSC)

import Mathlib

namespace MetricGenerators.FewComponents

/-- The degree `deg_F(v)` of a vertex `v` in an edge set `F`: the number of edges of `F` that
contain `v` (Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393
(2004), §3, p. 389).

**Formalization Note.** Edges are unordered pairs `Sym2 V`; for a subset of the edges of a simple
graph there are no loops, so this is the usual degree in the graph `(V, F)`. -/
def edgeDeg {V : Type*} [DecidableEq V] (F : Finset (Sym2 V)) (v : V) : ℕ :=
  (F.filter (fun e => v ∈ e)).card

/-- A `T`-join of a graph `G` (Sebő and Tannier 2004, §3, p. 389): "If T is an even cardinality
subset of vertices of a connected graph G, F ⊆ E(G) is called a T-join if for all v ∈ V,
deg_F(v) is odd exactly when v is in T."

**Formalization Note.** `F` is a finite set of edges of `G`; the parity condition uses the degree
in `F` (`edgeDeg`), not in `G`. "Even cardinality" and "connected" are hypotheses of the theorems
that use the notion, not part of the definition. -/
def IsTJoin {V : Type*} [DecidableEq V] (G : SimpleGraph V) (T : Finset V)
    (F : Finset (Sym2 V)) : Prop :=
  (↑F : Set (Sym2 V)) ⊆ G.edgeSet ∧ ∀ v : V, Odd (edgeDeg F v) ↔ v ∈ T

/-- A minimum `T`-join (Sebő and Tannier 2004, §3, pp. 389–390): a `T`-join of minimum
cardinality among **all** `T`-joins of `G`; its cardinality is τ(G, T).

**Formalization Note.** Stated as "`F` is a `T`-join and `|F| ≤ |F'|` for every `T`-join `F'`"
rather than through an infimum on `ℕ` (which would be `0` on the empty set). -/
def IsMinTJoin {V : Type*} [DecidableEq V] (G : SimpleGraph V) (T : Finset V)
    (F : Finset (Sym2 V)) : Prop :=
  IsTJoin G T F ∧ ∀ F' : Finset (Sym2 V), IsTJoin G T F' → F.card ≤ F'.card

/-- The graph with edge set `F` on the vertex type `V` (loops, if any, are dropped). -/
def edgeGraph {V : Type*} (F : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))

/-- `V(F)`: the set of endpoints of edges of `F`. -/
def edgeSupport {V : Type*} (F : Finset (Sym2 V)) : Set V :=
  {v | ∃ e ∈ F, v ∈ e}

/-- The connected components of an edge set `F` (Sebő and Tannier 2004, §3, p. 390: "a minimum
cardinality T-join F with k connected components"): the connected components of the graph
`(V(F), F)`.

**Formalization Note.** They are represented as the connected components of `edgeGraph F` (on the
whole vertex type) that contain a vertex of `V(F)`. The vertices outside `V(F)`, which are isolated
in `edgeGraph F`, are **not** components of `F`. Two vertices of `V(F)` lie in the same component
of `edgeGraph F` exactly when they lie in the same component of `(V(F), F)`, since every vertex of
a walk in `edgeGraph F` is an endpoint of an edge of `F`. -/
def components {V : Type*} (F : Finset (Sym2 V)) : Set (edgeGraph F).ConnectedComponent :=
  {c | ∃ v ∈ edgeSupport F, (edgeGraph F).connectedComponentMk v = c}

/-- The number of connected components of the edge set `F`, i.e. of the graph `(V(F), F)`; the
empty edge set has `0` components.

**Formalization Note.** `Nat.card` of the set `components F`; it is the true count whenever `V`
is finite (the only case used). -/
noncomputable def numComponents {V : Type*} (F : Finset (Sym2 V)) : ℕ :=
  Nat.card (components F)

end MetricGenerators.FewComponents


