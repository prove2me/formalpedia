-- Prove2me | Definitions.Def_LabelConnected_Treewidth_Multigraph
-- name    : LabelConnected_Treewidth_Multigraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:26:33.557767+00:00
-- url     : https://prove2.me/theorems/15a439f2-5f1b-477a-b13b-0296679eca7a
-- title:
--   Multigraphs with an endpoint map: support, connectivity, components, cycles, forests, spanning trees, degrees
-- statement:
--   A **multigraph** $G$ has vertex set $V = \{0, \dots, n-1\}$ and a finite set $E$ of edges, each edge $e$ with an ordered pair of endpoints $\mathrm{ends}(e) = (u, w)$; the orientation carries no meaning. The edge $e$ **joins** $u$ and $w$ if $\mathrm{ends}(e) \in \{(u,w), (w,u)\}$. It is a **loop** if $u = w$; two edges with the same unordered endpoint pair are **parallel** and remain distinct edges. A graph given as a list of $m$ endpoint pairs has edge set $\{0, \dots, m-1\}$, edge $i$ being the $i$-th pair.
--
--   For $F \subseteq E$, the graph $(V, F)$ keeps every vertex; $V(F)$ is the set of endpoints of $F$. Its **components** are those of the simple graph on $V$ in which $u \ne w$ are adjacent when some edge of $F$ joins them, and $(V, F)$ is **connected** if any two vertices are joined by a path in it. The **support** of $G$ is this simple graph for $F = E$: loops deleted, each nonempty parallel class replaced by one edge.
--
--   A **cycle** of length $\ell \ge 1$ is a closed walk $v_0 e_1 v_1 \cdots e_\ell v_\ell$ with $v_\ell = v_0$, pairwise distinct edges and pairwise distinct vertices $v_0, \dots, v_{\ell-1}$; a loop is a cycle of length one and two parallel edges form a cycle of length two. $E(C)$ and $V(C)$ are its edges and vertices. $(V, F)$ is a **forest** if no cycle has all its edges in $F$; a **spanning tree** is an edge set $T$ with $(V, T)$ a connected forest. The **degree** $\deg_F(v)$ counts the edges of $F$ at $v$ with multiplicity, a loop twice; the **maximum degree** of $G$ is $\max_v \deg_E(v)$.
--
--   **Formalization Note.** `ends : E → Fin n × Fin n` over a `Fintype E`; `ofList es` is the multigraph of an edge list; `restrict ends S` is $(V, S)$ with edge type the subtype of $S$. `adjGraph`, `support`, `SpansConnected` (`Preconnected`, so the vertex-free graph counts as connected), `numComponents` (`Nat.card` of the connected components), `compOf`, `Cycle` with `vertAt`/`edgeAt` (indices modulo the length), `edgeSet`, `vertSet`, `IsForest`, `IsSpanningTree`, `mdeg`, `maxDeg`.
-- source:
--   Klasing, Mertzios, Molter, Morawietz, Spirakis, Recognizing Label-Connected Graphs, arXiv:2611.05144 (PDF sha256 8dde27a5…), §2, p. 6, Graphs

import Mathlib

open Classical

namespace LabelConnected.Treewidth

/-! # Multigraphs as edge maps: support, connectivity, components, cycles, forests, spanning trees

Klasing, Mertzios, Molter, Morawietz, Spirakis, *Recognizing Label-Connected Graphs*,
arXiv:2611.05144 (PDF sha256 8dde27a5…), §2, p. 6, "Graphs.": "Unless stated otherwise, graphs are
finite undirected multigraphs, with parallel edges treated as distinct. […] For F ⊆ E(G), the graph
(V(G), F) retains isolated vertices, and V(F) is the set of endpoints of F. […] The support of a
multigraph is the simple graph obtained by deleting loops and replacing each nonempty parallel class
by one edge. A path has no repeated vertices; a path consisting of one vertex is allowed. A cycle of
length ℓ ≥ 1 is a closed walk v0e1v1 · · · eℓvℓ with vℓ = v0, pairwise distinct edges e1, . . . , eℓ,
and pairwise distinct vertices v0, . . . , vℓ−1; we identify it with the subgraph formed by these
vertices and edges. […] A forest contains no cycle; in particular, it contains no loop and no pair
of parallel edges. A spanning forest includes every vertex, and isolated vertices count as
components."

**Formalization Note.** A multigraph has vertex set `Fin n` and a finite edge type `E` with an
endpoint map `ends : E → Fin n × Fin n`; a loop is an edge with equal endpoints, and two distinct
edges with the same endpoint pair (in either orientation) are parallel. A graph given as a list of
endpoint pairs is `ofList es` with `E = Fin es.length` (edge `i` is the `i`-th pair). A sub-multigraph
`(V(G), S)` for `S : Finset E` is `restrict ends S`, with edge type the subtype `↥S` and every vertex
kept. Connectivity of `(V(G), S)` is `Preconnected` of the simple graph `adjGraph ends S` (loops and
multiplicities do not affect it); in particular the graph with no vertex counts as connected. -/

variable {n : ℕ} {E : Type} [Fintype E] [DecidableEq E]

/-- The multigraph on `Fin n` whose `i`-th edge is the `i`-th pair of the list `es`. -/
def ofList (es : List (Fin n × Fin n)) : Fin es.length → Fin n × Fin n := es.get

/-- The sub-multigraph `(V(G), S)`: same vertices, edges the members of `S`. -/
def restrict (ends : E → Fin n × Fin n) (S : Finset E) : S → Fin n × Fin n :=
  fun e => ends e.1

/-- Edge `e` joins `u` and `w` (in either orientation; `u = w` for a loop). -/
def Joins (ends : E → Fin n × Fin n) (e : E) (u w : Fin n) : Prop :=
  ends e = (u, w) ∨ ends e = (w, u)

/-- `e` is a loop. -/
def IsLoop (ends : E → Fin n × Fin n) (e : E) : Prop := (ends e).1 = (ends e).2

/-- `e` and `f` have the same unordered endpoint pair (they lie in one parallel class). -/
def Parallel (ends : E → Fin n × Fin n) (e f : E) : Prop :=
  Sym2.mk (ends e) = Sym2.mk (ends f)

/-- The endpoints `V(F)` of an edge set `F`. -/
noncomputable def vertsOf (ends : E → Fin n × Fin n) (F : Finset E) : Finset (Fin n) :=
  F.biUnion fun e => {(ends e).1, (ends e).2}

/-- The simple graph on `Fin n` underlying `(V(G), S)`: `u ~ w` iff `u ≠ w` and some edge of `S`
joins `u` and `w`. Loops and multiplicities are forgotten; connectivity is unaffected by them. -/
def adjGraph (ends : E → Fin n × Fin n) (S : Set E) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u w => ∃ e ∈ S, ends e = (u, w)

/-- **The support** of a multigraph (p. 6): delete loops, replace each nonempty parallel class by
one edge. -/
def support (ends : E → Fin n × Fin n) : SimpleGraph (Fin n) := adjGraph ends Set.univ

/-- The graph `(V(G), S)` is connected (every two vertices are joined by a path in it). -/
def SpansConnected (ends : E → Fin n × Fin n) (S : Finset E) : Prop :=
  (adjGraph ends (S : Set E)).Preconnected

/-- The number of components of `(V(G), S)`; isolated vertices count as components. -/
noncomputable def numComponents (ends : E → Fin n × Fin n) (S : Finset E) : ℕ :=
  Nat.card (adjGraph ends (S : Set E)).ConnectedComponent

/-- The component of `v` in `(V(G), S)`. -/
def compOf (ends : E → Fin n × Fin n) (S : Finset E) (v : Fin n) :
    (adjGraph ends (S : Set E)).ConnectedComponent :=
  (adjGraph ends (S : Set E)).connectedComponentMk v

/-- **A cycle** of length `len ≥ 1` (p. 6): a closed walk `v₀ e₁ v₁ ⋯ e_len v_len` with
`v_len = v₀`, pairwise distinct edges and pairwise distinct vertices `v₀, …, v_{len−1}`. Here
`vert i = vᵢ` and `edge i = e_{i+1}` joins `vᵢ` and `v_{i+1 mod len}`. A cycle of length one is a
loop, a cycle of length two is a pair of parallel edges. -/
structure Cycle (ends : E → Fin n × Fin n) where
  len : ℕ
  len_pos : 0 < len
  vert : Fin len → Fin n
  edge : Fin len → E
  vert_inj : Function.Injective vert
  edge_inj : Function.Injective edge
  joins : ∀ i : Fin len,
    Joins ends (edge i) (vert i) (vert ⟨(i.val + 1) % len, Nat.mod_lt _ len_pos⟩)

/-- The `k`-th vertex of the cycle, indices modulo its length. -/
def Cycle.vertAt {ends : E → Fin n × Fin n} (c : Cycle ends) (k : ℕ) : Fin n :=
  c.vert ⟨k % c.len, Nat.mod_lt _ c.len_pos⟩

/-- The `k`-th edge of the cycle (joining `vertAt k` and `vertAt (k + 1)`), indices modulo its
length. -/
def Cycle.edgeAt {ends : E → Fin n × Fin n} (c : Cycle ends) (k : ℕ) : E :=
  c.edge ⟨k % c.len, Nat.mod_lt _ c.len_pos⟩

/-- The edge set `E(C)` of a cycle. -/
def Cycle.edgeSet {ends : E → Fin n × Fin n} (c : Cycle ends) : Finset E :=
  Finset.univ.image c.edge

/-- The vertex set `V(C)` of a cycle. -/
def Cycle.vertSet {ends : E → Fin n × Fin n} (c : Cycle ends) : Finset (Fin n) :=
  Finset.univ.image c.vert

/-- `(V(G), F)` is a **forest**: no cycle of `G` has all its edges in `F` (so `F` contains no loop
and no two parallel edges). -/
def IsForest (ends : E → Fin n × Fin n) (F : Finset E) : Prop :=
  ∀ c : Cycle ends, ¬ c.edgeSet ⊆ F

/-- `T` is the edge set of a **spanning tree**: `(V(G), T)` is a connected forest. -/
def IsSpanningTree (ends : E → Fin n × Fin n) (T : Finset E) : Prop :=
  IsForest ends T ∧ SpansConnected ends T

/-- Degree of `v` in `(V(G), S)`, counting multiplicities (a loop counts twice). -/
noncomputable def mdeg (ends : E → Fin n × Fin n) (S : Finset E) (v : Fin n) : ℕ :=
  (S.filter fun e => (ends e).1 = v).card + (S.filter fun e => (ends e).2 = v).card

/-- Maximum degree of the multigraph, counting multiplicities (`0` when there is no vertex). -/
noncomputable def maxDeg (ends : E → Fin n × Fin n) : ℕ :=
  Finset.univ.sup (mdeg ends Finset.univ)

end LabelConnected.Treewidth


