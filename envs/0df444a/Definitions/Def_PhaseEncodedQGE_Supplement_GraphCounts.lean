-- Prove2me | Definitions.Def_PhaseEncodedQGE_Supplement_GraphCounts
-- name    : PhaseEncodedQGE_Supplement_GraphCounts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:28:33.858081+00:00
-- url     : https://prove2.me/theorems/47241657-4da6-4a70-9fb4-b4fceba2e9e3
-- title:
--   Codegree, pair census $N_{a,k}$, cycle counts $C_\ell$ and the $K_4-e$ count $D_\diamond$
-- statement:
--   Let $G$ be a simple graph on the vertex set $\{0,\dots,n-1\}$ and write $N(v)$ for the neighbourhood of $v$.
--
--   1. The **codegree** of two vertices is $k=|N(u)\cap N(v)|$, and their **adjacency label** is $a=\mathbf 1[uv\in E]\in\{0,1\}$.
--   2. The **pair census** $N_{a,k}(G)$ is the number of unordered pairs $\{u,v\}$, $u\ne v$, of class $(a,k)$. On cubic graphs the realizable classes are $(0,0),\dots,(0,3),(1,0),(1,1),(1,2)$.
--   3. $C_\ell(G)$ is the number of $\ell$-cycles of $G$, counted as subgraphs: each cycle once, not as closed walks or ordered tuples.
--   4. $D_\diamond(G)$ is the number of (not necessarily induced) copies of $K_4-e$ in $G$; $K_4$ contains six.
--
--   These are the graph invariants that the two- and three-defect layers and the second-order purity read: the two-defect block is the pair census, the girth-five three-defect histograms are functions of $(n,C_5,C_6)$, and the purity closure is in $C_3$, $C_4$, $D_\diamond$.
--
--   **Formalization Note** Unordered pairs are counted as ordered pairs $u<v$. A cycle subgraph is determined by its edge set, so $C_\ell$ counts edge sets that are the edge set of a closed walk which is a cycle of length $\ell$ (it is $0$ for $\ell<3$). A simple graph with five edges on exactly four vertices is $K_4-e$, so $D_\diamond$ counts five-edge subsets covering exactly four vertices. All are defined for every simple graph, not through the cubic incidence identities (5).
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), §2, p.5 (PDF p.6), 'Profiles, extremal counts and the pair census', eq. (5); App. A.1.5, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_PhaseEncodedQGE_GraphNbhd
set_option autoImplicit false

namespace PhaseEncodedQGE.Supplement

/-- The codegree `k = |N(u) ∩ N(v)|` of two vertices (Miller, Lee, *Structural Accessibility in
Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), §2, p.5,
"Profiles, extremal counts and the pair census"). -/
noncomputable def codegree {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : ℕ :=
  (nbrs G u ∩ nbrs G v).card

open Classical in
/-- The adjacency label `a = 1[uv ∈ E]` of a pair, as a natural number `0` or `1` (§2, p.5). -/
noncomputable def adjBit {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : ℕ :=
  if G.Adj u v then 1 else 0

open Classical in
/-- The pair census `N_{a,k}(G)`: the number of unordered pairs `{u, v}`, `u ≠ v`, of class
`(a, k)`, i.e. with `1[uv ∈ E] = a` and `|N(u) ∩ N(v)| = k` (§2, p.5).

**Formalization Note** An unordered pair is counted once, as the ordered pair `u < v`. The
census is defined for every `a, k ∈ ℕ`; it vanishes unless `a ≤ 1`, and on cubic graphs unless
`k ≤ 3`. -/
noncomputable def pairCensus {n : ℕ} (G : SimpleGraph (Fin n)) (a k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => p.1 < p.2 ∧ adjBit G p.1 p.2 = a ∧ codegree G p.1 p.2 = k)).card

open Classical in
/-- The number `C_ℓ(G)` of `ℓ`-cycles of `G`, counted as subgraphs (§2, p.5, eq. (5); App. A.1.5,
p.18): each cycle is counted once, not as a closed walk and not as an ordered tuple.

**Formalization Note** A cycle subgraph is determined by its edge set, so `C_ℓ(G)` is the number
of edge sets `S ⊆ E(G)` that are the edge set of some closed walk of `G` which is a cycle
(`SimpleGraph.Walk.IsCycle`: length at least three, no repeated vertex) of length `ℓ`. It is
defined for every simple graph, not through the incidence identities (5) of cubic graphs, and is
`0` for `ℓ < 3`. -/
noncomputable def cycleCount {n : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) : ℕ :=
  (G.edgeFinset.powerset.filter (fun S => ∃ u : Fin n, ∃ p : G.Walk u u,
    p.IsCycle ∧ p.length = ℓ ∧ p.edges.toFinset = S)).card

open Classical in
/-- The number `D⋄(G) = N_{K₄−e}(G)` of (not necessarily induced) copies of `K₄ − e` in `G`
(§2, p.5, below eq. (5)); `K₄` itself contains six.

**Formalization Note** A copy of `K₄ − e` is a subgraph, hence determined by its five edges, and a
simple graph with five edges on exactly four vertices is `K₄ − e`. So `D⋄(G)` is the number of
five-element edge sets `S ⊆ E(G)` whose edges cover exactly four vertices. This is the subgraph
count for every simple graph; on cubic graphs it equals `∑_k (k choose 2) N_{1,k}` by (5). -/
noncomputable def diamondCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  (G.edgeFinset.powerset.filter (fun S => S.card = 5 ∧
    ((Finset.univ : Finset (Fin n)).filter (fun v => ∃ e ∈ S, v ∈ e)).card = 4)).card

end PhaseEncodedQGE.Supplement


