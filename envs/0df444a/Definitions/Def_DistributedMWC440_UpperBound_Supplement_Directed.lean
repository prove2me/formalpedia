-- Prove2me | Definitions.Def_DistributedMWC440_UpperBound_Supplement_Directed
-- name    : DistributedMWC440_UpperBound_Supplement_Directed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:47:25.826874+00:00
-- url     : https://prove2.me/theorems/f9ac8e5f-ce1b-48d3-99ab-c679b0e105ca
-- title:
--   Directed simple cycles, the directed optimum, and the Erdős girth conjecture
-- statement:
--   A **directed simple cycle** of a digraph $G$ is a cyclic sequence of $L\ge 2$ pairwise distinct vertices $v_0,\dots,v_{L-1}$ with an arc $v_i\to v_{i+1 \bmod L}$ for every $i$. In the unweighted setting its weight is its number of arcs $L$, and the directed optimum is
--
--   $$
--   \mathrm{OPT}(G)=\inf\{L(C) : C \text{ a directed simple cycle of } G\}\in\mathbb N\cup\{\infty\},
--   $$
--
--   which is $\infty$ for an acyclic digraph (the same convention as the base mission's undirected optimum).
--
--   For an integer $k\ge 1$, the **Erdős girth conjecture** (bipartite form, Conjecture 1.2) for $k$ asserts that there are a constant $c>0$ and a threshold $n_0$ such that for every $n\ge n_0$ there is a bipartite simple graph on exactly $n$ vertices with at least $c\,n^{1+1/k}$ edges and girth greater than $2k$ (a forest has infinite girth).
--
--   These objects are used by the lower bounds (Theorems 2 and 5) and the gap lemmas (Lemmas 8.1 and 8.4). The conjecture is a hypothesis of those theorems only, never an axiom.
--
--   **Formalization Note** Digraphs are Mathlib `Digraph`s; a cycle carries its length, an injective vertex map from `Fin L`, and its arcs. The conjecture is stated per `k` with Mathlib's extended girth `egirth` and 2-colourability for bipartiteness. The printed "for all $n\ge1$" with $\Omega$ is read asymptotically: literally, a bipartite graph on one vertex has no edge.
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf (SHA-256 cdee21a6e698b7d3caf34f1990ab2132af424195b394467946a89faadca70ac1), §1, printed pp. 1–3 / PDF pp. 3–5 (Definition 1.1, Conjecture 1.2); §8.1, printed p. 44 / PDF p. 46.

import Mathlib
import Definitions.Def_DistributedMWC440_UpperBound_Graph

open scoped ENNReal

noncomputable section

namespace DistributedMWC440.UpperBound.Supplement

/-!
Chang–Chen–Dey–Jiang–Mishra–Nguyen–Yang, *The Complexity of Distributed Minimum Weight Cycle
Approximation*, STOC 2027 submission #440 (October 2026). Directed simple cycles and the directed
optimum (§1, printed pp. 1–2 / PDF pp. 3–4; §8.1, printed p. 44 / PDF p. 46), and the bipartite
Erdős girth conjecture (Conjecture 1.2, printed p. 3 / PDF p. 5).
-/

/-- A directed simple cycle of a digraph: `len ≥ 2` pairwise distinct vertices
`vert 0, …, vert (len-1)` with an arc from each to the next, cyclically. Its weight in the
unweighted setting is its number of arcs, `len`. Loops are never used (`len ≥ 2`, injectivity). -/
structure DCycle {V : Type} (G : Digraph V) where
  len : ℕ
  two_le : 2 ≤ len
  vert : Fin len → V
  injective : Function.Injective vert
  adj : ∀ i : Fin len, G.Adj (vert i) (vert ⟨(i.val + 1) % len, Nat.mod_lt _ (by omega)⟩)

/-- The arc `a → b` is one of the arcs of the directed cycle `C`. -/
def DCycle.HasArc {V : Type} {G : Digraph V} (C : DCycle G) (a b : V) : Prop :=
  ∃ i : Fin C.len, C.vert i = a ∧
    C.vert ⟨(i.val + 1) % C.len, Nat.mod_lt _ (by have := C.two_le; omega)⟩ = b

/-- Directed unweighted OPT: the least number of arcs of a directed simple cycle, in the extended
nonnegative reals (`⊤` for an acyclic digraph), mirroring the base `optimum`. -/
def dOptimum {V : Type} (G : Digraph V) : ℝ≥0∞ :=
  ⨅ C : DCycle G, (C.len : ℝ≥0∞)

/-- Conjecture 1.2 (Erdős girth conjecture, bipartite form) for one integer `k`: there are a
constant `c > 0` and a threshold `n₀` such that for every `n ≥ n₀` some bipartite simple graph on
exactly `n` vertices has at least `c · n^(1+1/k)` edges and girth greater than `2k`
(an acyclic graph has girth `⊤`). -/
def ErdosGirth (k : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ G : SimpleGraph (Fin n),
    G.Colorable 2 ∧ c * (n : ℝ) ^ (1 + 1 / (k : ℝ)) ≤ (G.edgeSet.ncard : ℝ) ∧
    ((2 * k : ℕ) : ℕ∞) < G.egirth

end DistributedMWC440.UpperBound.Supplement


