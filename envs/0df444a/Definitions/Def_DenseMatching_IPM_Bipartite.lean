-- Prove2me | Definitions.Def_DenseMatching_IPM_Bipartite
-- name    : DenseMatching_IPM_Bipartite
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:38:56.574712+00:00
-- url     : https://prove2.me/theorems/8bdeacb6-90ba-4ccf-8560-328cd11de4a3
-- title:
--   §1 — the input of Theorem 1.1: a simple bipartite graph with given sides, and its maximum matching size ν(G)
-- statement:
--   An input on $n$ vertices is a finite simple bipartite graph on the vertex set $\{0,\dots,n-1\}$ with its two sides given: a map `side` sending each vertex to $L$ (`false`) or $R$ (`true`), and a list of edges $(u,v)$ with $u\in L$, $v\in R$, without repetitions (the graphs of the paper have no duplicate edges, p. 7). Any edge set is allowed, including the empty one, and the two sides may have different sizes.
--
--   A **matching** is a set of edges no two of which share a vertex. The **maximum matching size** is
--   $$\nu(G)=\max\{|M| : M\subseteq E(G)\ \text{a matching}\},$$
--   the quantity Theorem 1.1 computes.
--
--   **Formalization Note.** Edges are pairs `(u, v) : Fin n × Fin n` listed in `edges` (`List.Nodup`); since every edge goes from $L$ to $R$, two edges share a vertex exactly when their left or their right endpoints agree. `matchingNumber` is the supremum of the cardinalities over the matchings among the subsets of the edge set, a finite nonempty family (the empty set is a matching).
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), p. 1, Theorem 1.1; p. 7, §2

import Mathlib

namespace DenseMatching.IPM

/-- An input of Theorem 1.1 (p. 1): a finite simple bipartite graph on the `n` vertices
`0, …, n - 1` with its two sides given. `side v = false` puts `v` in the left side `L`,
`side v = true` in the right side `R`. The edges are listed in `edges` as pairs `(u, v)` with
`u ∈ L` and `v ∈ R`, each at most once (the graphs of the paper have no duplicate edges, p. 7).
Any edge set is allowed, including the empty one, and the sides may have different sizes. -/
structure BipartiteInput (n : ℕ) where
  /-- the side of each vertex: `false` = `L`, `true` = `R` -/
  side : Fin n → Bool
  /-- the edge list; the pair `(u, v)` joins `u ∈ L` to `v ∈ R` -/
  edges : List (Fin n × Fin n)
  /-- no duplicate edges -/
  nodup : edges.Nodup
  /-- every edge goes from `L` to `R` -/
  bipartite : ∀ uv ∈ edges, side uv.1 = false ∧ side uv.2 = true

/-- A set of `L`–`R` pairs is a matching when distinct pairs share no endpoint. (A left
endpoint never equals a right endpoint, so comparing the two coordinates separately covers every
shared vertex.) -/
def IsMatching {n : ℕ} (M : Finset (Fin n × Fin n)) : Prop :=
  ∀ a ∈ M, ∀ b ∈ M, a ≠ b → a.1 ≠ b.1 ∧ a.2 ≠ b.2

open Classical in
/-- The maximum matching size `ν(G)`: the largest cardinality of a set of edges of `G` no two of
which share a vertex (the empty set is a matching, so the value is `0` when `G` has no edge). -/
noncomputable def matchingNumber {n : ℕ} (G : BipartiteInput n) : ℕ :=
  (G.edges.toFinset.powerset.filter (fun M => IsMatching M)).sup Finset.card

end DenseMatching.IPM


