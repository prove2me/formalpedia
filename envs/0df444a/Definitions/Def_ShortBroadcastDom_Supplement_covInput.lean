-- Prove2me | Definitions.Def_ShortBroadcastDom_Supplement_covInput
-- name    : ShortBroadcastDom_Supplement_covInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:38:20.472781+00:00
-- url     : https://prove2.me/theorems/5cb05a05-c3ee-43f6-a13d-b5cfd6f3410e
-- title:
--   Local input of a general covering instance
-- statement:
--   In a general covering instance $(R,C,c)$ on a network $G$ with vertex identifiers, every vertex $v$ knows:
--
--   1. whether it is a demand;
--   2. its cost $c_v$;
--   3. if it is a demand, whether $v\in C(v)$;
--   4. the identifiers of the neighbouring demands $r$ with $v\in C(r)$;
--   5. if it is a demand, the identifiers of its neighbours $u\in C(v)$.
--
--   This is exactly the information that the paper grants: "Every vertex knows whether it is a demand. For each demand $r$ and neighboring candidate $v$, both vertices know whether $v$ is allowed to cover $r$, and each demand also knows whether it can cover itself." The covering relation enters only at demands, along edges and at the demand itself.
--
--   **Formalization Note** The broadcast model used here has no port numbers, so the per-edge incidence bits are given as sets of neighbour identifiers; every vertex can learn its neighbours' identifiers in one broadcast round anyway.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §1.1, p.2 (PDF p.5); §6.6, p.40 (PDF p.43)

import Mathlib

namespace ShortBroadcastDom.Supplement

/-- The local input of a vertex in a general covering instance:
`(demand bit, cost, self-cover bit, covered demands, own candidates)`. -/
abbrev CovInput : Type := Bool × ℕ × Bool × Finset ℕ × Finset ℕ

/-- **The local input of a general covering instance** `(R, C, c)` at the vertex `v`, for a graph
`G` with identifiers `id`.

Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §1.1, p.2 (PDF 5): "Each candidate v knows its positive integer cost cv ∈ {1, …, b} for a
fixed bound b. Every vertex knows whether it is a demand. For each demand r and neighboring
candidate v, both vertices know whether v is allowed to cover r, and each demand also knows whether
it can cover itself." §6.6, p.40 (PDF 43): "For every edge rv, both endpoints know whether
v ∈ C(r), and each demand knows whether r ∈ C(r)."

The five components are:
1. whether `v` is a demand;
2. its cost `c v`;
3. whether `v` is a demand with `v ∈ C(v)`;
4. the identifiers of the neighbouring demands `r` with `v ∈ C(r)`;
5. if `v` is a demand, the identifiers of its neighbours `u ∈ C(v)` (empty otherwise).

**Formalization Note** The broadcast model of `BroadcastAlg` has no port numbers, so the knowledge
"for the edge rv, whether v ∈ C(r)" is given as the set of identifiers of the relevant neighbours;
in one broadcast round every vertex can learn its neighbours' identifiers anyway, so this adds no
information beyond the paper's. Nothing else about the graph is in the input: the relation `C(r)`
enters only for demands `r ∈ R`, and only along edges and at `r` itself. -/
def covInput {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (id : V → ℕ) (R : Finset V) (Cov : V → Finset V) (c : V → ℕ) (v : V) : CovInput :=
  (decide (v ∈ R), c v, decide (v ∈ R ∧ v ∈ Cov v),
    ((G.neighborFinset v).filter fun r => r ∈ R ∧ v ∈ Cov r).image id,
    if v ∈ R then ((G.neighborFinset v).filter fun u => u ∈ Cov v).image id else ∅)

end ShortBroadcastDom.Supplement


