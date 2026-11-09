-- Prove2me | Definitions.Def_NAMatchEst_RandAlg
-- name    : NAMatchEst_RandAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:50:32.924202+00:00
-- url     : https://prove2.me/theorems/f30567bb-9ad2-4f19-baa2-8edb5b51d13e
-- title:
--   Randomized non-adaptive algorithm in the adjacency-list model
-- statement:
--   A **randomized non-adaptive algorithm** on $n$ vertices with outputs in a set $\beta$ consists of
--
--   1. a finite seed space $\Omega$ with a probability distribution $w$ on it, $w(\omega)\ge 0$, $\sum_\omega w(\omega)=1$ (the internal randomness; the public finite distribution `WildeQIT.FinDist`);
--   2. for every seed $\omega$, a list $\mathrm{queries}(\omega)$ of queries (repetitions allowed);
--   3. an output rule that, from the seed and the answers to the queries, computes an output in $\beta$.
--
--   The queries are a function of the seed alone: they are all fixed before any answer is observed, and they may depend on the internal randomness but not on any answer. This is the paper's notion of a non-adaptive algorithm.
--
--   **Formalization Note** The output rule receives the degree answers and the neighbour answers as partial functions; a query not in the list is answered `none` (see `RandAlg.run`). The finite seed space with real weights covers every algorithm of the paper (finitely many uniform vertex samples and positions, independent Bernoulli inclusions with real probabilities).
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §2.1, p.13 (PDF 17)

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_NAMatchEst_Query

namespace NAMatchEst

/-- A **randomized non-adaptive algorithm** in the adjacency-list model on `n` vertices, with
outputs in `β`. It draws a seed `ω` from a finite probability space `(Ω, w)`; its list of queries
`queries ω` is a function of the seed alone; after all queries are answered it computes its output
from the seed and the answers.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §2.1, p.13 (PDF 17): "An algorithm in the adjacency list model is non-adaptive if all of
its degree and neighbor queries are determined before any query answers are observed. A
non-adaptive algorithm may be randomized, in which case its queries may depend on its internal
randomness, but not on the answers to any queries."

**Formalization Note**
1. Non-adaptivity is structural: `queries` has type `Ω → List (Query n)` and never sees the graph.
2. `output ω d m` receives the degree answers `d v` and the neighbour answers `m v i`; the value
   is `none` for a query the algorithm did not make (see `RandAlg.run`), so the output depends on
   the graph only through the answers to its own queries.
3. The internal randomness is a finite seed space with a probability distribution, the public
   `WildeQIT.FinDist` (real nonnegative weights summing to one). This covers the source's algorithms (finitely many uniform vertex samples and positions,
   independent Bernoulli inclusions with real probabilities). -/
structure RandAlg (n : ℕ) (β : Type) where
  /-- The seed space (internal randomness). -/
  Ω : Type
  /-- The seed space is finite. -/
  [instFintype : Fintype Ω]
  /-- The law of the seed. -/
  dist : WildeQIT.FinDist Ω
  /-- The queries issued under seed `ω` (in order, repetitions allowed). -/
  queries : Ω → List (Query n)
  /-- The output from the seed, the degree answers and the neighbour answers. -/
  output : Ω → (Fin n → Option ℕ) → (Fin n → ℕ → Option (Option (Fin n))) → β

attribute [instance] RandAlg.instFintype

end NAMatchEst


