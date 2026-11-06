-- Prove2me | Definitions.Def_BinaryQueryLB_Algorithm
-- name    : BinaryQueryLB_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:07.368221+00:00
-- url     : https://prove2.me/theorems/4f6d9a5a-4fad-47aa-93a5-189745e43677
-- title:
--   Deterministic algorithm with local binary queries
-- statement:
--   A **deterministic algorithm with local binary queries** chooses its $t$-th query $(y_t,h_t)$, and decides whether to stop, as functions of the answers $b_1,\dots,b_{t-1}\in\{0,1\}$ received so far; when it stops after $T$ queries it outputs a point $\hat y$ that is a function of $b_1,\dots,b_T$. There is no restriction on the computation between queries and no bound on the number of queries.
--
--   **Formalization Note** An algorithm is a map from the list of answers received so far (oldest first) to either a next query or a final output. That queries lie in $X$ is a separate hypothesis; that outputs lie in $X$ is part of $\varepsilon$-optimality.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.2, pp.11–12

import Mathlib
import Definitions.Def_BinaryQueryLB_LocalQuery

namespace BinaryQueryLB

/-- **Deterministic algorithm with local binary queries.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.2, pp.11–12: "A deterministic
algorithm with local binary queries chooses its `t`-th query `(y_t, h_t)`, and decides whether to
stop, as functions of the answers `b_1, …, b_{t−1} ∈ {0, 1}` received so far. When it stops after
`T` queries, it outputs a point `ŷ ∈ X` that is a function of `b_1, …, b_T`."

**Formalization Note.** An algorithm is a map from the answer history `[b_1, …, b_{t−1}]`
(a `List Bool`, oldest first) to either `Sum.inl (y_t, h_t)` ("ask this query next") or
`Sum.inr ŷ` ("stop and output `ŷ`"). There is no bound on the number of queries, and no
restriction on the computation between queries. That query points lie in `X` is the separate
predicate `QueriesInBox`; that outputs lie in `X` is part of ε-optimality. -/
abbrev Algorithm (d : ℕ) : Type :=
  List Bool → LocalQuery d ⊕ EuclideanSpace ℝ (Fin d)

end BinaryQueryLB


