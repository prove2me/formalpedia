-- Prove2me | Definitions.Def_BinaryQueryLB_Supplement_StrongAlgorithm
-- name    : BinaryQueryLB_Supplement_StrongAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:49:18.917201+00:00
-- url     : https://prove2.me/theorems/5e6d17ea-7c98-4c48-a2d1-a377e1e30325
-- title:
--   Deterministic algorithm with the strong oracle $O^*$
-- statement:
--   The **strong oracle** $O^*$ answers a query $(y,v)$, with $y\in X=[-R,R]^d$ and $v\in\mathbb R^d$, by the exact pair of real numbers $\big(f(y),\langle v,g_f(y)\rangle\big)$, where $g_f(y)$ is the subgradient reported by the chart. A **deterministic algorithm with $O^*$** chooses its $t$-th query $(y_t,v_t)$, decides whether to stop, and, when it stops, chooses its output $\hat y$, all as functions of the real answers $(\varphi_1,\psi_1),\dots,(\varphi_{t-1},\psi_{t-1})$ received so far.
--
--   There is no bound on the number of queries and no restriction on the computation between queries; every query counts, including repeated ones.
--
--   **Formalization Note** An algorithm is a map from the history of answer pairs (a list of elements of $\mathbb R\times\mathbb R$, oldest first) to either a query $(y,v)\in\mathbb R^d\times\mathbb R^d$ or an output $\hat y\in\mathbb R^d$. That query points lie in $X$ is the separate predicate `StrongQueriesInBox`; that outputs lie in $X$ is part of $\varepsilon$-optimality.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.2, pp.11–12

import Mathlib

namespace BinaryQueryLB.Supplement

/-- **Deterministic algorithm with the strong oracle O\*.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.2, p.12: "The oracle `O∗` answers a query `(y, v)` with `y ∈ X` and `v ∈ R^d` by the
exact pair `(f(y), ⟨v, g_f(y)⟩)`, and a deterministic algorithm with `O∗` chooses each query and
its output as functions of the previous real answers."

**Formalization Note.** An algorithm is a map from the history of real answer pairs
`[(φ₁, ψ₁), …, (φ_{t−1}, ψ_{t−1})]` (a `List (ℝ × ℝ)`, oldest first) to either
`Sum.inl (y_t, v_t)` ("ask the query `(y_t, v_t)` next") or `Sum.inr ŷ` ("stop and output `ŷ`").
As in §2.2 there is no bound on the number of queries and no restriction on the computation between
queries; answers are exact reals, not discretized. That query points lie in `X` is the separate
predicate `StrongQueriesInBox`; that outputs lie in `X` is part of ε-optimality. ℝ^d is
`EuclideanSpace ℝ (Fin d)`. -/
abbrev StrongAlgorithm (d : ℕ) : Type :=
  List (ℝ × ℝ) → (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ⊕ EuclideanSpace ℝ (Fin d)

end BinaryQueryLB.Supplement


