-- Prove2me | Definitions.Def_PConeEB_RR
-- name    : PConeEB_RR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:52.485406+00:00
-- url     : https://prove2.me/theorems/7c6063cc-0a96-422a-afd6-60103fdbd13a
-- title:
--   The space $\mathbb R^{n+1}$
-- statement:
--   The Euclidean space $\mathbb R^{n+1}$ with its usual inner product. A vector is written $x=(x_0,\bar x)$, where $x_0$ is its first (0th) entry and $\bar x\in\mathbb R^n$ is the subvector obtained by deleting $x_0$.
--
--   **Formalization Note** This is `EuclideanSpace ℝ (Fin (n + 1))`. The entry $\bar x_i$ with $i$ in $\{1,\dots,n\}$ is `x i.succ` with `i : Fin n`.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, §4, p.17

import Mathlib

namespace PConeEB

/-- The space `ℝ^{n+1}` with the usual Euclidean inner product, whose entries are numbered
`0, 1, …, n`. A vector `x` has first entry `x₀ = x 0` and tail `x̄ = (x 1, …, x n)`, written
`x i.succ` for `i : Fin n`. Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, §4, p.17. -/
abbrev RR (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

end PConeEB


