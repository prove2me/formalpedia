-- Prove2me | Definitions.Def_CentralityGame_pageRank
-- name    : CentralityGame_pageRank
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:30.845109+00:00
-- url     : https://prove2.me/theorems/38fe4146-b7b8-45cf-8082-f1f0ac2fb612
-- title:
--   PageRank centrality $\pi$
-- statement:
--   For a discount factor $\beta\in(0,1)$ and an intrinsic centrality $\eta$, the **PageRank centrality** vector of a graph with normalized adjacency matrix $R$ is
--
--   $$
--   \pi=(1-\beta)(I-\beta R^\top)^{-1}\eta.
--   $$
--
--   This is the utility vector of the centrality game. Definition (2) on the page also records the series form $(1-\beta)\sum_{k\ge 0}\beta^k(R^\top)^k\eta$; the Lean definition is the closed form.
--
--   **Formalization Note** The inverse is the matrix inverse of Mathlib. For a graph and $\beta\in(0,1)$ the matrix $I-\beta R^\top$ is invertible.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §2, (2), p.6

import Mathlib
import Definitions.Def_CentralityGame_normAdj
open scoped Matrix

namespace CentralityGame

/-- The **PageRank centrality** vector of (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §2, (2), p.6):
`π = (1 - β) (I - β Rᵀ)⁻¹ η`.

**Formalization Note** `⁻¹` is Mathlib's matrix inverse, which returns `0` on a singular matrix.
That value never arises for a graph and `β ∈ (0, 1)`: `I - β Rᵀ` is then invertible
(strictly diagonally dominant), as `(2)` asserts. No invertibility hypothesis is needed. -/
noncomputable def pageRank {V : Type*} [Fintype V] [DecidableEq V] (N : V → Finset V) (β : ℝ)
    (η : V → ℝ) : V → ℝ :=
  (1 - β) • ((1 - β • (normAdj N)ᵀ)⁻¹ *ᵥ η)

end CentralityGame


