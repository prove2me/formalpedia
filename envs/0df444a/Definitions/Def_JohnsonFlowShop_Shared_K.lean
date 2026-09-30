-- Prove2me | Definitions.Def_JohnsonFlowShop_Shared_K
-- name    : JohnsonFlowShop_Shared_K
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:36:56.130418+00:00
-- url     : https://prove2.me/theorems/e1dcaf1d-2a7c-4f88-ba91-0c548ab60779
-- title:
--   Johnson's quantities $K_u$ of an order (p. 62)
-- statement:
--   Items are indexed by $i \in \{0,\dots,n-1\}$ (the paper's items $1,\dots,n$ shifted by one), and an order is a permutation $\sigma$ of the items with $\sigma(k)$ the item processed in position $k$ (positions $0,\dots,n-1$). For the order $\sigma$ and a position $u$, Johnson's quantity is
--   $$
--   K_u = \sum_{l \le u} A_{\sigma(l)} - \sum_{l < u} B_{\sigma(l)} ,
--   $$
--   the total machine-1 time of the first $u+1$ positions minus the total machine-2 time of the first $u$ positions.
--
--   In the paper, for the sequence $S = 1, 2, \dots, n$ (items in their own order, 1-based), $K_u = \sum_{i=1}^{u} A_i - \sum_{i=1}^{u-1} B_i$ for $1 \le u \le n$.
--
--   It serves both missions of the series: `01-two-stage` (p. 62, PDF p. 2, Two-stage production schedule, display "In general", definition of $K_u$) and `02-three-stage` (p. 66, PDF p. 6, Three-stage production schedule, $K_u$ "as before", with the same $A$ and $B$). It is reviewed once for both.
--
--   **Formalization Note** Positions are 0-based: the Lean value at position $u$ is the paper's $K_{u+1}$ for the sequence $\sigma$.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 62, Two-stage production schedule, display "In general" (definition of K_u); p. 66, Three-stage production schedule, definition of K_u ("as before")

import Mathlib

namespace JohnsonFlowShop.Shared

/-- Johnson's quantity `K_u` for the order `σ`, with 0-based positions: for position `u`,
`K u = ∑_{l ≤ u} A (σ l) - ∑_{l < u} B (σ l)`. In the paper's 1-based indexing this is
`K_{u+1} = Σ_{i=1}^{u+1} A_i - Σ_{i=1}^{u} B_i` for the sequence `σ`. -/
def K {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (u : Fin n) : ℝ :=
  ∑ l ∈ Finset.Iic u, A (σ l) - ∑ l ∈ Finset.Iio u, B (σ l)

end JohnsonFlowShop.Shared


