-- Prove2me | Definitions.Def_StengelZeroSum_Feasible58
-- name    : StengelZeroSum_Feasible58
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:53.656496+00:00
-- url     : https://prove2.me/theorems/f6db9e4b-d664-47e5-80d3-2e2b952e558a
-- title:
--   Feasible solutions of the system (58)
-- statement:
--   For a $k\times k$ matrix $C$ and $d\in\mathbb R^k$, a pair $(z,w)\in\mathbb R^k\times\mathbb R$ is **feasible for (58)** if
--
--   $$
--   Cz-\mathbf 1w\le d,\qquad d^\top z-w\le 0,\qquad z\ge \mathbf 0,\qquad w\ge 0 .
--   $$
--
--   The variable $w$ is a uniform slack added to the right-hand side; Theorem 8 minimizes it.
--
--   **Formalization Note** Vector inequalities are componentwise.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 8, eq. (58), p.21

import Mathlib

open Matrix

namespace StengelZeroSum

/-- `(z, w) ∈ ℝ^k × ℝ` is **feasible for (58)**,
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Theorem 8,
eq. (58), p.21:
`Cz − 1w ≤ d,  d⊤z − w ≤ 0,  z ≥ 0,  w ≥ 0`.

**Formalization Note** The `k` coordinates form an arbitrary finite type `ι`; vector
inequalities are componentwise (`Pi.le`). -/
def Feasible58 {ι : Type*} [Fintype ι] (C : Matrix ι ι ℝ) (d : ι → ℝ) (z : ι → ℝ) (w : ℝ) :
    Prop :=
  (∀ i, (C *ᵥ z) i - w ≤ d i) ∧ d ⬝ᵥ z - w ≤ 0 ∧ 0 ≤ z ∧ 0 ≤ w

end StengelZeroSum


