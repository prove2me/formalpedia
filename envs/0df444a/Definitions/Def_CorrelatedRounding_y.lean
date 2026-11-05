-- Prove2me | Definitions.Def_CorrelatedRounding_y
-- name    : CorrelatedRounding_y
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:36.53783+00:00
-- url     : https://prove2.me/theorems/52bb33a1-e26d-4c1e-8724-e6d880e9cd4d
-- title:
--   The lower bound $y_k=\max_i u_{ki}$
-- statement:
--   For an FC $k$,
--   $$y_k:=\max_{i} u_{ki}.$$
--   The event that FC $k$ is used contains each event $Z_i=k$, so it has probability at least $y_k$ under any rounding scheme. A scheme is $\alpha$-competitive when each FC is used with probability at most $\alpha y_k$.
--
--   **Formalization Note.** Lean takes the supremum over the finite type `Fin q`, which is the maximum when $q\ge 1$.
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, Definition 1, p.9

import Mathlib

namespace CorrelatedRounding

/-- **The lower bound `y_k := max_i u_ki`.** W. Ma, *Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders*, arXiv:2207.04774v4,
Definition 1, p.9.

The event that FC `k` is used has probability at least `y_k`, and a rounding scheme is compared to it.

**Formalization Note.** A supremum over the finite type `Fin q`, hence the maximum when `q ≥ 1`. For
`q = 0` the Lean value is `0`, and every theorem where this could matter assumes `q ≥ 1` or holds vacuously. -/
noncomputable def y {q K : ℕ} (u : Fin K → Fin q → ℝ) (k : Fin K) : ℝ :=
  ⨆ i, u k i

end CorrelatedRounding


