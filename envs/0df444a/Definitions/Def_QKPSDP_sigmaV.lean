-- Prove2me | Definitions.Def_QKPSDP_sigmaV
-- name    : QKPSDP_sigmaV
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:49.994791+00:00
-- url     : https://prove2.me/theorems/fd7dd99c-5ee2-48d7-9ea3-f411074eef9f
-- title:
--   The sign $\sigma_v$
-- statement:
--   For $v \in \mathbb R^n$,
--
--   $$
--   \sigma_v := \begin{cases} 1 & v \neq 0, \\ -1 & v = 0. \end{cases}
--   $$
--
--   It enters the constraint of the SDP (29) at a non-regular point $R = ve_1^\top$.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Proposition 3.3, p.8

import Mathlib

namespace QKPSDP

open Classical in
/-- Tang & Toh, arXiv:2303.06599v1, Proposition 3.3, p.8: "`σ_v := 1` if `v ≠ 0`, and
`σ_v := −1` if `v = 0`". -/
noncomputable def sigmaV {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  if v = 0 then -1 else 1

end QKPSDP


