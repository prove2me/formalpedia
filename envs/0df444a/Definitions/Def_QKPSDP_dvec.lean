-- Prove2me | Definitions.Def_QKPSDP_dvec
-- name    : QKPSDP_dvec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:48.199384+00:00
-- url     : https://prove2.me/theorems/242abec0-681d-4d4c-8c1a-ced17ce21c8e
-- title:
--   The sign vector $d = 2v - e$
-- statement:
--   For $v \in \{0,1\}^n$, $d := 2v - e \in \{-1,1\}^n$, where $e$ is the all-ones vector.
--
--   It enters the SDP (29) that defines second-order stationarity at a non-regular point $R = ve_1^\top$.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Proposition 3.3, p.8

import Mathlib

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, Proposition 3.3, p.8: "`d = 2v − e`", for `v ∈ {0,1}ⁿ`
(so `d ∈ {−1,1}ⁿ`), with `e` the all-ones vector. -/
def dvec {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => 2 * v i - 1

end QKPSDP


