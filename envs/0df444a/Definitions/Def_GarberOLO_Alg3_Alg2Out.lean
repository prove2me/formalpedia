-- Prove2me | Definitions.Def_GarberOLO_Alg3_Alg2Out
-- name    : GarberOLO_Alg3_Alg2Out
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:55:08.73442+00:00
-- url     : https://prove2.me/theorems/e5f04bc1-9d9a-4f9f-853f-232283eac621
-- title:
--   Output record of Algorithm 2
-- statement:
--   An output of Algorithm 2 records
--
--   1. the returned point $\tilde y$,
--   2. the number $N$ of oracle outputs in the returned decomposition, the weights $(a_1, \dots, a_N)$ and the oracle outputs $(v_1, s_1), \dots, (v_N, s_N)$,
--   3. the number $k$ of times the loop was entered,
--   4. the total number of calls to the approximation oracle.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Algorithm 2, line 9, p. 12; Lemma 7, p. 12

import Mathlib

namespace GarberOLO.Alg3

/-- **The output of Algorithm 2.**
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Algorithm 2, line 9, p. 12: "return ỹ, (a₁, …, a_N), {(v₁, s₁), …, (v_N, s_N)}"; Lemma 7,
p. 12: "if the for loop was entered a total number of k times … the overall number of queries
to the approximation oracle".

A value `o : Alg2Out d` records the returned point `o.yt` (ỹ), the number `o.N` of Ellipsoid
iterations of the last procedure call, the weights `o.a` (a₁, …, a_N), the oracle outputs
`o.vs` ((vᵢ, sᵢ)), the number `o.loops` of times the loop was entered (the paper's k), and the
total number `o.calls` of oracle calls made by the run. -/
structure Alg2Out (d : ℕ) where
  /-- The number N of oracle outputs in the returned decomposition. -/
  N : ℕ
  /-- The returned point ỹ. -/
  yt : EuclideanSpace ℝ (Fin d)
  /-- The returned weights (a₁, …, a_N). -/
  a : Fin N → ℝ
  /-- The returned oracle outputs (vᵢ, sᵢ). -/
  vs : Fin N → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)
  /-- The number k of times the loop was entered. -/
  loops : ℕ
  /-- The total number of calls to the approximation oracle. -/
  calls : ℕ

end GarberOLO.Alg3


