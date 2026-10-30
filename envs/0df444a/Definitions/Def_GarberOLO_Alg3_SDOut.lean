-- Prove2me | Definitions.Def_GarberOLO_Alg3_SDOut
-- name    : GarberOLO_Alg3_SDOut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:51:45.941597+00:00
-- url     : https://prove2.me/theorems/fd653ace-72d1-4b57-8433-a59d23930f78
-- title:
--   Output record of the Separation-or-Decomposition procedure
-- statement:
--   An output of the procedure run for at most $N$ iterations records
--
--   1. whether it returned a separating vector ($\mathrm{isSep}$),
--   2. the returned vector $w$ (when it did),
--   3. the $N$ outputs $(v_1, s_1), \dots, (v_N, s_N)$ of the extended oracle (when it did not),
--   4. the number of iterations executed, which equals the number of oracle calls.
--
--   It is the return type of $\mathrm{sepOrDec}$.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Lemma 5, pp. 9–10

import Mathlib

namespace GarberOLO.Alg3

/-- **The output of the Separation-or-Decomposition procedure** (Lemma 5).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Lemma 5, pp. 9–10: the procedure either "declare[s] Problem (4) feasible and return[s] the
vector w", or "complete[s] N iterations without declaring Problem (4) feasible", in which case
"(v₁, s₁), …, (v_N, s_N) [are] the outputs of the extended approximation oracle gathered
throughout the run of the algorithm".

A value `o : SDOut d N` records: `o.isSep` (`true` when a vector `w` was returned),
`o.w` (the returned vector; meaningful when `o.isSep = true`), `o.vs` (the N oracle outputs
`(vᵢ, sᵢ)` in order; meaningful when `o.isSep = false`), and `o.calls`, the number of
iterations executed, which is the number of calls to the extended oracle, hence to O_K. -/
structure SDOut (d N : ℕ) where
  /-- `true` iff the procedure returned a separating vector. -/
  isSep : Bool
  /-- The returned vector `w` (when `isSep = true`). -/
  w : EuclideanSpace ℝ (Fin d)
  /-- The oracle outputs `(vᵢ, sᵢ)`, `i = 1, …, N` (when `isSep = false`). -/
  vs : Fin N → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)
  /-- The number of iterations executed (= oracle calls). -/
  calls : ℕ

end GarberOLO.Alg3


