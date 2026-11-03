-- Prove2me | Definitions.Def_SparseBatchBandit_gramSum
-- name    : SparseBatchBandit_gramSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:04.827855+00:00
-- url     : https://prove2.me/theorems/fe288802-e679-4df3-9849-b5ce14197a09
-- title:
--   Empirical covariance sum
-- statement:
--   For a set $S$ of rounds,
--
--   $$
--   \sum_{t\in S}x_{t,a_t}x_{t,a_t}^\top .
--   $$
--
--   The paper's matrix $D_{m,j}$ is this sum with $S=T_m^{(j)}$.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, §4.2.1, p.17

import Mathlib

namespace SparseBatchBandit

/-- The empirical covariance sum `∑_{t∈S} x_{t,a_t} x_{t,a_t}⊤` over a set `S` of rounds, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4,
§4.2.1, p.17 (PDF 17). `D_{m,j}` is the case `S = T_m^{(j)}`. -/
def gramSum {T K d : ℕ} (c : Fin T → Fin K → Fin d → ℝ) (a : Fin T → Fin K)
    (S : Finset (Fin T)) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ t ∈ S, Matrix.vecMulVec (c t (a t)) (c t (a t))

end SparseBatchBandit


