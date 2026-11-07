-- Prove2me | Definitions.Def_SparseHistComm_levelMean
-- name    : SparseHistComm_levelMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:49.972193+00:00
-- url     : https://prove2.me/theorems/f684c46a-08cd-4c67-86a0-00ac1806441d
-- title:
--   Mean level $\sum_j j\,p_j$
-- statement:
--   For a probability vector $p = (p_0,\dots,p_k)$ on the covering levels, the **mean level** is $\sum_{j=0}^k j\, p_j$.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (12), p.7 (the objective)

import Mathlib

namespace SparseHistComm

/-- The mean level `∑_{j=0}^{k} j·p_j` of a law `p = (p₀, …, p_k)` on `{0, …, k}` (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), the objective
of (12), p.7). -/
noncomputable def levelMean (k : ℕ) (p : Fin (k + 1) → ℝ) : ℝ :=
  ∑ j : Fin (k + 1), (j : ℝ) * p j

end SparseHistComm


