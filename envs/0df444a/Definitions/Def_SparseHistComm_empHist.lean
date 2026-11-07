-- Prove2me | Definitions.Def_SparseHistComm_empHist
-- name    : SparseHistComm_empHist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:25.932202+00:00
-- url     : https://prove2.me/theorems/953ae60d-a869-4c27-b7b4-02fd8f5341aa
-- title:
--   Empirical histogram $u = \frac1n\sum_i x_i$
-- statement:
--   The **empirical histogram** of an input profile $(x_1,\dots,x_n)$ is the vector
--   $$
--   u = \frac1n \sum_{i=1}^n x_i \in [0,1]^d ,
--   $$
--   whose coordinate $u(a)$ is the fraction of users whose input contains category $a$. It is the server's estimation target.
--
--   **Formalization Note** Inputs are supports and $x_i$ as a vector is its indicator vector. Every theorem using the histogram assumes $n \ge 1$.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (1), p.2

import Mathlib
import Definitions.Def_SparseHistComm_ind

namespace SparseHistComm

/-- The **empirical histogram** `u = (1/n) ∑ᵢ xᵢ` of an input profile (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (1), p.2).

**Formalization Note** Inputs are supports (`xᵢ : Finset (Fin d)`), and `xᵢ` as a vector is
`ind (x i)`. The profile is indexed by `Fin n`; every theorem that uses `empHist` assumes `n ≥ 1`. -/
noncomputable def empHist {n d : ℕ} (x : Fin n → Finset (Fin d)) : Fin d → ℝ :=
  fun a => (1 / (n : ℝ)) * ∑ i, ind (x i) a

end SparseHistComm


