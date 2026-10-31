-- Prove2me | Definitions.Def_SQMeanEstimation_ringInf
-- name    : SQMeanEstimation_ringInf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:02.109046+00:00
-- url     : https://prove2.me/theorems/8585eb1f-4c6c-4dca-ae2a-561d3f704ffe
-- title:
--   Remainder ring $R_\infty(w)$
-- statement:
--   For an integer $k$ and $w\in\mathbb R^d$, the **remainder ring** is
--   $$
--   R_\infty(w)=\sum_{i=1}^d e_i w_i\mathbf 1_{\{|w_i|\le 2^{-k-1}\}}:
--   $$
--   the coordinates of absolute value at most $2^{-k-1}$ are kept and the others set to $0$.
--
--   **Formalization Note** $k$ is an integer and may be negative: the paper's $k=\lfloor\log(d)/q\rfloor-2$ is $-1$ or $-2$ for small $d$.
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, proof of Theorem 3.15, p.17

import Mathlib

namespace SQMeanEstimation

/-- **The remainder ring `R_∞` of a vector.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, proof of Theorem 3.15, p.17:
"R_∞(w) ≐ Σ_{i=1}^d eᵢwᵢ1_{|wᵢ|≤2^{−k−1}}".

`ringInf k w` keeps the coordinates with `|wᵢ| ≤ 2^{−k−1}` and sets the others to `0`.

**Formalization Note.** `k : ℤ` and the power is the integer power `zpow`: the paper's
`k = ⌊log(d)/q⌋ − 2` is negative for small `d` (see `ringDepth`). -/
noncomputable def ringInf {d : ℕ} (k : ℤ) (w : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if |w i| ≤ (2 : ℝ) ^ (-k - 1) then w i else 0

end SQMeanEstimation


