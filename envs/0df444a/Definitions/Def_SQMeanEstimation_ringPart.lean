-- Prove2me | Definitions.Def_SQMeanEstimation_ringPart
-- name    : SQMeanEstimation_ringPart
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:01.592591+00:00
-- url     : https://prove2.me/theorems/4f85457e-720d-43e9-9b23-6084ca3c1a32
-- title:
--   Ring $R_j(w)$ of dynamic range 2
-- statement:
--   For $j\in\mathbb N$ and $w\in\mathbb R^d$, the **$j$-th ring** of $w$ is
--   $$
--   R_j(w)=\sum_{i=1}^d e_i w_i\mathbf 1_{\{2^{-(j+1)}<|w_i|\le 2^{-j}\}}:
--   $$
--   the coordinates whose absolute value lies in $(2^{-(j+1)},2^{-j}]$ are kept and the others set to $0$. All nonzero coordinates of $R_j(w)$ are within a factor $2$ of each other, which is the "dynamic range 2" used in the proofs of Theorems 3.13 and 3.15.
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, proof of Theorem 3.15, p.17 (as in the proof of Theorem 3.13, p.16)

import Mathlib

namespace SQMeanEstimation

/-- **The `j`-th ring of a vector.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, proof of Theorem 3.15, p.17 (as on p.16):
"Rⱼ(w) ≐ Σ_{i=1}^d eᵢwᵢ1_{2^{−(j+1)}<|wᵢ|≤2^{−j}}".

`ringPart j w` keeps the coordinates with `2^{−(j+1)} < |wᵢ| ≤ 2^{−j}` (strict lower end, closed
upper end) and sets the others to `0`.

**Formalization Note.** `j : ℕ`; the powers are `Real.rpow` with base 2. -/
noncomputable def ringPart {d : ℕ} (j : ℕ) (w : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if (2 : ℝ) ^ (-((j : ℝ) + 1)) < |w i| ∧ |w i| ≤ (2 : ℝ) ^ (-(j : ℝ)) then w i else 0

end SQMeanEstimation


