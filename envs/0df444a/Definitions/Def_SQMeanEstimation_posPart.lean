-- Prove2me | Definitions.Def_SQMeanEstimation_posPart
-- name    : SQMeanEstimation_posPart
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:56.30559+00:00
-- url     : https://prove2.me/theorems/9e9e5881-0a73-4b78-9214-1869c59c3e82
-- title:
--   Positive part $w^+$ of a vector
-- statement:
--   For $w\in\mathbb R^d$, the **positive part** is
--   $$
--   w^+=\sum_{i=1}^d e_i w_i\mathbf 1_{\{w_i\ge0\}},
--   $$
--   i.e. the coordinates $w_i\ge0$ are kept and the negative ones are set to $0$. Together with $w^-$ it gives $w=w^+-w^-$ with both parts nonnegative.
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, proof of Theorem 3.15, p.17

import Mathlib

namespace SQMeanEstimation

/-- **Positive part of a vector.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, proof of Theorem 3.15, p.17:
"w⁺ ≐ Σ_{i=1}^d eᵢwᵢ1_{wᵢ≥0}".

`posPart w` keeps the coordinates `wᵢ ≥ 0` and sets the others to `0`. -/
noncomputable def posPart {d : ℕ} (w : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if 0 ≤ w i then w i else 0

end SQMeanEstimation


