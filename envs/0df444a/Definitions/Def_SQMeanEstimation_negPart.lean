-- Prove2me | Definitions.Def_SQMeanEstimation_negPart
-- name    : SQMeanEstimation_negPart
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:58.394513+00:00
-- url     : https://prove2.me/theorems/c477f6e0-0b58-45ec-8109-77727baac1c3
-- title:
--   Negative part $w^-$ of a vector
-- statement:
--   For $w\in\mathbb R^d$, the **negative part** is
--   $$
--   w^-=-\sum_{i=1}^d e_i w_i\mathbf 1_{\{w_i<0\}},
--   $$
--   so coordinate $i$ of $w^-$ is $-w_i$ when $w_i<0$ and $0$ otherwise. Then $w=w^+-w^-$.
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, proof of Theorem 3.15, p.17

import Mathlib

namespace SQMeanEstimation

/-- **Negative part of a vector.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, proof of Theorem 3.15, p.17:
"w⁻ ≐ −Σ_{i=1}^d eᵢwᵢ1_{wᵢ<0}".

`negPart w` has coordinate `−wᵢ` where `wᵢ < 0` and `0` elsewhere, so `w = posPart w − negPart w`
and both parts are nonnegative. -/
noncomputable def negPart {d : ℕ} (w : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if w i < 0 then -w i else 0

end SQMeanEstimation


