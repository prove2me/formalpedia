-- Prove2me | Definitions.Def_SQMeanEstimation_zeroSmall
-- name    : SQMeanEstimation_zeroSmall
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:59.182931+00:00
-- url     : https://prove2.me/theorems/617b8078-5308-40d9-8c3a-8315b39a55aa
-- title:
--   Zeroing of small answers $v_i=v'_i\mathbf 1_{\{|v'_i|\ge2/n\}}$
-- statement:
--   For $n>0$ and $v'\in\mathbb R^d$, let
--   $$
--   v_i=v'_i\cdot\mathbf 1_{\{|v'_i|\ge 2/n\}},
--   $$
--   i.e. answers of absolute value below $2/n$ are replaced by $0$. In the proof of Theorem 3.15 this zeroing keeps the coordinates whose true mean is close to $0$ from accumulating error.
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, proof of Theorem 3.15, p.17

import Mathlib

namespace SQMeanEstimation

/-- **Zeroing of small oracle answers.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, proof of Theorem 3.15, p.17: "let
vᵢ = v′ᵢ · 1_{|v′ᵢ|≥2/n}".

`zeroSmall n v'` keeps the coordinates with `|v′ᵢ| ≥ 2/n` and sets the others to `0`. -/
noncomputable def zeroSmall {d : ℕ} (n : ℝ) (v' : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if 2 / n ≤ |v' i| then v' i else 0

end SQMeanEstimation


