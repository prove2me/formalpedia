-- Prove2me | Definitions.Def_SQMeanEstimation_lowPart
-- name    : SQMeanEstimation_lowPart
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:00.233375+00:00
-- url     : https://prove2.me/theorems/e4f0ad33-1d93-42f4-aa4a-944f4f20764a
-- title:
--   Small coordinates $u^<_i=u_i\mathbf 1_{\{u_i<4/n\}}$
-- statement:
--   For $n>0$ and $u\in\mathbb R^d$, the vector of **small coordinates** is
--   $$
--   u^<_i=u_i\cdot\mathbf 1_{\{u_i<4/n\}}
--   $$
--   (strict inequality).
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, Lemma 3.16, p.17

import Mathlib

namespace SQMeanEstimation

/-- **The small coordinates `u^<`.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, Lemma 3.16, p.17: "u^<_i = uᵢ · 1_{uᵢ<4/n}".

`lowPart n u` keeps the coordinates with `uᵢ < 4/n` (strict) and sets the others to `0`. -/
noncomputable def lowPart {d : ℕ} (n : ℝ) (u : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if u i < 4 / n then u i else 0

end SQMeanEstimation


