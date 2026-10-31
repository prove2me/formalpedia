-- Prove2me | Definitions.Def_SQMeanEstimation_highPart
-- name    : SQMeanEstimation_highPart
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:03.812994+00:00
-- url     : https://prove2.me/theorems/dcf0412c-8c49-4e17-95f8-fb51b8526bc8
-- title:
--   Large coordinates $u^>_i=u_i\mathbf 1_{\{u_i\ge1/n\}}$
-- statement:
--   For $n>0$ and $u\in\mathbb R^d$, the vector of **large coordinates** is
--   $$
--   u^>_i=u_i\cdot\mathbf 1_{\{u_i\ge1/n\}}.
--   $$
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, Lemma 3.16, p.17

import Mathlib

namespace SQMeanEstimation

/-- **The large coordinates `u^>`.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, Lemma 3.16, p.17: "u^>_i = uᵢ · 1_{uᵢ≥1/n}".

`highPart n u` keeps the coordinates with `uᵢ ≥ 1/n` and sets the others to `0`. -/
noncomputable def highPart {d : ℕ} (n : ℝ) (u : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if 1 / n ≤ u i then u i else 0

end SQMeanEstimation


