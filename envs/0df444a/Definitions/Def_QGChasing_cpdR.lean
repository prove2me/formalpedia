-- Prove2me | Definitions.Def_QGChasing_cpdR
-- name    : QGChasing_cpdR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:56.631269+00:00
-- url     : https://prove2.me/theorems/54abd034-a959-4d14-953f-c60d54e1b690
-- title:
--   CPD parameter $r=\frac{1}{2\kappa^{1/3}}$, Eq. (3)
-- statement:
--   For $\kappa>0$, the step-size parameter of Clipped Proximal Descent is
--   $$
--   r=\frac{1}{2\kappa^{1/3}} .
--   $$
--   For $\kappa\ge1$ it satisfies $0<r\le\frac12$ and $\kappa r^3=\frac18$.
--
--   **Formalization Note** $\kappa^{1/3}$ is the real power `κ ^ (1/3 : ℝ)`.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Eq. (3), p.6

import Mathlib

namespace QGChasing

/-- The CPD parameter `r = 1/(2κ^{1/3})` (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), Eq. (3), p.6).

**Formalization Note** `κ^{1/3}` is `Real.rpow κ (1/3)`; every theorem assumes `κ ≥ 1`, where it
is the real cube root. -/
noncomputable def cpdR (κ : ℝ) : ℝ := 1 / (2 * κ ^ (1 / 3 : ℝ))

end QGChasing


