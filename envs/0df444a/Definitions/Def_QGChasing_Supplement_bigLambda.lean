-- Prove2me | Definitions.Def_QGChasing_Supplement_bigLambda
-- name    : QGChasing_Supplement_bigLambda
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:24:04.572106+00:00
-- url     : https://prove2.me/theorems/e11dc207-61c8-458b-b420-4d9d5b3d9e7a
-- title:
--   The function $\Lambda(q,\delta)$ of Eq. (2)
-- statement:
--   For $q>0$ and $0\le\delta<1$ let
--   $$
--   \Lambda(q,\delta)=\frac{(1+q\delta^2)^2}{q(1-\delta^2)(q+\delta)} .
--   $$
--   On this domain the denominator is positive and $\Lambda(q,\delta)>0$. Minimizing $\Lambda(q,\cdot)$ over $[0,1)$ gives the function $\phi$ whose inverse determines the optimal competitive ratio $1+q^*(\lambda)$ for squared Euclidean movement; the condition $\lambda\ge\Lambda(q,\delta)$ is exactly what makes R-OBD with parameters $(q,\delta)$ $(1+q)$-competitive.
--
--   **Formalization Note** Outside $q>0$, $0\le\delta<1$ the Lean value is real division with Lean's conventions; no statement of the mission uses it there.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Eq. (2), p.2

import Mathlib

namespace QGChasing.Supplement

/-- The function `Λ(q, δ) = (1 + qδ²)² / (q(1 − δ²)(q + δ))` of Eq. (2) (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.2).

**Formalization Note** The source uses `Λ` only for `q > 0` and `0 ≤ δ < 1`, where the denominator
is positive. Outside that range the value is Lean's real division and is never used by the
statements of this mission. -/
noncomputable def bigLambda (q δ : ℝ) : ℝ :=
  (1 + q * δ ^ 2) ^ 2 / (q * (1 - δ ^ 2) * (q + δ))

end QGChasing.Supplement


