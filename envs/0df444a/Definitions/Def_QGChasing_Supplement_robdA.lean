-- Prove2me | Definitions.Def_QGChasing_Supplement_robdA
-- name    : QGChasing_Supplement_robdA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:24:58.906137+00:00
-- url     : https://prove2.me/theorems/63d474fe-d657-42f5-a28e-b1bf39c6863c
-- title:
--   R-OBD weight $a=\frac{1+q\delta^2}{1-\delta}$, Eq. (5)
-- statement:
--   For $q>0$ and $0\le\delta<1$, with $h=1+q\delta^2$, the weight on the movement term in R-OBD is
--   $$
--   a=\frac{h}{1-\delta}=\frac{1+q\delta^2}{1-\delta}.
--   $$
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Eq. (5), Lemma 5.1, p.9

import Mathlib

namespace QGChasing.Supplement

/-- The R-OBD weight `a = h/(1 − δ)` with `h = 1 + qδ²`, Eq. (5) (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), Lemma 5.1, p.9).

**Formalization Note** Used only for `0 ≤ δ < 1`, where `1 − δ > 0`. -/
noncomputable def robdA (q δ : ℝ) : ℝ := (1 + q * δ ^ 2) / (1 - δ)

end QGChasing.Supplement


