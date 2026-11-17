-- Prove2me | Definitions.Def_QGChasing_Supplement_robdB
-- name    : QGChasing_Supplement_robdB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:25:37.710024+00:00
-- url     : https://prove2.me/theorems/a091a381-83f1-47d8-a912-582fcf261977
-- title:
--   R-OBD weight $b=\frac{a^2}{q(1+\delta)}$, Eq. (5)
-- statement:
--   For $q>0$ and $0\le\delta<1$, the weight on the pull toward the minimizer $v_t$ in R-OBD is
--   $$
--   b=\frac{a^2}{q(1+\delta)},
--   $$
--   with $a$ the other weight of (5).
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Eq. (5), Lemma 5.1, p.9

import Mathlib
import Definitions.Def_QGChasing_Supplement_robdA

namespace QGChasing.Supplement

/-- The R-OBD weight `b = a²/(q(1 + δ))`, Eq. (5) (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), Lemma 5.1, p.9).

**Formalization Note** Used only for `q > 0`, `0 ≤ δ < 1`, where `q(1 + δ) > 0`. -/
noncomputable def robdB (q δ : ℝ) : ℝ := robdA q δ ^ 2 / (q * (1 + δ))

end QGChasing.Supplement


