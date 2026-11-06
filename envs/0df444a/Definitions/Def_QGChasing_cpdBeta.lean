-- Prove2me | Definitions.Def_QGChasing_cpdBeta
-- name    : QGChasing_cpdBeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:39.711287+00:00
-- url     : https://prove2.me/theorems/bf848b47-eb53-4d6d-a553-893451bef26f
-- title:
--   CPD balance parameter $\beta=1+3r$, Eq. (3)
-- statement:
--   The balance parameter of Clipped Proximal Descent is $\beta=1+3r$ with $r=\frac1{2\kappa^{1/3}}$. Algorithm 1 compares the shifted hitting cost with $\beta$ times the movement: in line 4, $g_t(v^X_t)\ge\beta\|v^X_t-x_{t-1}\|$, and in line 7 the balance equation $g_t(y_t)=\beta\|y_t-x_{t-1}\|$.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Eq. (3), p.6

import Mathlib
import Definitions.Def_QGChasing_cpdR

namespace QGChasing

/-- The CPD balance parameter `β = 1 + 3r` (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), Eq. (3), p.6). -/
noncomputable def cpdBeta (κ : ℝ) : ℝ := 1 + 3 * cpdR κ

end QGChasing


