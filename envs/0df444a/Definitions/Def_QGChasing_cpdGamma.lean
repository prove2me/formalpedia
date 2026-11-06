-- Prove2me | Definitions.Def_QGChasing_cpdGamma
-- name    : QGChasing_cpdGamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:32.446987+00:00
-- url     : https://prove2.me/theorems/bab1aa08-630e-4dee-861f-c0586451237c
-- title:
--   Cap $\gamma_t=\frac{r^2 s_t}{s_t+\beta\mu_t}$ (Algorithm 1, line 7)
-- statement:
--   For $\kappa>0$, a proximal step length $s=s_t$ and a balancing parameter $\mu=\mu_t$, the cap on the clipped step of Algorithm 1 is
--   $$
--   \gamma_t=\frac{r^2 s_t}{s_t+\beta\mu_t},
--   $$
--   with $r$ and $\beta$ from (3).
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Algorithm 1, line 7, p.5; p.6

import Mathlib
import Definitions.Def_QGChasing_cpdR
import Definitions.Def_QGChasing_cpdBeta

namespace QGChasing

/-- The cap `γ_t = r² s_t/(s_t + βμ_t)` of Algorithm 1, line 7 (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.5; also p.6), as a
function of `κ`, the proximal step length `s = s_t` and the balancing parameter `μ = μ_t`. -/
noncomputable def cpdGamma (κ s μ : ℝ) : ℝ := cpdR κ ^ 2 * s / (s + cpdBeta κ * μ)

end QGChasing


