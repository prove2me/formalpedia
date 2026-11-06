-- Prove2me | Definitions.Def_QGChasing_cpdEta
-- name    : QGChasing_cpdEta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:22.115807+00:00
-- url     : https://prove2.me/theorems/f264ad1b-f147-49f9-a53e-65de22de2c0a
-- title:
--   Clipped fraction $\eta_t=\min\{\gamma_t, r s_t/\|y_t-v_t\|\}$ (Algorithm 1, line 7)
-- statement:
--   For $\kappa>0$, $s=s_t$, $\mu=\mu_t$ and $\delta=\|y_t-v_t\|$, the fraction of the clipped step toward the minimizer $v_t$ is
--   $$
--   \eta_t=\min\Big\{\gamma_t,\ \frac{r s_t}{\|y_t-v_t\|}\Big\},
--   $$
--   with $\gamma_t$ the cap of line 7 and $r$ from (3). The cap $\eta_t\le\gamma_t$ controls a localization error, and $\eta_t\|y_t-v_t\|\le r s_t$ limits the extra movement to a fraction $r$ of the proximal step.
--
--   **Formalization Note** The formula is as printed. Lean evaluates $rs/0$ to $0$; this case never arises because $y_t\ne v_t$ in a balanced round (Lemma 4.1).
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Algorithm 1, line 7, p.5; p.6

import Mathlib
import Definitions.Def_QGChasing_cpdR
import Definitions.Def_QGChasing_cpdGamma

namespace QGChasing

/-- The clipped step fraction `η_t = min{γ_t, r s_t/‖y_t − v_t‖}` of Algorithm 1, line 7
(He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.5; also p.6), as a function of `κ`, `s = s_t`, `μ = μ_t` and `dist = ‖y_t − v_t‖`.

**Formalization Note** The formula is as printed. In Lean `r s/0 = 0`; this case does not occur,
since `y_t ≠ v_t` in every balanced round (Lemma 4.1). -/
noncomputable def cpdEta (κ s μ dist : ℝ) : ℝ := min (cpdGamma κ s μ) (cpdR κ * s / dist)

end QGChasing


