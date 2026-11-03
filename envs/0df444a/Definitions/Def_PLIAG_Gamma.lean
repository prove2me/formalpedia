-- Prove2me | Definitions.Def_PLIAG_Gamma
-- name    : PLIAG_Gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:29:22.377981+00:00
-- url     : https://prove2.me/theorems/178b1a9a-4435-4a31-885e-84fcf6786e5b
-- title:
--   Lyapunov function $\Gamma_\alpha$ of (4.6)
-- statement:
--   For a step size $\alpha>0$, the **Lyapunov function** of Theorem 4.2 is
--
--   $$
--   \Gamma_\alpha(x):=\Phi(x)-\Phi^*+\frac1\alpha\inf_{z\in\mathcal X}D_w(z,x). \tag{4.6}
--   $$
--
--   It combines the optimality gap and the Bregman distance to the optimal solution set; Theorem 4.2 shows it decays geometrically along the PLIAG iterates.
--
--   **Formalization Note** In `EReal`; $D_w(z,x)=+\infty$ for $z\notin\operatorname{dom}w$, so the infimum over $\mathcal X$ is the paper's. $\Gamma_\alpha(x_0)$ may be $+\infty$ (when $x_0\notin\operatorname{dom}h$), in which case the bounds of Theorem 4.2 hold trivially.
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, (4.6), Theorem 4.2, p.12

import Mathlib
import Definitions.Def_PLIAG_bregman
import Definitions.Def_PLIAG_Phi
import Definitions.Def_PLIAG_PhiStar
import Definitions.Def_PLIAG_optSet

namespace PLIAG

/-- **The Lyapunov function `Γ_α`** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, (4.6), p.12):
`Γ_α(x) := Φ(x) − Φ* + (1/α) inf_{z ∈ X} D_w(z, x)`.

**Formalization Note.** In `EReal`; `D_w(z, x) = +∞` for `z ∉ dom w`, so the infimum over `X` is
the paper's. `Γ_α(x_0)` may be `+∞` (when `x_0 ∉ dom h`); the bounds of Theorem 4.2 are then
trivially true, as on the page. -/
noncomputable def Gamma {d N : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal)
    (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal) (h : EuclideanSpace ℝ (Fin d) → EReal)
    (α : ℝ) (y : EuclideanSpace ℝ (Fin d)) : EReal :=
  Phi f h y - PhiStar w f h + ((1 / α : ℝ) : EReal) * ⨅ z ∈ optSet w f h, bregman w z y

end PLIAG


