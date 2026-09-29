-- Prove2me | Definitions.Def_NonmonotoneLS_RLinear_Constants
-- name    : NonmonotoneLS_RLinear_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:24:40.914505+00:00
-- url     : https://prove2.me/theorems/53cd4a5c-1d6a-4572-a9f2-cd76c464c410
-- title:
--   The constants $\beta$, $b$, $b_2$ and $\theta$ of the R-linear convergence proof
-- statement:
--   Given the NLSA parameters, direction constants $c_1, c_2$, a Lipschitz constant $L$ and the strong convexity constant $\gamma$, define
--
--   $$\beta = \min\left\{\frac{\delta\mu c_1}{\rho},\ \frac{2\delta(1-\delta)c_1^2}{L\rho c_2^2},\ \frac{\delta(1-\sigma)c_1^2}{L c_2^2}\right\} \quad (2.9), \qquad b = 1 + \mu c_2 L \quad (3.7),$$
--
--   $$b_2 = \frac{1}{\beta + \gamma b^2}, \qquad \theta = 1 - \beta b_2 (1 - \eta_{\max}).$$
--
--   These are the explicit constants in the sufficient-decrease bound (3.6), the gradient growth bound (3.7) and the contraction (3.8).
--
--   **Formalization Note.** Plain real arithmetic. The divisions are by $L c_2^2$, $L\rho c_2^2$, $\rho$ and $\beta + \gamma b^2$; every statement that uses these constants assumes $L, c_1, c_2, \gamma > 0$, under which all denominators are positive.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1047, Eq. (2.9); p. 1050, Eqs. (3.7)–(3.8)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params

namespace NonmonotoneLS.RLinear

/-- The constant `β` of Eq. (2.9) (p. 1047):
`β = min{δμc₁/ρ, 2δ(1-δ)c₁²/(Lρc₂²), δ(1-σ)c₁²/(Lc₂²)}`. -/
noncomputable def beta (p : Shared.Params) (c₁ c₂ L : ℝ) : ℝ :=
  min (min (p.δ * p.μ * c₁ / p.ρ) (2 * p.δ * (1 - p.δ) * c₁ ^ 2 / (L * p.ρ * c₂ ^ 2)))
    (p.δ * (1 - p.σ) * c₁ ^ 2 / (L * c₂ ^ 2))

/-- The constant `b = 1 + μc₂L` of Eq. (3.7) (p. 1050). -/
def bConst (p : Shared.Params) (c₂ L : ℝ) : ℝ :=
  1 + p.μ * c₂ * L

/-- The constant `b₂ = 1/(β + γb²)` of (3.8) (p. 1050). -/
noncomputable def b2Const (p : Shared.Params) (c₁ c₂ L γ : ℝ) : ℝ :=
  1 / (beta p c₁ c₂ L + γ * bConst p c₂ L ^ 2)

/-- The contraction factor `θ = 1 - βb₂(1 - η_max)` of (3.8) (p. 1050). -/
noncomputable def theta (p : Shared.Params) (c₁ c₂ L γ : ℝ) : ℝ :=
  1 - beta p c₁ c₂ L * b2Const p c₁ c₂ L γ * (1 - p.ηmax)

end NonmonotoneLS.RLinear


