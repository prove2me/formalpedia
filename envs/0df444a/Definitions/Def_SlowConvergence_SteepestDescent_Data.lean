-- Prove2me | Definitions.Def_SlowConvergence_SteepestDescent_Data
-- name    : SlowConvergence_SteepestDescent_Data
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:45.132819+00:00
-- url     : https://prove2.me/theorems/128d866b-11e5-419a-a195-36ff35d3a695
-- title:
--   The data (2.5)–(2.10) of the slow steepest-descent example: iterates $x_k$, steps $s_k$, values $f_k$, gradients $g_k$, Hessians $H_k$
-- statement:
--   Fix $\tau \in (0,1)$ and a sequence of step lengths $(\alpha_k)_{k \ge 0}$. Put
--   $$\eta = \eta(\tau) = \frac{1}{2-\tau} - \frac12 = \frac{\tau}{4-2\tau},$$
--   and write $\zeta(t) = \sum_{n\ge1} n^{-t}$ for the Riemann zeta function at a real argument $t > 1$.
--
--   The one-dimensional example of Cartis, Gould and Toint prescribes, for every $k \ge 0$:
--
--   1. the iterates $x_0 = 0$ and $x_{k+1} = x_k + \alpha_k \big(\tfrac{1}{k+1}\big)^{\frac12+\eta}$, as in (2.5);
--   2. the steps $s_k = x_{k+1} - x_k = \alpha_k \big(\tfrac{1}{k+1}\big)^{\frac12+\eta}$, as in (2.7);
--   3. the function values $f_0 = \tfrac12\,\zeta(1+2\eta)$ and $f_{k+1} = f_k - \alpha_k\big(1-\tfrac12\alpha_k\big)\big(\tfrac{1}{k+1}\big)^{1+2\eta}$, as in (2.8);
--   4. the gradients $g_k = -\big(\tfrac{1}{k+1}\big)^{\frac12+\eta}$ and the Hessians $H_k = 1$, as in (2.9).
--
--   These are the values that the objective $f_1$ of the example must take at the iterates, $f_k = f_1(x_k)$ and $g_k = f_1'(x_k)$ (2.4). Since $x_{k+1} = x_k - \alpha_k g_k$, the iterates are those of the steepest descent method with step lengths $\alpha_k$. Every milestone of the mission is stated about these data.
--
--   **Formalization Note** $\zeta$ is the real series $\sum_{n \ge 0} (1/(n+1))^t$ (a `tsum`, which Lean would set to $0$ for a divergent series; it is only used at $t = 1 + 2\eta > 1$). The sequences are defined for an arbitrary real sequence $\alpha$; the milestones add the paper's condition (2.6) on it.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 3, §2, (2.5)–(2.10); p. 4, definition of ζ

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data

namespace SlowConvergence.SteepestDescent

/-- The iterates (2.5), p. 3: `x_0 = 0` and `x_{k+1} = x_k + α_k (1/(k+1))^{1/2+η}`, for a step-length
sequence `α = (α_k)_{k ≥ 0}`. -/
noncomputable def xk (τ : ℝ) (α : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => xk τ α k + α k * (1 / ((k : ℝ) + 1)) ^ (1 / 2 + SlowConvergence.Newton.eta τ)

/-- The step (2.7), p. 3: `s_k = x_{k+1} − x_k`. -/
noncomputable def sk (τ : ℝ) (α : ℕ → ℝ) (k : ℕ) : ℝ := xk τ α (k + 1) - xk τ α k

/-- The prescribed function values (2.8), p. 3: `f_0 = ½ ζ(1 + 2η)` and
`f_{k+1} = f_k − α_k (1 − ½ α_k) (1/(k+1))^{1+2η}`. -/
noncomputable def fk (τ : ℝ) (α : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1 / 2 * SlowConvergence.Newton.zetaR (1 + 2 * SlowConvergence.Newton.eta τ)
  | k + 1 => fk τ α k - α k * (1 - 1 / 2 * α k) * (1 / ((k : ℝ) + 1)) ^ (1 + 2 * SlowConvergence.Newton.eta τ)

/-- The prescribed gradients (2.9), p. 3: `g_k = −(1/(k+1))^{1/2+η}`. -/
noncomputable def gk (τ : ℝ) (k : ℕ) : ℝ := -((1 / ((k : ℝ) + 1)) ^ (1 / 2 + SlowConvergence.Newton.eta τ))

/-- The prescribed Hessians (2.9), p. 3: `H_k = 1`. -/
def Hk (_k : ℕ) : ℝ := 1

end SlowConvergence.SteepestDescent


