-- Prove2me | Definitions.Def_SlowConvergence_ARC_Data
-- name    : SlowConvergence_ARC_Data
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:51.296986+00:00
-- url     : https://prove2.me/theorems/f4c7670a-547a-461c-8700-7007b4bc6aa3
-- title:
--   The data (5.2)–(5.4) of the slow ARC example: iterates $x_k$, values $f_{4,k}$, gradients $g_k$, $H_k = 0$, $\sigma_k = 1$
-- statement:
--   Fix $\tau\in(0,1)$ and put
--   $$\eta = \eta(\tau) = \frac12\Big(\frac{2}{3-2\tau} - \frac23\Big), \qquad s_k = \Big(\frac1{k+1}\Big)^{\frac13+\eta}\quad(k\ge0).$$
--   Write $\zeta(t) = \sum_{n\ge1} n^{-t}$ for the Riemann zeta function at a real argument $t>1$.
--
--   The example of §5 prescribes, for every $k\ge0$:
--
--   1. the iterates (5.2): $x_0 = 0$ and $x_{k+1} = x_k + s_k$;
--   2. the function values (5.3): $f_{4,0} = \tfrac23\zeta(1+3\eta)$ and $f_{4,k+1} = f_{4,k} - \tfrac23\big(\tfrac1{k+1}\big)^{1+3\eta}$;
--   3. the gradients, Hessians and weights (5.4): $g_k = -\big(\tfrac1{k+1}\big)^{\frac23+2\eta}$, $H_k = 0$, $\sigma_k = 1$;
--   4. the cubic model (1.3) built from these data,
--   $$m_k(x_k+s) = f_{4,k} + g_k s + \tfrac12 H_k s^2 + \tfrac13\sigma_k|s|^3 .$$
--
--   These are the values that the function $f_4$ of the example must take at the iterates, $f_4(x_k) = f_{4,k}$, $f_4'(x_k) = g_k$, $f_4''(x_k) = H_k$ (condition (3.1)); the milestones are stated about them.
--
--   **Formalization Note** $\zeta$ is the series $\sum_{n\ge0}(1/(n+1))^t$ as a `tsum`, which Lean sets to $0$ for a divergent series; it is only used at $t = 1+3\eta > 1$. The step is written $s_k$ and $x_{k+1}-x_k = s_k$ by definition; $\eta$ is defined by its first printed expression, and its simplified form $2\tau/(9-6\tau)$ is a milestone.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 2, (1.3); p. 13, §5, (5.2)–(5.4) and η(τ)

import Mathlib

namespace SlowConvergence.ARC

/-- The exponent shift of §5, p. 13 (Cartis, Gould & Toint, preprint 15 Oct 2009):
`η = η(τ) = ½ (2/(3 − 2τ) − 2/3)`, which the page simplifies to `2τ/(9 − 6τ)`. -/
noncomputable def eta (τ : ℝ) : ℝ := 1 / 2 * (2 / (3 - 2 * τ) - 2 / 3)

/-- The step `s_k = (1/(k+1))^{1/3+η}` of (5.2), p. 13. -/
noncomputable def sk (τ : ℝ) (k : ℕ) : ℝ := (1 / ((k : ℝ) + 1)) ^ (1 / 3 + eta τ)

/-- The iterates (5.2), p. 13: `x_0 = 0`, `x_{k+1} = x_k + (1/(k+1))^{1/3+η}`. -/
noncomputable def xk (τ : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => xk τ k + sk τ k

/-- The Riemann zeta function on the reals, `ζ(t) = ∑_{n ≥ 1} n^{-t}`, written as
`∑_{n ≥ 0} (1/(n+1))^t`. It is used only at `t = 1 + 3η > 1`, where the series converges
(a Lean `tsum` of a non-summable series would be `0`). -/
noncomputable def zetaR (t : ℝ) : ℝ := ∑' n : ℕ, (1 / ((n : ℝ) + 1)) ^ t

/-- The prescribed function values (5.3), p. 13: `f_{4,0} = ⅔ ζ(1 + 3η)` and
`f_{4,k+1} = f_{4,k} − ⅔ (1/(k+1))^{1+3η}`. -/
noncomputable def fk (τ : ℝ) : ℕ → ℝ
  | 0 => 2 / 3 * zetaR (1 + 3 * eta τ)
  | k + 1 => fk τ k - 2 / 3 * (1 / ((k : ℝ) + 1)) ^ (1 + 3 * eta τ)

/-- The prescribed gradients (5.4), p. 13: `g_k = −(1/(k+1))^{2/3+2η}`. -/
noncomputable def gk (τ : ℝ) (k : ℕ) : ℝ := -(1 / ((k : ℝ) + 1)) ^ (2 / 3 + 2 * eta τ)

/-- The prescribed Hessians (5.4), p. 13: `H_k = 0`. -/
def Hk (_k : ℕ) : ℝ := 0

/-- The regularization weights (5.4), p. 13: `σ_k = 1`. -/
def sigk (_k : ℕ) : ℝ := 1

/-- The cubic model (1.3), p. 2, built from the prescribed data (with `f(x_k) = f_{4,k}`,
`∇f(x_k) = g_k`, `∇²f(x_k) = H_k` as required by (3.1)), as a function of the step `s`:
`m_k(x_k + s) = f_{4,k} + g_k s + ½ H_k s² + ⅓ σ_k |s|³`. -/
noncomputable def dataModel (τ : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  fk τ k + gk τ k * s + 1 / 2 * Hk k * s ^ 2 + sigk k / 3 * |s| ^ 3

end SlowConvergence.ARC


