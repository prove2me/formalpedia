-- Prove2me | Definitions.Def_SlowConvergence_Newton_Data
-- name    : SlowConvergence_Newton_Data
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:35.798844+00:00
-- url     : https://prove2.me/theorems/00045207-0665-4de8-8e7b-d4d0b8c5995c
-- title:
--   The data (3.2)–(3.5) of the slow Newton example: iterates $x_k$, values $f_k$, gradients $g_k$, Hessians $H_k$, steps $s_k$ and the model $m_k$
-- statement:
--   Fix $\tau \in (0,1)$ and put
--   $$\eta = \eta(\tau) = \frac{\tau}{4-2\tau}, \qquad \mu_k = \Big(\frac{1}{k+1}\Big)^{\frac12+\eta}, \qquad b_k = \Big(\frac{1}{k+1}\Big)^{2} \qquad (k \ge 0).$$
--   Write $\zeta(t) = \sum_{n\ge1} n^{-t}$ for the Riemann zeta function at a real argument $t > 1$.
--
--   The example of Cartis, Gould and Toint prescribes, in the Euclidean plane $\mathbb R^2$, the following data for every $k \ge 0$:
--
--   1. the iterates $x_0 = (0,0)^T$ and $x_{k+1} = x_k + (\mu_k, 1)^T$, as in (3.2);
--   2. the function values $f_0 = \tfrac12\big[\zeta(1+2\eta) + \zeta(2)\big]$ and $f_{k+1} = f_k - \tfrac12\big[(1/(k+1))^{1+2\eta} + (1/(k+1))^2\big]$, as in (3.3);
--   3. the gradients $g_k = -(\mu_k, b_k)^T$ and the Hessians $H_k = \mathrm{diag}(1, b_k)$, as in (3.4);
--   4. the steps $s_k = x_{k+1} - x_k$, as in (3.5);
--   5. Newton's quadratic model (1.2) built from these data,
--   $$m_k(x_k + s) = f_k + g_k^T s + \tfrac12\, s^T H_k s .$$
--
--   These are the target values that the function $f_2$ of the example must reproduce at the iterates, $f_k = f_2(x_k)$, $g_k = \nabla f_2(x_k)$, $H_k = \nabla^2 f_2(x_k)$ (3.1); every milestone of the mission is stated about them.
--
--   **Formalization Note** The plane is `EuclideanSpace ℝ (Fin 2)`; $[x]_1, [x]_2$ are the coordinates `x 0`, `x 1`. $H_k$ is the linear operator of the diagonal matrix. $\zeta$ is the real series $\sum_{n \ge 0} (1/(n+1))^t$ (a `tsum`, which Lean would set to $0$ for a divergent series; it is only used at $t = 1+2\eta > 1$ and $t = 2$). The model is written as a function of the trial point $y = x_k + s$.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 1, (1.2); p. 3, (2.10); p. 6, §3, (3.2)–(3.5)

import Mathlib

open scoped RealInnerProductSpace

namespace SlowConvergence.Newton

/-- The exponent shift `η(τ) = τ / (4 − 2τ)` of (2.10), p. 3 (Cartis, Gould & Toint, *On the complexity of
steepest descent, Newton's and regularized Newton's methods*, preprint 15 Oct 2009), reused in §3, p. 6.
For `0 < τ < 1` it satisfies `η > 0` and `1/2 + η = 1/(2 − τ)`. -/
noncomputable def eta (τ : ℝ) : ℝ := τ / (4 - 2 * τ)

/-- The first component `µ_k = (1/(k+1))^{1/2+η}` of the Newton step `s_k` (3.5), p. 6. -/
noncomputable def mu (τ : ℝ) (k : ℕ) : ℝ := (1 / ((k : ℝ) + 1)) ^ (1 / 2 + eta τ)

/-- The second-coordinate curvature `b_k = (1/(k+1))²` appearing in (3.3) and (3.4), p. 6. -/
noncomputable def bk (k : ℕ) : ℝ := (1 / ((k : ℝ) + 1)) ^ 2

/-- The Riemann zeta function on the reals, `ζ(t) = ∑_{n ≥ 1} n^{-t}` (p. 4 and p. 6), written as
`∑_{n ≥ 0} (1/(n+1))^t`. It is finite for `t > 1`, the only arguments used (`t = 1 + 2η` and `t = 2`).
(As a Lean `tsum` it would be `0` for a non-summable series, which never occurs for those arguments.) -/
noncomputable def zetaR (t : ℝ) : ℝ := ∑' n : ℕ, (1 / ((n : ℝ) + 1)) ^ t

/-- The iterates (3.2), p. 6: `x_0 = (0, 0)ᵀ` and `x_{k+1} = x_k + ((1/(k+1))^{1/2+η}, 1)ᵀ`. -/
noncomputable def xk (τ : ℝ) : ℕ → EuclideanSpace ℝ (Fin 2)
  | 0 => !₂[0, 0]
  | k + 1 => xk τ k + !₂[mu τ k, 1]

/-- The prescribed function values (3.3), p. 6: `f_0 = ½[ζ(1 + 2η) + ζ(2)]` and
`f_{k+1} = f_k − ½[(1/(k+1))^{1+2η} + (1/(k+1))²]`. -/
noncomputable def fk (τ : ℝ) : ℕ → ℝ
  | 0 => 1 / 2 * (zetaR (1 + 2 * eta τ) + zetaR 2)
  | k + 1 => fk τ k - 1 / 2 * ((1 / ((k : ℝ) + 1)) ^ (1 + 2 * eta τ) + (1 / ((k : ℝ) + 1)) ^ 2)

/-- The prescribed gradients (3.4), p. 6: `g_k = −((1/(k+1))^{1/2+η}, (1/(k+1))²)ᵀ`. -/
noncomputable def gk (τ : ℝ) (k : ℕ) : EuclideanSpace ℝ (Fin 2) := -!₂[mu τ k, bk k]

/-- The prescribed Hessians (3.4), p. 6: `H_k = diag(1, (1/(k+1))²)`, as a linear operator on the
Euclidean plane. -/
noncomputable def Hk (k : ℕ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Matrix.diagonal ![1, bk k]))

/-- The step (3.5), p. 6: `s_k = x_{k+1} − x_k`. -/
noncomputable def sk (τ : ℝ) (k : ℕ) : EuclideanSpace ℝ (Fin 2) := xk τ (k + 1) - xk τ k

/-- Newton's quadratic model (1.2), p. 1, built from the prescribed data:
`m_k(x_k + s) = f_k + g_kᵀ s + ½ sᵀ H_k s`, evaluated at the point `y = x_k + s`. -/
noncomputable def model (τ : ℝ) (k : ℕ) (y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  fk τ k + ⟪gk τ k, y - xk τ k⟫ + 1 / 2 * ⟪Hk k (y - xk τ k), y - xk τ k⟫

end SlowConvergence.Newton


