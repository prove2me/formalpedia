-- Prove2me | Definitions.Def_WardropTraffic_Signal_Setting
-- name    : WardropTraffic_Signal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:22.640248+00:00
-- url     : https://prove2.me/theorems/e648e78d-2da8-483f-854c-bb0e460a81f8
-- title:
--   pp. 337–339, 358–359 — two-phase signal: average delay (16), T(x, y) = (λx² + μy²)/(x + y − 1), feasible (x, y), ξ, η, λ, μ
-- statement:
--   A fixed-time traffic signal at an intersection alternates two **phases**. For phase $k \in \{1,2\}$ let $q_k$ be the arriving flow, $p_k$ the **saturation flow** (the departure rate of a queue discharging at minimum headway), $a_k$ the **lost time** at the start of green, $g_k$ the green time and $r_k$ the red time, with $r_1 = g_2$ and $r_2 = g_1$. Write $Q = q_1 + q_2$, $A = a_1 + a_2$, and $c = g_1 + g_2$ for the **cycle time**.
--
--   **Average delay (16).** The flow-weighted average delay at the intersection is
--   $$T = \frac{1}{2Qc}\left\{\frac{q_1 (r_1 + a_1)^2}{1 - q_1/p_1} + \frac{q_2 (r_2 + a_2)^2}{1 - q_2/p_2}\right\}.$$
--
--   **Reduced variables (Appendix IV).** Put $\xi = 1 - q_1/p_1$, $\eta = 1 - q_2/p_2$,
--   $$\lambda = \frac{A q_1}{2Q\xi}, \qquad \mu = \frac{A q_2}{2Q\eta}.$$
--   In terms of the effective-red fractions $x = (r_1 + a_1)/c$ and $y = (r_2 + a_2)/c$, the delay becomes
--   $$T(x,y) = \frac{\lambda x^2 + \mu y^2}{x + y - 1}.$$
--   The **feasible region** is the set of $(x,y)$ with $x \le \xi$, $y \le \eta$ (no indefinite accumulation of vehicles on either phase) and $x + y > 1$ (a positive cycle $c = A/(x+y-1)$).
--
--   Two auxiliary quantities appear in the optimality criterion:
--   $$D = \frac{\mu}{\lambda}\eta^2 + 2\xi(1-\eta) - \xi^2, \qquad x_0 = 1 - \eta + \sqrt{(1-\eta)^2 + \frac{\mu}{\lambda}\eta^2}.$$
--
--   These objects are the whole vocabulary of the signal-timing results of Wardrop's paper: (16) is the objective, $(x,y)$ the decision, and $D$, $x_0$ describe the optimum.
--
--   **Formalization Note** All quantities are real numbers. `delayT lam mu x y` is $T(x,y)$, `feasibleXY xi eta` the feasible region, `cornerD` is $D$, `edgeRoot` is $x_0$, `xiOf`, `etaOf`, `lamOf`, `muOf` are $\xi, \eta, \lambda, \mu$ as functions of the original data, and `avgDelay16` is the right side of (16). The condition $x + y > 1$ is part of the feasible set: the page presupposes a positive cycle, and without it Lean's convention $t/0 = 0$ would put a spurious zero of $T$ on the line $x + y = 1$. The page prints $\eta = 1 - q_1/p_1$; this is a slip for $1 - q_2/p_2$, which is what `etaOf` uses.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 337 (symbols), p. 339 (16), p. 358 (Appendix IV: x, y, ξ, η, λ, μ, T(x, y)), p. 359 (the corner condition and the root)

import Mathlib

namespace WardropTraffic.Signal

/-- Appendix IV, p. 358: the average delay `T = (λx² + μy²)/(x + y − 1)` in terms of the
effective-red fractions `x = (r₁ + a₁)/c`, `y = (r₂ + a₂)/c`. -/
noncomputable def delayT (lam mu x y : ℝ) : ℝ :=
  (lam * x ^ 2 + mu * y ^ 2) / (x + y - 1)

/-- Appendix IV, p. 358: the admissible `(x, y)`: `x ≤ ξ`, `y ≤ η` (no indefinite accumulation on
either phase) and `x + y > 1` (a positive cycle `c = A/(x + y − 1)`). -/
def feasibleXY (xi eta : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ≤ xi ∧ z.2 ≤ eta ∧ 1 < z.1 + z.2}

/-- The left side of the corner condition, p. 359: `(μ/λ)η² + 2ξ(1 − η) − ξ²`. -/
noncomputable def cornerD (lam mu xi eta : ℝ) : ℝ :=
  (mu / lam) * eta ^ 2 + 2 * xi * (1 - eta) - xi ^ 2

/-- The root on the edge `y = η`, p. 359: `1 − η + √((1 − η)² + (μ/λ)η²)`. -/
noncomputable def edgeRoot (lam mu eta : ℝ) : ℝ :=
  1 - eta + Real.sqrt ((1 - eta) ^ 2 + (mu / lam) * eta ^ 2)

/-- `ξ = 1 − q₁/p₁`, p. 358. -/
noncomputable def xiOf (q₁ p₁ : ℝ) : ℝ := 1 - q₁ / p₁

/-- `η = 1 − q₂/p₂` (the page prints `1 − q₁/p₁`, a slip), p. 358. -/
noncomputable def etaOf (q₂ p₂ : ℝ) : ℝ := 1 - q₂ / p₂

/-- `λ = Aq₁/(2Qξ)`, p. 358. -/
noncomputable def lamOf (A Q q₁ p₁ : ℝ) : ℝ := A * q₁ / (2 * Q * xiOf q₁ p₁)

/-- `μ = Aq₂/(2Qη)`, p. 358. -/
noncomputable def muOf (A Q q₂ p₂ : ℝ) : ℝ := A * q₂ / (2 * Q * etaOf q₂ p₂)

/-- Equation (16), p. 339: the average delay for the intersection as a whole,
`T = (1/2Qc){q₁(r₁ + a₁)²/(1 − q₁/p₁) + q₂(r₂ + a₂)²/(1 − q₂/p₂)}`. -/
noncomputable def avgDelay16 (Q c q₁ q₂ p₁ p₂ r₁ r₂ a₁ a₂ : ℝ) : ℝ :=
  1 / (2 * Q * c) * (q₁ * (r₁ + a₁) ^ 2 / (1 - q₁ / p₁) + q₂ * (r₂ + a₂) ^ 2 / (1 - q₂ / p₂))

end WardropTraffic.Signal


