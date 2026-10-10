-- Prove2me | Definitions.Def_RandomListsMatching_GeneralRates_Setting
-- name    : RandomListsMatching_GeneralRates_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:07:53.083991+00:00
-- url     : https://prove2.me/theorems/52c7b3ef-9bd3-4fd0-8083-5f1773c59d80
-- title:
--   §5.4, pp. 14–15 — the functions h, g of Claim 2, the per-advertiser bracket, and R(f, β, s)
-- statement:
--   These are the closed-form functions in which Jaillet and Lu carry out the analytic half of the proof of their $0.706$ ratio for online stochastic matching with general arrival rates.
--
--   **The functions $h$ and $g$ (Claim 2).** For real $y, x$,
--   $$
--   h(y,x)=\begin{cases}\dfrac{y}{y-x}\,\bigl(e^{-x}-e^{-y}\bigr), & x\neq y,\\[4pt] y\,e^{-y}, & x=y,\end{cases}\qquad g(y,x)=h(y,0)-h(y,x).
--   $$
--   In the paper $y = f_{a_1}$ is the LP flow into an advertiser $a_1$ and $x = m_{a_1,a}$ is the expected number of random lists $\langle a_1, a\rangle$; $g(f_{a_1}, m_{a_1,a})$ is the probability that $a$ is matched through a list headed by $a_1$.
--
--   **The per-advertiser bracket.** Fix an advertiser with flow $f = f_a$, and index its neighbours $a_1 \in A^*_a$ (including the dummy advertiser $a_d$) by $j = 1, \dots, k$, with $x_j = m_{a,a_1} = m_{a_1,a}$ and $y_j = f_{a_1}$. The numerator of the ratio inside $\min_{a \in A}$ in the chain of p. 15 is
--   $$
--   B(f; x, y) = 1 - e^{-f} + \frac1e \sum_{j} g(f, x_j) - \frac1{2e}\Bigl(\sum_j g(y_j, x_j)\Bigr)^2 + \frac1{2e}\sum_j g(f, x_j)^2 .
--   $$
--
--   **The reduced function $R$.** For reals $f, \beta, s$,
--   $$
--   R(f,\beta,s) = \frac1f\Bigl(1 - e^{-f} + \frac1e\,\frac{s}{\beta}\,g(f,\beta) - \frac1{2e}\bigl(e^{-1}(s-\beta) + g(1,\beta)\bigr)^2 + \frac1{2e}\,g(f,\beta)^2\Bigr).
--   $$
--   In the paper $\beta = \beta_a = \max_j x_j$ and $s = s_a = \sum_j x_j$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $h$ keeps the paper's case split at $x = y$; the bare quotient would be $0$ there in Lean, not $y e^{-y}$. $R$ takes its arguments in the order $(f, \beta, s)$ of its defining display on p. 15 (the proof of Claim 4 writes $R(f_a, s_a, \beta_a)$, a slip). The divisions $1/f$, $s/\beta$ are Lean's total division (value $0$ at a zero denominator); every theorem that uses them assumes the denominator positive. The neighbours are a family indexed by `Fin k`.
-- source:
--   Jaillet & Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (rev. June 2013), p. 14, Claim 2 (h, g); p. 15, third line of the chain (the bracket inside min_{a∈A}) and last display (definition of R(f_a, β_a, s_a))

import Mathlib

namespace RandomListsMatching.GeneralRates

/-- The function `h(y, x)` of Claim 2 (Jaillet & Lu, *Online Stochastic Matching: New Algorithms
with Better Bounds*, accepted manuscript (rev. June 2013), §5.4, p. 14):
`h(y, x) = y / (y - x) * (e^{-x} - e^{-y})` if `x ≠ y`, and `h(y, x) = y e^{-y}` if `x = y`.
The case split is the printed one; it makes `h y` continuous at `x = y`. -/
noncomputable def h (y x : ℝ) : ℝ :=
  if x = y then y * Real.exp (-y) else y / (y - x) * (Real.exp (-x) - Real.exp (-y))

/-- The function `g(y, x) = h(y, 0) - h(y, x)` of Claim 2 (§5.4, p. 14). -/
noncomputable def g (y x : ℝ) : ℝ := h y 0 - h y x

/-- The function `R(f, β, s)` defined in §5.4, p. 15, last display:
`R(f, β, s) = (1/f) (1 - e^{-f} + (1/e)(s/β) g(f, β) - (1/2e)(e^{-1}(s - β) + g(1, β))² + (1/2e) g(f, β)²)`.
The argument order is `(f, β, s)`, as in the defining display. -/
noncomputable def R (f β s : ℝ) : ℝ :=
  (1 / f) * (1 - Real.exp (-f) + (1 / Real.exp 1) * (s / β) * g f β
    - (1 / (2 * Real.exp 1)) * (Real.exp (-1) * (s - β) + g 1 β) ^ 2
    + (1 / (2 * Real.exp 1)) * (g f β) ^ 2)

/-- The numerator of the per-advertiser ratio inside `min_{a ∈ A}` (§5.4, p. 15, third line of the
chain): for an advertiser with `f_a = f` whose neighbours (including the dummy `a_d`) are indexed by
`Fin k`, with `x j = m_{a,a1} = m_{a1,a}` and `y j = f_{a1}`,
`1 - e^{-f} + (1/e) Σ_j g(f, x_j) - (1/2e) (Σ_j g(y_j, x_j))² + (1/2e) Σ_j g(f, x_j)²`. -/
noncomputable def bracket (f : ℝ) {k : ℕ} (x y : Fin k → ℝ) : ℝ :=
  1 - Real.exp (-f) + (1 / Real.exp 1) * ∑ j, g f (x j)
    - (1 / (2 * Real.exp 1)) * (∑ j, g (y j) (x j)) ^ 2
    + (1 / (2 * Real.exp 1)) * ∑ j, (g f (x j)) ^ 2

end RandomListsMatching.GeneralRates


