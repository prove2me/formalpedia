-- Prove2me | Definitions.Def_RiskBalancingMNL_lambertW
-- name    : RiskBalancingMNL_lambertW
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:29.92272+00:00
-- url     : https://prove2.me/theorems/2c9bb7df-e27f-47c1-ac1c-dd31c14a4b1d
-- title:
--   Principal Lambert W function $W$ on $[0,\infty)$
-- statement:
--   The **Lambert W function** is the inverse of $w\mapsto we^{w}$. On $[0,\infty)$ this map is a strictly increasing bijection, so for every $x\ge0$ there is exactly one $w\ge0$ with
--   $$
--   W(x)\,e^{W(x)}=x .
--   $$
--   It gives the closed form of the profit-maximizing markup in Theorem 1(i).
--
--   **Formalization Note** Only the positive argument $\sum_ie^{a_i-bc_i-1}$ occurs, so only the principal branch on $[0,\infty)$ is defined; for $x<0$ the definition returns the placeholder $0$. The body mirrors the platform definition `DirectTradeCoffee.lambertW`, which is not yet public.
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), Theorem 1(i), p.12 ("where W is the lambertW function")

import Mathlib

namespace RiskBalancingMNL

/-- **Principal Lambert W function on `[0, ∞)`**, used in Theorem 1(i) of Li & Webster,
*Optimizing Risk-balancing Return under Discrete Choice Models*, SSRN 3959428 (PDF of
2021-11-14), p.12: "`W` is the lambertW function".

For `x ≥ 0`, `lambertW x` is the unique `w ≥ 0` with `w * exp w = x`.

**Formalization Note** Only the argument `Σᵢ e^{aᵢ − bcᵢ − 1} > 0` occurs, so only the principal
branch on `[0, ∞)` is needed. For `x < 0` no such `w` exists and the definition returns the junk
value `0`. The body mirrors the not-yet-public platform definition `DirectTradeCoffee.lambertW`. -/
noncomputable def lambertW (x : ℝ) : ℝ :=
  open Classical in
  if h : ∃ w : ℝ, 0 ≤ w ∧ w * Real.exp w = x then Classical.choose h else 0

end RiskBalancingMNL


