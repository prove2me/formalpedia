-- Prove2me | Definitions.Def_PeriodicEval_Params
-- name    : PeriodicEval_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:26.159157+00:00
-- url     : https://prove2.me/theorems/dafa879c-e5a1-42f6-b823-48aedd8b9a09
-- title:
--   Model parameters, $\theta$, $h$, $\kappa$, $T_i$ and the standing assumptions
-- statement:
--   The model of the paper has the following parameters: the drift $\mu\in\mathbb R$ and volatility $\sigma$ of the stock, the interest rate $r\in\mathbb R$, the evaluation period $\tau$, the performance target $\gamma$, the utility exponent $\alpha$, the loss coefficient $k$, the discount rate $\beta$, and the initial stock price $S_0$. Derived from them are the Sharpe ratio $\theta:=(\mu-r)/\sigma$, the Merton growth constant
--
--   $$h:=r\alpha+\frac{\alpha\theta^2}{2(1-\alpha)},$$
--
--   the case threshold $\kappa:=(k^{1/(1-\alpha)}+1)^{1-\alpha}$, the point $y_{\max}(a):=\gamma/(1-|a|^{-1/(1-\alpha)})$ (used for $a<-1$), and the evaluation dates $T_i:=i\tau$, $i=0,1,2,\dots$
--
--   The **standing assumptions** are
--
--   1. $\sigma>0$ and $\theta\neq0$;
--   2. $\tau>0$ and $\gamma\ge0$;
--   3. $\alpha\in(0,1)$ and $k\ge0$;
--   4. $\beta>0$ and Assumption 1: $\beta>h$;
--   5. $S_0>0$.
--
--   Every result of the mission is stated under these assumptions.
--
--   **Formalization Note** Evaluation dates are elements of $[0,\infty)$ (`ℝ≥0`), the time index of Mathlib's Brownian motion. The paper never names $S_0$; it is kept as a positive parameter and cancels from every result.
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), §2, pp.6–10: parameters (p.6–8), θ ≠ 0 (p.7), T_i = iτ (p.7), Assumption 1 eq. (5) (p.10); κ and γ/(1−|a|^{−1/(1−α)}) from Lemma 1 4(a)–(b) (p.32) and Theorem 1 (p.14)

import Mathlib

open scoped NNReal

namespace PeriodicEval

/-- The parameters of the periodic-evaluation portfolio problem.
Tse–Zheng, *Portfolio Selection, Periodic Evaluations and Risk Taking*, SSRN 3971852
(June 20, 2023), §2, pp.6–10: drift `μ` and volatility `σ` of the stock, interest rate `r`,
evaluation period `τ` (`T_i = iτ`), performance target `γ`, utility exponent `α` and loss
coefficient `k` of (3), discount rate `β` of (4), and the initial stock price `S₀`.

**Formalization Note** The paper never names the initial stock price; `S₀` is kept as a
parameter (it cancels from every result). -/
structure Params where
  μ : ℝ
  r : ℝ
  σ : ℝ
  τ : ℝ
  γ : ℝ
  α : ℝ
  k : ℝ
  β : ℝ
  S₀ : ℝ

namespace Params

/-- The Sharpe ratio `θ := (μ − r)/σ`, SSRN 3971852 (June 20, 2023), p.6. -/
noncomputable def θ (p : Params) : ℝ := (p.μ - p.r) / p.σ

/-- The Merton growth constant `h := rα + αθ²/(2(1 − α))` of Assumption 1, eq. (5), p.10. -/
noncomputable def h (p : Params) : ℝ := p.r * p.α + p.α * p.θ ^ 2 / (2 * (1 - p.α))

/-- The case threshold `κ := (k^{1/(1−α)} + 1)^{1−α}` of Lemma 1 4(a)–(b), Lemma 2,
Proposition 3 and Theorem 1, pp.13–14, 32–37. -/
noncomputable def κ (p : Params) : ℝ := (p.k ^ (1 / (1 - p.α)) + 1) ^ (1 - p.α)

/-- The point `γ/(1 − |a|^{−1/(1−α)})`, where `G_a` attains its interior maximum for
`a < −1` (Lemma 1, 4(a), p.32), and the upper end of the support in Case 2b of Theorem 1, p.14.
Used only for `a < −1`, where the denominator lies in `(0, 1)`. -/
noncomputable def ymax (p : Params) (a : ℝ) : ℝ := p.γ / (1 - |a| ^ (-1 / (1 - p.α)))

/-- The evaluation dates `T_i := iτ`, `i = 0, 1, 2, …`, SSRN 3971852 (June 20, 2023), p.7.

**Formalization Note** Time is indexed by `ℝ≥0` (as for Mathlib's Brownian motion);
`T_i` is `iτ` cast to `ℝ≥0`, which is exact because `τ > 0` under `Params.Standing`. -/
noncomputable def T (p : Params) (i : ℕ) : ℝ≥0 := Real.toNNReal ((i : ℝ) * p.τ)

/-- The standing assumptions of the paper, SSRN 3971852 (June 20, 2023), §2, pp.6–10:
`σ > 0` (p.6), `θ ≠ 0` ("We assume θ ≠ 0 throughout this paper", p.7), `τ > 0` (p.7),
`γ ≥ 0` (p.7), `α ∈ (0, 1)` and `k ≥ 0` (p.8), `β > 0` (p.8), and Assumption 1, `β > h`
((5), p.10, "the standing assumption of this paper").

**Formalization Note** `S₀ > 0` is added: a stock price is positive. -/
def Standing (p : Params) : Prop :=
  0 < p.σ ∧ p.θ ≠ 0 ∧ 0 < p.τ ∧ 0 ≤ p.γ ∧ 0 < p.α ∧ p.α < 1 ∧ 0 ≤ p.k ∧ 0 < p.β ∧
    p.h < p.β ∧ 0 < p.S₀

end Params

end PeriodicEval


