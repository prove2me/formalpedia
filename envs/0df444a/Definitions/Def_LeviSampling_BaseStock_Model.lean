-- Prove2me | Definitions.Def_LeviSampling_BaseStock_Model
-- name    : LeviSampling_BaseStock_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:24.5859+00:00
-- url     : https://prove2.me/theorems/19d3e61d-5259-4cc4-9a75-25fd93259b5c
-- title:
--   Multiperiod backlogging inventory model: newsvendor cost and the optimal dynamic program (1)–(2) (§3, pp. 827–829)
-- statement:
--   The finite-horizon periodic-review inventory model of Levi, Roundy and Shmoys (§3). There are $T$ periods, indexed here from $0$: period $i$ (with $i < T$) is the paper's period $i+1$. The demand $D_i$ of period $i$ is a real random variable with law $\mu_i$ (negative demand is allowed); demands of different periods are independent. Orders arrive immediately, unmet demand is backlogged, and ordering is free. If the inventory is raised to $y$ in period $i$, the period's cost is $h_i (y - D_i)^+ + b_i (D_i - y)^+$ with holding cost $h_i$ and backlogging cost $b_i$.
--
--   This file defines:
--
--   1. the **newsvendor cost** $C_i(y) = \mathbb E\big[h_i (y - D_i)^+ + b_i (D_i - y)^+\big]$ (p. 828);
--   2. the operator $\min_{y \ge x} f(y)$, written $\mathrm{minAbove}\,f\,(x)$ and taken as the infimum of $f$ over $[x, \infty)$;
--   3. the **smallest minimizer** of a function $f$: a point $r$ with $f(r) \le f(z)$ for all $z$, lying below every other global minimizer;
--   4. the **optimal dynamic program** (1)–(2), p. 828:
--   $$V_i(x) = \min_{y \ge x} U_i(y), \qquad U_i(y) = C_i(y) + \mathbb E\big[V_{i+1}(y - D_i)\big],$$
--   with $V_i \equiv 0$ for $i \ge T$, so that the last period has $U_{T-1} = C_{T-1}$ (the paper's $U_T = C_T$);
--   5. the **optimal expected cost** $\mathrm{OPT} = \min_y U_0(y)$, the paper's $\min_y U_1(y) = U_1(R_1)$.
--
--   The optimum is built from the demand laws alone and is independent of any sampling algorithm.
--
--   **Formalization Note** Periods are $0$-based natural numbers, and the laws $\mu_i$ and costs $h_i, b_i$ are given for every $i \in \mathbb N$; only $i < T$ matter. Expectations are Bochner integrals, which are $0$ for non-integrable integrands, so every theorem that uses these objects assumes $\mathbb E|D_i| < \infty$ (the paper's standing assumption, p. 824). The minimum $\min_{y\ge x}$ is a real infimum; all costs here are nonnegative, so it is the true infimum.
-- source:
--   Levi, Roundy & Shmoys, Provably Near-Optimal Sampling-Based Policies for Stochastic Inventory Control Models, Math. Oper. Res. 32(4) 2007, pp. 827–829, §3 and §3.1, eqs. (1)–(2)

import Mathlib

open MeasureTheory

namespace LeviSampling.BaseStock

/-! Multiperiod backlogging inventory model of Levi, Roundy & Shmoys (2007), §3, pp. 827–829.

Periods are indexed **from 0**: period `i : ℕ` with `i < T` is the paper's period `i + 1`.
`μ i` is the law of the demand `D_{i+1}` (a probability measure on `ℝ`; negative demand allowed),
`h i > 0` and `b i > 0` are the per-unit holding and backlogging costs of that period.
Demands of different periods are independent: every expectation over `D_i` below is an integral
against `μ i` alone, with the later periods' cost-to-go evaluated inside. -/

/-- The newsvendor (period) cost `C(y) = E[h (y - D)⁺ + b (D - y)⁺]` of raising the inventory to
`y` when the demand has law `μ` (p. 828). -/
noncomputable def nvCost (μ : Measure ℝ) (h b y : ℝ) : ℝ :=
  ∫ d, (h * max (y - d) 0 + b * max (d - y) 0) ∂μ

/-- `min_{y ≥ x} f(y)`, the cost of the best order-up-to level reachable from inventory `x`
(the operator of eq. (2), p. 828, and of Fact 3.1). -/
noncomputable def minAbove (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ⨅ y : Set.Ici x, f y

/-- `r` is the **smallest minimizer** of `f`: `f r ≤ f z` for every `z`, and every global
minimizer of `f` is `≥ r` (pp. 829–831). -/
def IsSmallestMinimizer (f : ℝ → ℝ) (r : ℝ) : Prop :=
  (∀ z, f r ≤ f z) ∧ ∀ y, (∀ z, f y ≤ f z) → r ≤ y

/-- The optimal cost-to-go `V_i(x)` of the dynamic program (1)–(2), p. 828: the minimum expected
cost over periods `i, …, T-1` (0-based) starting period `i` with inventory `x`,
`V_i(x) = min_{y ≥ x} [C_i(y) + E[V_{i+1}(y - D_i)]]`, and `V_i ≡ 0` for `i ≥ T`
(so that `U_{T-1} = C_{T-1}`, the paper's `U_T = C_T`). -/
noncomputable def optV (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (i : ℕ) (x : ℝ) : ℝ :=
  if _hi : i < T then
    minAbove (fun y => nvCost (μ i) (h i) (b i) y + ∫ d, optV T μ h b (i + 1) (y - d) ∂(μ i)) x
  else 0
termination_by T - i

/-- The optimal order-up-to cost `U_i(y) = C_i(y) + E[V_{i+1}(y - D_i)]`, eq. (1), p. 828
(0-based period `i`): the expected cost over periods `i, …, T-1` when the inventory in period `i`
is raised to `y` and an optimal policy is followed afterwards. -/
noncomputable def optU (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (i : ℕ) (y : ℝ) : ℝ :=
  nvCost (μ i) (h i) (b i) y + ∫ d, optV T μ h b (i + 1) (y - d) ∂(μ i)

/-- The optimal expected cost over the whole horizon, `min_y U_1(y)` (the paper's period 1 is
period `0` here), pp. 828–830. It is defined from the true dynamic program alone. -/
noncomputable def optCost (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) : ℝ :=
  ⨅ y : ℝ, optU T μ h b 0 y

end LeviSampling.BaseStock


