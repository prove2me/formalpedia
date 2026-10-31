-- Prove2me | Definitions.Def_DynTargetMV_Market
-- name    : DynTargetMV_Market
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:21.01961+00:00
-- url     : https://prove2.me/theorems/908ba833-4587-46ea-a742-888220b298e0
-- title:
--   The market data $(r,b,\sigma,Q,T,x_0)$
-- statement:
--   The market consists of a risk-free asset and $m$ risky stocks, driven by a $d$-dimensional Brownian motion. Its data are:
--
--   1. the risk-free rate $r(t)$;
--   2. the mean excess return rate vector $b(t)\in\mathbb R^m$;
--   3. the volatility matrix $\sigma(t)\in\mathbb R^{m\times d}$;
--   4. the $n$-by-$m$ matrix $Q$ of the portfolio constraints $Q\pi\ge 0$;
--   5. the end date $T>0$ and the initial wealth $x_0>0$.
--
--   Every other object of the mission is built on these data.
--
--   **Formalization Note** The functions are total on $\mathbb R$, and only times $t\ge 0$ are used. The case $n=0$ (no portfolio constraint) is allowed. The positivity of $T$ and $x_0$ is part of the data.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, §2.1, p.6; §2.2, p.7

import Mathlib

namespace DynTargetMV

/-- The data of the market and of the agent: the risk-free rate `r`, the mean excess return rate
vector `b`, the volatility matrix `σ` (`m` stocks, `d` Brownian motions), the `n`-by-`m` portfolio
constraint matrix `Q` (constraints `Qπ ≥ 0`), the end date `T > 0`, and the initial wealth `x₀ > 0`.
He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, §2.1, p.6 and §2.2, p.7.

**Formalization Note** ℝ^m is `Fin m → ℝ` and `σ(t)` is a `Matrix (Fin m) (Fin d) ℝ`. The functions are
total on `ℝ`; only times `t ≥ 0` are used. `n = 0` (no portfolio constraint) is allowed. The positivity
of `T` and `x₀` are part of the data (p.7: "given and assumed to be positive"). -/
structure Market (m d n : ℕ) where
  /-- The risk-free rate `r(t)`. -/
  r : ℝ → ℝ
  /-- The mean excess return rate vector `b(t)`. -/
  b : ℝ → Fin m → ℝ
  /-- The volatility matrix `σ(t)`. -/
  σ : ℝ → Matrix (Fin m) (Fin d) ℝ
  /-- The portfolio constraint matrix `Q`. -/
  Q : Matrix (Fin n) (Fin m) ℝ
  /-- The end date `T`. -/
  T : ℝ
  /-- The initial wealth `x₀`. -/
  x₀ : ℝ
  /-- The horizon is positive. -/
  T_pos : 0 < T
  /-- The initial wealth is positive. -/
  x₀_pos : 0 < x₀

end DynTargetMV


