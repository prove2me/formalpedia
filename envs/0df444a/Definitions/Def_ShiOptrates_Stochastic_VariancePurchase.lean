-- Prove2me | Definitions.Def_ShiOptrates_Stochastic_VariancePurchase
-- name    : ShiOptrates_Stochastic_VariancePurchase
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-08T22:25:08.573053+00:00
-- url     : https://prove2.me/theorems/1432af20-198e-48bd-b93c-329e28da9276
-- title:
--   $\mathrm{sgdIterations}$ and $\mathrm{variancePurchaseTotal}$: buying variance reduction at a chosen exponent
-- statement:
--   The schedule that spends oracle queries to reduce variance, with the price left as a parameter.
--
--   Here $\mathrm{sgdIterations}$ is the iteration count a target accuracy requires, and $\mathrm{variancePurchaseTotal}$ is the resulting bill, the iteration count multiplied by the per-step price drawn from a cost model:
--   $$\mathrm{variancePurchaseTotal}=\mathrm{sgdIterations}\cdot\mathrm{powerCost}.$$
--
--   Because the price is a cost-model parameter, evaluating this one quantity at $p=2$ gives the classical bound $8aL\Delta_0/\varepsilon^{4}$ and at $p=1$ the quantum bound $8aL\Delta_0\hat\sigma/\varepsilon^{4}$; the two published rates differ only in that exponent.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Stochastic/VariancePurchase.lean | Formalized by Yueheng Shi; Apache License 2.0. Platform copy produced by declaration-graph skeleton subtraction; root namespace `OptRates` renamed to `ShiOptRates`.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/VariancePurchase.lean
Original work Copyright (c) 2026 Yueheng Shi, released under the Apache License,
Version 2.0.  The original copyright and author notices are retained below.

MODIFICATIONS made for publication on Prove2me: declarations not reachable from
the published targets were removed by declaration-graph skeleton subtraction;
project imports were rewritten to platform `Definitions.Def_*` / `Theorems.Thm_*`
modules; the root namespace `OptRates` was renamed to `ShiOptRates`; 
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiOptrates_Cost
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_ShiOptrates_Stochastic_Bridge
import Definitions.Def_ShiOptrates_Stochastic_Recursion
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Martingale.Basic
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# The mechanism: buying variance, and why the cost exponent decides everything

`Stochastic.sgd_rate` needs `K ≥ 8 L Δ₀ σ̂² / ε⁴` iterations from an oracle whose variance
is `σ̂²`.  But `σ̂` is not given by nature — it is *purchased*.  An oracle that averages
samples, or a quantum mean estimator, delivers variance `σ̂²` at a price
`price(σ̂) = a / σ̂ ^ p`, and `p` is the whole story:

| `p` | estimator | total queries |
|---|---|---|
| `2` | classical averaging, `a = L²` | `8 a L Δ₀ / ε⁴` — **independent of `σ̂`** |
| `1` | quantum mean estimation, `a ≍ L√d` | `8 a L Δ₀ σ̂ / ε⁴` — **strictly decreasing in `σ̂`** |

At `p = 2` the `σ̂²` in the iteration count cancels the `σ̂⁻²` in the price exactly, so
buying variance reduction is *cost-neutral*: this is the formal reason a classical sampler
cannot improve SGD's `ε⁻⁴` by averaging harder.  At `p = 1` the cancellation is incomplete
and the purchase is strictly profitable.  That broken tie is the mechanism behind every
quantum stochastic-optimization speedup in the literature.

This is the library's central abstraction discharged at L3: the classical and quantum
analyses share the oracle contract (*unbiased, variance `σ̂²`*) and the entire rate
analysis, and differ in one natural number.

Note which contract appears here: **unbiased**, not bounded-error.  Sidford–Zhang
(arXiv:2308.01582) make exactly this choice, debiasing the quantum estimator by MLMC
before using it, because — in their words — its bias "hinders its combination with various
optimization algorithms assuming unbiased inputs".  `Stochastic.accumulation_linear_tight`
is the machine-checked form of that obstruction.

## Main results

* `variance_purchase_total` — the total query bill as a function of `σ̂` and `p`.
* `variance_purchase_classical` — at `p = 2` the bill does not depend on `σ̂`.
* `variance_purchase_quantum` — at `p = 1` it is linear in `σ̂`.
* `variance_purchase_strict_gain` — hence strictly profitable to reduce `σ̂` when `p = 1`
  and exactly neutral when `p = 2`.
-/

namespace ShiOptRates.Stochastic

open CostModel

/-- Iterations needed by `sgd_rate` at oracle variance `σ̂²`. -/
noncomputable def sgdIterations (L Δ ε σhat : ℝ) : ℝ := 8 * L * Δ * σhat ^ 2 / ε ^ 4

/-- Total queries: iterations at variance `σ̂²`, times the price of variance `σ̂²`. -/
noncomputable def variancePurchaseTotal (a L Δ ε σhat : ℝ) (p : ℕ) (ha : 0 ≤ a) : ℝ :=
  sgdIterations L Δ ε σhat * (powerCost a p ha).cost σhat

/-! ### Calibration: Q-SGD

Buying variance below `ε` is wasted — the iteration count `8LΔ₀σ̂²/ε⁴` drops below one — so
the purchase stops at `σ̂ ≍ ε`.  Evaluating the bill there recovers the two published
bounded-variance rates. -/

end ShiOptRates.Stochastic


