-- Prove2me | Definitions.Def_ShiOptrates_Cost
-- name    : ShiOptrates_Cost
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-08T22:23:39.815554+00:00
-- url     : https://prove2.me/theorems/b1b7df56-8ab5-4bb1-af2b-4a9d335f3069
-- title:
--   Oracle cost models: $\mathrm{CostModel}$, its power law, and the classical/quantum instances
-- statement:
--   The bookkeeping that turns an iteration count into a query bill, so that classical and quantum costs are two members of one family rather than two separate theorems.
--
--   A $\mathrm{CostModel}$ assigns to a target accuracy the number of oracle queries needed to meet it. The power law $\mathrm{powerCost}$ has exponent $p$; its $p=2$ member is $\mathrm{minibatch}$, the classical variance-reduction bill scaling as $\sigma^{2}/\varepsilon^{2}$, and its $p=1$ member is $\mathrm{quantumMean}$, the quantum mean-estimation bill scaling as $\sigma/\varepsilon$. Finally $\mathrm{totalCost}$ aggregates a per-step price over a schedule.
--
--   $$\text{classical: } p=2 \qquad\text{quantum: } p=1$$
--
--   The single exponent $p$ is what makes the library's central claim expressible as a term rather than as prose: the classical rate and the quantum rate are one theorem evaluated at two exponents.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Cost.lean | Formalized by Yueheng Shi; Apache License 2.0. Platform copy produced by declaration-graph skeleton subtraction; root namespace `OptRates` renamed to `ShiOptRates`.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Cost.lean
Original work Copyright (c) 2026 Yueheng Shi, released under the Apache License,
Version 2.0.  The original copyright and author notices are retained below.

MODIFICATIONS made for publication on Prove2me: declarations not reachable from
the published targets were removed by declaration-graph skeleton subtraction;
project imports were rewritten to platform `Definitions.Def_*` / `Theorems.Thm_*`
modules; the root namespace `OptRates` was renamed to `ShiOptRates`; 
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# L0 — Cost accounting

The piece of the library with no analogue in Mathlib or in the existing Lean
optimization formalizations: an oracle's *price list*.

A `CostModel` is a map from requested accuracy to number of queries.  A classical
minibatch mean estimator and a quantum multivariate mean estimator are two terms of this
one type, and — see `minibatch_eq_powerCost` and `quantumMean_eq_powerCost` — two members
of the same one-parameter family `PowerCost a p : cost δ = a / δ ^ p`, differing only in
the exponent `p` (`2` classical, `1` quantum).  Every rate separation proved in this
library is downstream of that single numeral.

## Main definitions

* `CostModel` — accuracy `↦` queries, nonnegative on positive accuracies.
* `CostModel.powerCost a p`, `CostModel.exact`, `CostModel.minibatch`,
  `CostModel.quantumMean` — the instances.
* `CostModel.totalCost C δ K` — `∑_{k<K} cost (δ k)`, the price of an accuracy schedule.

## Main results

* `totalCost_const` — constant schedule: `K * cost δ`.
* `totalCost_geometric` — geometric schedule against a power-law cost, in closed form.
* `totalCost_powerCost_const` — the form the rate theorems consume.
-/

namespace ShiOptRates

open Finset

/-- An oracle's price list: how many queries it takes to answer to accuracy `δ`.

Nonnegativity is only required on positive accuracies, which is all a schedule ever
requests; this lets the field be a bare formula (`σ²/δ²`) instead of a truncation. -/
structure CostModel where
  /-- Queries needed to reach accuracy `δ`. -/
  cost : ℝ → ℝ
  /-- Costs are nonnegative at positive accuracies. -/
  cost_nonneg : ∀ δ : ℝ, 0 < δ → 0 ≤ cost δ

namespace CostModel

/-- The power-law cost family `δ ↦ a / δ ^ p`.  Both estimators used in the literature
are instances; the classical/quantum separation is the value of `p`. -/
noncomputable def powerCost (a : ℝ) (p : ℕ) (ha : 0 ≤ a) : CostModel where
  cost := fun δ => a / δ ^ p
  cost_nonneg := fun δ hδ => by positivity

/-- Classical minibatch mean estimation: `σ²/δ²` samples for accuracy `δ`. -/
noncomputable def minibatch (σ : ℝ) : CostModel where
  cost := fun δ => σ ^ 2 / δ ^ 2
  cost_nonneg := fun δ hδ => by positivity

/-- Quantum multivariate mean estimation: `scale * √dim * σ / δ * log(1/η)` queries for
accuracy `δ` at failure probability `η`.  Linear in `1/δ` where the classical estimator
is quadratic; the `√dim` and the `log(1/η)` are carried explicitly rather than inside
an `Õ`. -/
noncomputable def quantumMean (dim : ℕ) (σ η scale : ℝ) (hσ : 0 ≤ σ) (hscale : 0 ≤ scale)
    (hη0 : 0 < η) (hη1 : η ≤ 1) : CostModel where
  cost := fun δ => scale * Real.sqrt dim * σ / δ * Real.log (1 / η)
  cost_nonneg := fun δ hδ => by
    have hlog : 0 ≤ Real.log (1 / η) :=
      Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
    have hpre : 0 ≤ scale * Real.sqrt dim * σ / δ := by positivity
    exact mul_nonneg hpre hlog

/-- Total queries spent by an accuracy schedule `δ : ℕ → ℝ` over `K` iterations. -/
noncomputable def totalCost (C : CostModel) (δ : ℕ → ℝ) (K : ℕ) : ℝ := ∑ k ∈ range K, C.cost (δ k)

@[simp] theorem totalCost_zero (C : CostModel) (δ : ℕ → ℝ) : C.totalCost δ 0 = 0 := by
  simp [totalCost]

end CostModel

end ShiOptRates


