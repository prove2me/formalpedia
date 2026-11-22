-- Prove2me | Definitions.Def_ShiOptrates_Stochastic_Stopped
-- name    : ShiOptrates_Stochastic_Stopped
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-08T22:26:00.884934+00:00
-- url     : https://prove2.me/theorems/db3c0404-091e-4095-8895-43ae5f9cc153
-- title:
--   Stopped-time increments: $\mathrm{stoppedIncr}$ and $\mathrm{stoppedFactor}$
-- statement:
--   The two constructions needed to evaluate an error recursion at a random index rather than a fixed one.
--
--   For an increment process and a stopping time $\tau$, $\mathrm{stoppedIncr}$ is the increment sequence frozen at $\tau$, and $\mathrm{stoppedFactor}$ is the accompanying multiplicative weight.
--
--   $$\text{fixed index } k \;\longmapsto\; \text{random index } \tau$$
--
--   Random return times are where a schedule's analysis usually breaks, because conditioning on $\tau=k$ destroys an unconditional variance bound. These definitions are what let the accumulation law be restated at a stopped time with the same constant as the fixed-index version.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Stochastic/Stopped.lean | Formalized by Yueheng Shi; Apache License 2.0. Platform copy produced by declaration-graph skeleton subtraction; root namespace `OptRates` renamed to `ShiOptRates`.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/Stopped.lean
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
# The accumulation law at a stopped time

`accumulation_sq` bounds `E‖e_K‖²` at a *fixed* index `K`.  Algorithms that stop
adaptively — SPIDER returns as soon as `‖vₜ‖ ≤ 2ε` — need the bound at the **random** index
`τ`, and the naive route fails: conditioning on `{τ = k}` destroys the unconditional
variance bound, which is exactly why `Spider.output_critical` is stated pathwise and why
Sidford–Zhang import Fang et al.'s Theorem 1 rather than reproving it.

The fix is to stop the process rather than the bound.  Write

`s_k = e_{τ ∧ k}`,  so that  `s_{k+1} = s_k + 1_{k < τ} ξ_k`,

and observe that `1_{k < τ} s_k` is still `ℱ_k`-measurable, so the *same* pull-out
(`integral_inner_condExp`) gives orthogonality of the stopped increments.  Then
`accumulation_sq` applies verbatim and the constant does not change:

`E‖e_{τ∧K}‖² ≤ E‖e_0‖² + K δ².`

## Main results

* `stopped_orthogonal` — the stopped increments inherit `L²` orthogonality.
* `accumulation_sq_stopped` — the accumulation law at a stopped time, same constant.
* `stopped_eq_of_le` — `s K = e_τ` when `τ ≤ K`, so the bound is about `e_τ` itself.
* `prob_stopped_error_large_le` — Markov: the accuracy event
  `‖e_τ‖ ≤ ε` fails with probability at most `(E‖e_0‖² + K δ²)/ε²`.  This is what feeds
  `Spider.output_critical`'s hypothesis.
-/

namespace ShiOptRates.Stochastic

open MeasureTheory Filter
open scoped InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The stopped increment: `ξ k` while the process is still running, `0` afterwards. -/
def stoppedIncr (ξ : ℕ → Ω → E) (τ : Ω → ℕ) (k : ℕ) (ω : Ω) : E :=
  if k < τ ω then ξ k ω else 0

/-- The `ℱ_k`-measurable factor that the pull-out consumes. -/
def stoppedFactor (s : ℕ → Ω → E) (τ : Ω → ℕ) (k : ℕ) (ω : Ω) : E :=
  if k < τ ω then s k ω else 0

end ShiOptRates.Stochastic


