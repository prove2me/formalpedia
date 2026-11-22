-- Prove2me | Definitions.Def_ShiOptrates_Spider
-- name    : ShiOptrates_Spider
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-08T22:25:35.740368+00:00
-- url     : https://prove2.me/theorems/c1fa677c-a080-4e6d-b18d-2feb0a95849c
-- title:
--   The SPIDER schedule: epoch lengths, accuracy targets, and the classical/quantum query totals
-- statement:
--   The parameter block of the SPIDER variance-reduction schedule, together with the two query totals it induces.
--
--   The schedule is specified by an epoch length $\mathrm{qLen}$, two accuracy targets $\mathrm{sHat}_1$ and $\mathrm{sHat}_2$ for the two estimator stages, an iteration budget $\mathrm{iterBudget}$, and a per-query price $\mathrm{mePrice}$. Aggregating these gives $\mathrm{spiderTotal}$, and evaluating that aggregate at the two cost exponents gives $\mathrm{classicalIncrement}$ and $\mathrm{quantumIncrement}$.
--
--   $$\mathrm{spiderTotal}\;\xrightarrow{\;p=2\;}\;\mathrm{classicalIncrement}\qquad \mathrm{spiderTotal}\;\xrightarrow{\;p=1\;}\;\mathrm{quantumIncrement}$$
--
--   These are the objects in which the mission's crossover statement is phrased: one schedule, two cost exponents, and a comparison of the resulting bills. Concrete values of the parameters are given in the definitions themselves so that all constants in the downstream bounds are explicit rather than asymptotic.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Spider.lean | Schedule parameters follow Sidford & Zhang, arXiv:2308.01582 (Algorithm 7); the library records a discrepancy in that paper's parameter block, documented in its STATUS notes. | Formalized by Yueheng Shi; Apache License 2.0. Platform copy produced by declaration-graph skeleton subtraction; root namespace `OptRates` renamed to `ShiOptRates`.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Spider.lean
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
import Definitions.Def_ShiOptrates_Stochastic_VariancePurchase
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
# L4 / GL4 — SPIDER and Q-SPIDER

The recursive variance-reduction rate, at both cost exponents.

SPIDER (Fang et al. 2018) refreshes a full gradient estimate every `q` steps and, in
between, updates it by an estimate of the *increment* `∇f(xₜ) - ∇f(xₜ₋₁)`.  Under mean-
squared smoothness the increment is small — its variance is at most `ℓ²‖xₜ - xₜ₋₁‖²` — so
it can be estimated cheaply, and the accumulated error over an epoch is controlled by
`Stochastic.accumulation_sq`.

Q-SPIDER (Sidford–Zhang, arXiv:2308.01582, Algorithm 7) is the *same algorithm with the
same schedule*, with the classical variance-reduction step replaced by their quantum
variance reduction (their Theorem 4), which delivers an **unbiased** estimate of variance
`σ̂²` at price `√d · scale / σ̂` instead of the classical `scale² / σ̂²`.

So the two published rates, `ε⁻³` and `√d ε⁻⁵ᐟ²`, are the *same schedule* priced at two
cost exponents.  That is what `spider_queries_classical` and `spider_queries_quantum`
below establish, in closed form with explicit constants.

## Main definitions

* `MeanSquaredSmooth` — `E‖G x ω - G y ω‖² ≤ ℓ²‖x - y‖²`, the function class SPIDER needs.
* `mePrice scale σhat p a` — `a · (scale/σhat)^p`: mean-estimation price, classical at
  `p = 2, a = 1` and quantum at `p = 1, a = √d`.
* `spiderTotal` — the query bill of Algorithm 7's schedule at a given exponent.

## Main results

* `increment_variance_le` — the increment-variance bound, and `increment_variance_le_sq`
  its specialization at the algorithm's normalized step `ε/ℓ`.
* `epoch_error_le` — the accumulated epoch error, via `accumulation_sq`.
* `schedule_budget` — **the schedule verification**: Algorithm 7's `(q, σ̂₁, σ̂₂)` spend
  exactly `3ε²/1600` of error budget, so the claimed accuracy holds with slack.
* `spider_queries_classical` — `≍ 2.56·10⁷ · ℓ Δ σ / ε³`.
* `spider_queries_quantum` — `≍ 6.4·10⁴ √10 · ℓ Δ √(dσ) / ε⁵ᐟ²`.
* `quantum_beats_classical_iff` — the crossover: the quantum bill is smaller exactly when
  `d ε < 16000 σ`.  The dimension-versus-accuracy tradeoff, with the constant.

## What this file does and does not establish

It reproduces the **query complexity** of both algorithms, with explicit constants, and the
epoch error control that makes the schedule valid.  It does *not* prove that Algorithm 7's
output is an `ε`-critical point: that is Fang et al.'s Theorem 1, which Sidford–Zhang also
import rather than reprove (their Theorem 9).  The formalization therefore mirrors the
structure of the published proof exactly — correctness cited, query count computed — and
the correctness half remains open.  Closing it means formalizing SPIDER's descent argument
under the normalized step and the `‖vₜ‖ ≤ 2ε` early return.
-/

namespace ShiOptRates.Spider

open MeasureTheory Finset
open scoped InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The function class -/

/-! ### The epoch error, via the accumulation law -/

variable [IsProbabilityMeasure μ] [CompleteSpace E]

end ShiOptRates.Spider

/-! ### The schedule and the query bill

From here everything is arithmetic on Algorithm 7's stated parameters:

`q = 20σ/ε`, `σ̂₁ = ε/40`, `σ̂₂ = (ε/40)·√(ε/(10σ))`, budget `𝒯 = 1600 ℓΔ/ε²`.
-/

namespace ShiOptRates.Spider

/-- Algorithm 7's epoch length. -/
noncomputable def qLen (σ ε : ℝ) : ℝ := 20 * σ / ε

/-- Algorithm 7's variance target at an epoch start. -/
noncomputable def sHat₁ (ε : ℝ) : ℝ := ε / 40

/-- Algorithm 7's variance target for an increment. -/
noncomputable def sHat₂ (σ ε : ℝ) : ℝ := ε / 40 * Real.sqrt (ε / (10 * σ))

/-- Algorithm 7's total iteration budget, `1600 ℓ Δ / ε²`.

**Discrepancy with the source, recorded.**  Sidford–Zhang's Algorithm 7 parameter block
states `𝒯 = 1600 ℓ Δ / σ²` (the LaTeX in the published source reads
`\frac{1600\ell\Delta}{\sigma^{2}}`).  That value is inconsistent with their own
Theorem 8: it yields an increment bill of `≍ ℓ Δ √d / (σ^{3/2} √ε)`, i.e. `ε^{-1/2}`, not
`ε^{-5/2}`.  With `ε²` in the denominator the bill is exactly
`64000 √10 · ℓ Δ √(dσ) ε^{-5/2}`, which is Theorem 8 as stated — see
`spider_queries_quantum`.  `ε²` is also what the algorithm's own step size forces: the step
`x_{t+1} = x_t - (ε/ℓ)·v_t/‖v_t‖` has length `ε/ℓ` and buys `Θ(ε²/ℓ)` of objective
decrease, so a budget of `Δ` supports `Θ(ℓΔ/ε²)` steps.  We therefore take `ε²`; the `σ²`
is a typo. -/
noncomputable def iterBudget (ℓ Δ ε : ℝ) : ℝ := 1600 * ℓ * Δ / ε ^ 2

/-- **Mean-estimation price.**  `a · (scale/σ̂)^p` queries to reach variance `σ̂²` when
estimating a random variable of variance scale `scale²`.

* `p = 2`, `a = 1`: classical averaging, `scale²/σ̂²`.
* `p = 1`, `a = √d`: quantum variance reduction (Sidford–Zhang Thm 4), `√d · scale/σ̂`.

The unification is the point: `spiderTotal` below is one formula, and the two published
rates are its two instances. -/
noncomputable def mePrice (scale σhat : ℝ) (p : ℕ) (a : ℝ) : ℝ := a * (scale / σhat) ^ p

/-- The total query bill of Algorithm 7's schedule at cost exponent `p` and prefactor `a`:
epoch-start estimates (variance scale `σ`) plus increment estimates (variance scale `ε`,
by `increment_variance_le_sq`). -/
noncomputable def spiderTotal (ℓ Δ σ ε : ℝ) (p : ℕ) (a : ℝ) : ℝ :=
  iterBudget ℓ Δ ε / qLen σ ε * mePrice σ (sHat₁ ε) p a
    + iterBudget ℓ Δ ε * mePrice ε (sHat₂ σ ε) p a

/-- The `ε⁻⁵ᐟ²` term of the quantum bill — the dominant one. -/
noncomputable def quantumIncrement (ℓ Δ σ ε d : ℝ) : ℝ :=
  64000 * ℓ * Δ * Real.sqrt d * Real.sqrt (10 * σ) / (ε ^ 2 * Real.sqrt ε)

/-- The `ε⁻³` term of the classical bill — the dominant one. -/
noncomputable def classicalIncrement (ℓ Δ σ ε : ℝ) : ℝ :=
  25600000 * ℓ * Δ * σ / ε ^ 3

/-! ### The correctness half: the algorithm cannot run forever without returning

Algorithm 7 takes a *normalized* step of length `ε/ℓ` in the direction `-vₜ/‖vₜ‖`, and
returns `xₜ` as soon as `‖vₜ‖ ≤ 2ε`.  The content of correctness is that it must return
soon: while `‖vₜ‖ > 2ε` and the estimate is `ε`-accurate, every step buys `ε²/(2ℓ)` of
objective decrease, so at most `2ℓΔ₀/ε²` such steps can occur.

Everything here is deterministic, conditioned on the accuracy event `‖vₜ - ∇f(xₜ)‖ ≤ ε`;
`epoch_error_le` is what makes that event likely.  The remaining gap to Fang et al.'s
Theorem 1 is the probabilistic wrapper — bounding `E‖e_τ‖` at the *random* return time `τ`,
where conditioning on `τ = k` breaks the unconditional variance bound.  That step, and only
that step, is still open. -/

section Correctness

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {ℓ ε : ℝ}

end Correctness

end ShiOptRates.Spider


