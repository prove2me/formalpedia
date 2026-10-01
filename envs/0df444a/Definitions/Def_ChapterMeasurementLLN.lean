-- Prove2me | Definitions.Def_ChapterMeasurementLLN
-- name    : ChapterMeasurementLLN
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:16:29.019469+00:00
-- url     : https://prove2.me/theorems/d7c48af5-5b31-4ca2-8ab4-8c0ad85a2c76
-- title:
--   Chapter MeasurementLLN
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterMeasurementLLN.lean`): generated def bundle for ChapterMeasurementLLN. See BookProof/ChapterMeasurementLLN.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMeasurementLLN.lean

import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §10
*"Ensemble forecasting …"* — measurements reproduce the probability distribution
in the limit of infinitely many measurements

This file formalizes the self-contained mathematical claim of the section
*"10. Ensemble forecasting allows the approximation of a non-linear
infinite-dimensional model …"* (`book.tex` line ~2005):

> *"a measurement is applying the Bayes rule to update a probability: destroy the
> uncertainty … by converting probabilities into events, unpredictably and
> **reproducing the probability distribution in the limit of infinite
> measurements**. … It is not different from an unbiased sampling process taken
> over infinite time."*

The precise mathematical statement is the **strong law of large numbers** applied
to a (finite-outcome) measurement: if we repeat a measurement `M` — an i.i.d.
sequence of `Fin k`-valued random variables, each distributed like the physical
state being measured — then for every outcome `a` the **empirical frequency** of
`a` over the first `n` measurements,

`freqₙ(a) = (number of i < n with Mᵢ = a) / n`,

converges *almost surely*, as `n → ∞`, to the true probability of that outcome,
`ℙ(M₀ = a)`.  In other words, an infinite sequence of measurements reproduces the
probability distribution of the state, exactly as the book asserts.

## Deliverables

* `outcomeIndicator` — the `{0,1}`-valued indicator of the event "`Mᵢ = a`".
* `outcomeIndicator_integral` — its expectation is the outcome probability,
  `∫ outcomeIndicator M a 0 = (ℙ(M₀ = a)).toReal`.
* `measurement_average_tendsto` — the general real-observable version (the
  "unbiased sampling over infinite time" statement): the running average of an
  observable `f ∘ Mᵢ` tends a.s. to its expectation `𝔼[f ∘ M₀]`.
* `measurement_frequency_tendsto` — the headline: for i.i.d. measurements the
  empirical frequency of every outcome `a` tends almost surely to the outcome
  probability `(ℙ(M₀ = a)).toReal`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BookProof.ChapterMeasurementLLN

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {k : ℕ}

/-- The `{0,1}`-valued indicator of the measurement outcome "`Mᵢ = a`",
i.e. the observable that returns `1` when the `i`-th measurement yields outcome
`a` and `0` otherwise. -/
noncomputable def outcomeIndicator (M : ℕ → Ω → Fin k) (a : Fin k) (i : ℕ) : Ω → ℝ :=
  fun ω => if M i ω = a then (1 : ℝ) else 0







end BookProof.ChapterMeasurementLLN


