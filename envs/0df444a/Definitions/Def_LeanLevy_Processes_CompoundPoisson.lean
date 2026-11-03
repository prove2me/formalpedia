-- Prove2me | Definitions.Def_LeanLevy_Processes_CompoundPoisson
-- name    : LeanLevy_Processes_CompoundPoisson
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T22:01:06.761302+00:00
-- url     : https://prove2.me/theorems/6a1c6576-3eb4-42f7-b90a-b55a6775a7f2
-- title:
--   LeanLevy source module: Processes.CompoundPoisson
-- statement:
--   Source-faithful definition and structural-lemma bundle for `LeanLevy.Processes.CompoundPoisson`. It preserves the original Lean declarations, namespaces, assumptions and imported definitions. The upstream source is credited below. This is a draft pending Prove2Me compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.BorelCantelli

/-!
# Drivers for the compound Poisson process

A **compound Poisson driver** packages the two independent sources of randomness that build a
compound-Poisson-with-drift path: an i.i.d. sequence of exponential *interarrival times* `τ n` and
an i.i.d. sequence of *marks* `Y n`, all jointly independent on a common probability space.

The interarrival times generate the *arrival times*

`arrival τ n ω = ∑ i ∈ Finset.range (n + 1), τ i ω`,

the partial sums that mark when the jumps occur. This file records their almost-sure structure —
positivity, strict monotonicity, and divergence to `+∞`, and uses it to build the compound-Poisson
sample path itself and prove its almost-sure càdlàg regularity and pathwise Itô formula.

## Main definitions

* `ProbabilityTheory.arrival` — the arrival-time partial sums of the interarrival sequence.
* `ProbabilityTheory.IsCompoundPoissonDriver` — the joint independence and marginal-law data of the
  interarrival/mark sequences.
* `ProbabilityTheory.compoundPoisson` — the compound-Poisson-with-drift sample path, the
  `piecewisePath` built from the random arrival times and marks.

## Main results

* `ProbabilityTheory.exists_isCompoundPoissonDriver` — a compound Poisson driver exists for any
  positive rate `r` and any probability law `ν'` of the marks, on a canonical probability space.
* `ProbabilityTheory.measurable_compoundPoisson` — the compound Poisson path is measurable at each
  fixed time, so it is a genuine random variable.
* `ProbabilityTheory.IsCompoundPoissonDriver.ae_interarrival_pos` — the interarrival times are almost
  surely all positive.
* `ProbabilityTheory.IsCompoundPoissonDriver.ae_strictMono_arrival` — the arrival times are almost
  surely strictly increasing.
* `ProbabilityTheory.IsCompoundPoissonDriver.ae_tendsto_arrival` — the arrival times almost surely
  tend to `+∞`.
* `ProbabilityTheory.compoundPoisson_ae_start` — the compound Poisson path almost surely starts at
  `0`.
* `ProbabilityTheory.compoundPoisson_ae_isCadlag` — the compound Poisson process almost surely has
  càdlàg sample paths.
* `ProbabilityTheory.compoundPoisson_pathwise_ito` — **the pathwise Itô formula**: almost every
  sample path decomposes the increment of a `C¹` function along the process into the drift integral
  plus the sum of jump increments, with no stochastic integral needed.

## Implementation notes

The joint independence is stored as a single `iIndepFun` over the combined index type `ℕ ⊕ ℕ`, with
the interarrival family on the `Sum.inl` block and the mark family on the `Sum.inr` block, glued by
`Sum.elim τ Y`. This one-family spelling is what lets later layers extract *any* disjoint-block
independence (interarrivals ⟂ marks, or finite subfamilies of either): the per-block families are
exposed as `IsCompoundPoissonDriver.iIndepFun_interarrival` / `.iIndepFun_mark`, and finer splits
follow via `iIndepFun.precomp` and `iIndepFun.indepFun_finset`.

Because `isProbabilityMeasure_expMeasure` requires a strictly positive rate, the existence theorem
and every almost-sure lemma carries a hypothesis `hr : 0 < r`.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}

/-- The `n`-th arrival time of the interarrival sequence `τ`: the partial sum of the first `n + 1`
interarrival times. -/
def arrival (τ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range (n + 1), τ i ω





variable [MeasurableSpace Ω]

/-- A **compound Poisson driver**: an i.i.d. exponential interarrival sequence `τ` (rate `r`) and an
i.i.d. mark sequence `Y` (law `ν'`), jointly independent on the probability space `(Ω, μ)`.

The joint independence is a single `iIndepFun` over `ℕ ⊕ ℕ` via `Sum.elim τ Y`, so that any
disjoint-block independence between the two families (or within a family) is recoverable. -/
structure IsCompoundPoissonDriver (τ Y : ℕ → Ω → ℝ) (r : ℝ≥0) (ν' : Measure ℝ)
    (μ : Measure Ω) : Prop where
  /-- Each interarrival time is measurable. -/
  measurable_interarrival : ∀ n, Measurable (τ n)
  /-- Each mark is measurable. -/
  measurable_mark : ∀ n, Measurable (Y n)
  /-- The interarrival and mark families are jointly independent, as one `ℕ ⊕ ℕ`-indexed family. -/
  indep : iIndepFun (Sum.elim τ Y) μ
  /-- Each interarrival time is exponentially distributed with rate `r`. -/
  law_interarrival : ∀ n, HasLaw (τ n) (expMeasure r) μ
  /-- Each mark has law `ν'`. -/
  law_mark : ∀ n, HasLaw (Y n) ν' μ

namespace IsCompoundPoissonDriver

variable {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}























end IsCompoundPoissonDriver



section CompoundPoisson

variable {b : ℝ} {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}

/-- The **compound-Poisson-with-drift sample path**: the deterministic `piecewisePath` starting at
`0`, drifting at rate `b`, with jump times given by the random arrival times `arrival τ · ω` and
jump sizes given by the random marks `Y · ω`. At a fixed time `t` this is a random variable in `ω`. -/
noncomputable def compoundPoisson (b : ℝ) (τ Y : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  piecewisePath 0 b (fun n => arrival τ n ω) (fun n => Y n ω) t













end CompoundPoisson

end ProbabilityTheory


