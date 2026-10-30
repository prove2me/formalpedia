-- Prove2me | Definitions.Def_BSSSampleRobust_Asymptotic_Transport
-- name    : BSSSampleRobust_Asymptotic_Transport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T22:26:17.797546+00:00
-- url     : https://prove2.me/theorems/bac29c8b-a406-4580-bf29-205cbb84b40b
-- title:
--   Completed extended expectation, extrema and transport ambiguity objectives
-- statement:
--   The expectation applies the published positive-part-first extended expectation to the completion of a measure: if the positive integral is infinite the result is $+\infty$, otherwise the negative integral is subtracted. Nonmeasurable inputs use the lower integral. Pointwise extrema take values in $[-\infty,+\infty]$, and truncation is zero outside a set. The scaling helper gives zero when its coefficient is zero, including on infinite values; averages are finite sums divided by $N$. Probability laws concentrated on $Z$ are those with total mass one and indicator expectation $E_Q[I_Z]=1$, as explicitly defined on page 6. The moment-constrained worst expectation and Wasserstein-constrained worst expectation are actual suprema over those laws, using the published coupling distance, with no integrability restriction. A subtype function is extended by zero for ambient integration. No concentration inequality is assumed.
-- source:
--   Bertsimas, Shtern and Sturt (2023), A Data-Driven Approach to Multistage Stochastic Linear Optimization, Management Science, https://doi.org/10.1287/mnsc.2022.4352; published basis, supplied manuscript/e-companion artifact; §1.2, PDF/printed 6; §6, PDF/printed 22–23; Lemmas EC.1, EC.2, EC.4, PDF 57,59,62 / ec15,ec17,ec20

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_DupacovaWets_Consistency_expect

open MeasureTheory
open scoped ENNReal
noncomputable section

open scoped ENNReal Classical

namespace BSSSampleRobust.Asymptotic

/-- The referenced extended expectation on the completion; lower integral off its domain. -/
def expectation {E : Type*} [MeasurableSpace E] (Q : Measure E) (f : E → EReal) : EReal :=
  DupacovaWets.Consistency.expect Q.completion f

/-- A pointwise supremum, with empty value minus infinity and unbounded value plus infinity. -/
def supremum {E : Type*} (Z : Set E) (f : E → ℝ) : EReal :=
  ⨆ z ∈ Z, (f z : EReal)

def absSup {E : Type*} (Z : Set E) (f : E → ℝ) : EReal :=
  supremum Z (fun z => |f z|)

def truncated {E : Type*} (Z : Set E) (f : E → ℝ) (z : E) : EReal :=
  if z ∈ Z then (f z : EReal) else 0

/-- Nonnegative real scaling, explicitly zero even on an infinite argument. -/
def scale (a : ℝ) (v : EReal) : EReal := if a = 0 then 0 else (a : EReal) * v

def average {N : ℕ} (v : Fin N → EReal) : EReal :=
  scale ((N : ℝ)⁻¹) (∑ j, v j)

/-- Probability distributions on Z: the indicator expectation is one (p. 6). -/
def concentrated {E : Type*} [MeasurableSpace E] (Z : Set E) (Q : Measure E) : Prop :=
  IsProbabilityMeasure Q ∧ expectation Q (truncated Z (fun _ => 1)) = 1

def momentWorst {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (Z : Set E) (c : E) (θ : ℝ) (f : E → ℝ) : EReal :=
  ⨆ (Q : Measure E) (_ : concentrated Z Q)
    (_ : expectation Q (fun z => (‖z - c‖ : EReal)) ≤ (θ : EReal)),
    expectation Q (fun z => (f z : EReal))

def transportWorst {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (Z : Set E) (ν : Measure E) (θ : ℝ) (f : E → EReal) : EReal :=
  ⨆ (Q : Measure E) (_ : concentrated Z Q)
    (_ : WassersteinDRO.Duality.wassersteinDistance 1 Q ν ≤ ENNReal.ofReal θ),
    expectation Q f

/-- Extend a function on an arbitrary subset by zero, with no regularity imposed outside it. -/
def extendFrom {E : Type*} (Z : Set E) (g : Z → ℝ) (z : E) : ℝ :=
  if h : z ∈ Z then g ⟨z, h⟩ else 0

end BSSSampleRobust.Asymptotic


