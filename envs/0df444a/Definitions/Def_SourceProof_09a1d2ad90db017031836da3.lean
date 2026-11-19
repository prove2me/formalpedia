-- Prove2me | Definitions.Def_SourceProof_09a1d2ad90db017031836da3
-- name    : SourceProof_09a1d2ad90db017031836da3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:11:16.745003+00:00
-- url     : https://prove2.me/theorems/fe4e2674-a07e-475d-bb9c-e6dedafbb373
-- title:
--   LevyStochCalc source proof: MathFin.memLp_compensated
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_MathFin_Foundations_PoissonRandomMeasure_F000

open private hasSum_pw_compensated_sq pw from Definitions.Def_MathFin_Foundations_PoissonRandomMeasure_F000
/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/

/-!
# Poisson random measure and the compensated increment

A *Poisson random measure* `N` on the time-mark space `[0, ∞) × E` with σ-finite
mark-intensity `ν` is the driving object of Lévy-driven stochastic calculus: `N(·, B)`
is `Poisson`-distributed with mean `ν̂(B)` (`ν̂ := Leb[0,∞) ⊗ ν`), and counts on disjoint
regions are independent. The *compensated* measure `Ñ(B) := N(B) − ν̂(B)` is the mean-zero,
`L²` object one integrates against.

This module provides the object as a hypothesis-bundling structure (its fields are the
Applebaum Def. 2.3.1 properties) plus the two Poisson moment facts the isometry needs —
`𝔼[N(B)] = ν̂(B)` and `𝔼[N(B)²] = ν̂(B)² + ν̂(B)` — hence `𝔼[Ñ(B)] = 0`, `𝔼[Ñ(B)²] = ν̂(B)`.

Mathlib carries the Poisson law (`poissonMeasure`, `integral_poissonMeasure`)
but *not* its mean or variance; we derive them here from the total-mass identity by a single
index shift (`(n+1)·pmf(n+1) = r·pmf(n)`), with no exp-series differentiation.

## Provenance

The `PoissonRandomMeasure` structure's field shape is consulted from
`cgarryZA/LevyStochCalc` (Apache-2.0), itself a faithful rendering of Applebaum Def. 2.3.1;
the isometry developed on top (see `PoissonCompensatedIsometryAdapted` / `…IntegralL2`) is our
own — LevyStochCalc states that isometry as its cited axiom #6, we prove it. References:
Applebaum, *Lévy Processes and Stochastic Calculus*, CUP 2009, Def. 2.3.1 / Thm 4.2.3.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-! ## §1  Moments of the scalar Poisson law (Mathlib gap-fill) -/

/-! ## §2  The Poisson random measure and its compensated increment -/

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]

/-! ### Compensated-increment moments (transport of the scalar moments through `poisson_law`) -/

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]


theorem _root_.Prove2MeSourceProof.h_09a1d2ad90db017031836da3 (N : PoissonRandomMeasure P ν) {D : Set (ℝ × E)}
    (hD : MeasurableSet D) (hfin : referenceIntensity ν D ≠ ⊤) :
    MemLp (N.compensated D) 2 P := by
  refine (memLp_two_iff_integrable_sq (N.measurable_compensated hD).aestronglyMeasurable).mpr ?_
  have hrw : (fun ω => (N.compensated D ω) ^ 2)
      = (fun x : ℝ≥0∞ => (x.toReal - (MathFin.referenceIntensity ν D).toReal) ^ 2) ∘ (fun ω => N.N ω D) := rfl
  rw [hrw, ← integrable_map_measure (by fun_prop) (N.measurable_eval hD).aemeasurable,
      N.poisson_law hD hfin, MathFin.poissonMeasureENN,
      integrable_map_measure (by fun_prop) (Measurable.aemeasurable (by fun_prop)),
      integrable_poissonMeasure_iff]
  refine ((hasSum_pw_compensated_sq (MathFin.referenceIntensity ν D).toNNReal).summable).congr fun n => ?_
  simp only [Function.comp_apply, ENNReal.toReal_natCast, Real.norm_eq_abs]
  rw [abs_of_nonneg (sq_nonneg _)]
  rfl
end MathFin


