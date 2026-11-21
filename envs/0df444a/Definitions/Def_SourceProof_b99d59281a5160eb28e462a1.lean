-- Prove2me | Definitions.Def_SourceProof_b99d59281a5160eb28e462a1
-- name    : SourceProof_b99d59281a5160eb28e462a1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:00:23.243653+00:00
-- url     : https://prove2.me/theorems/24765ff8-11a0-429d-860b-6874f64b4c5d
-- title:
--   LevyStochCalc source module: SourceProof_b99d59281a5160eb28e462a1
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.integral_compensatedProfile_mul` comes from the `LevyStochCalc.Poisson.CompensatedProfileMoments` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileMoments_F000

open private tendsto_integral_mul_of_tendsto_L2 from Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileMoments_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# First and second moments of the compensated integral of a mark profile

The compensated integral of a simple mark profile over a step is a linear combination of
compensated counts, each of mean zero, and the `L²(P)` pairing of two such integrals over a
common step is the step length times the `L²(ν)` pairing of their mark functions. Both
identities pass to the `L²` limits that define the compensated integral of a square-integrable
mark profile: over the step `(a, b]` the mean of `J(f)` vanishes and

  `E[J(f) J(g)] = (b − a) ∫ f g dν`,   `E[J(f)²] = (b − a) ∫ f² dν`.

## Main statements

* `LevyStochCalc.Poisson.SimpleProfile.integral_stepIntegral` — the mean of the compensated
  step integral of a simple mark profile.
* `LevyStochCalc.Poisson.integral_compensatedProfile` — the mean of the compensated integral of
  a square-integrable mark profile over a step.
* `LevyStochCalc.Poisson.integral_compensatedProfile_mul` — the `L²(P)` pairing of the
  compensated integrals of two square-integrable mark profiles over a common step.
* `LevyStochCalc.Poisson.integral_compensatedProfile_sq` — the second moment of the compensated
  integral of a square-integrable mark profile over a step.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Passing an `L²` pairing to the limit -/

/-! ### The mean -/

/-! ### The second moments -/


theorem _root_.Prove2MeSourceProof.h_b99d59281a5160eb28e462a1 (N : PoissonRandomMeasure P ν) {f g : E → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProfile N f a b ω * compensatedProfile N g a b ω ∂P
      = (b - a) * ∫ e, f e * g e ∂ν := by
  obtain ⟨G, hG⟩ := _root_.Prove2MeSourceProof.h_abfa6819f153687cc685dc62 hf
  obtain ⟨G', hG'⟩ := _root_.Prove2MeSourceProof.h_abfa6819f153687cc685dc62 hg
  have hP := tendsto_integral_mul_of_tendsto_L2
    (fun n => (G n).memLp_stepIntegral N ha b) (fun n => (G' n).memLp_stepIntegral N ha b)
    (LevyStochCalc.Poisson.memLp_compensatedProfile N f a b) (LevyStochCalc.Poisson.memLp_compensatedProfile N g a b)
    (LevyStochCalc.Poisson.tendsto_stepIntegral_compensatedProfile N hf ha hab G hG)
    (LevyStochCalc.Poisson.tendsto_stepIntegral_compensatedProfile N hg ha hab G' hG')
  have hν := tendsto_integral_mul_of_tendsto_L2 (fun n => (G n).memLp_toFun)
    (fun n => (G' n).memLp_toFun) hf hg hG hG'
  refine tendsto_nhds_unique
    (hP.congr fun n => _root_.Prove2MeSourceProof.h_dc0655f17321fa2fa8890ee8 N (G n) (G' n) ha hab) ?_
  exact hν.const_mul (b - a)
end LevyStochCalc.Poisson


