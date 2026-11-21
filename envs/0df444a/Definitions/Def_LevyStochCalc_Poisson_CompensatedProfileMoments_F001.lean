-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileMoments_F001
-- name    : LevyStochCalc_Poisson_CompensatedProfileMoments_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:01:21.49765+00:00
-- url     : https://prove2.me/theorems/02be05a9-01c9-4700-980c-d40b889d98e8
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProfileMoments
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProfileMoments. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfile_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfile_F002
import Definitions.Def_SourceProof_b99d59281a5160eb28e462a1

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

/-- **The second moment of a compensated profile integral.** The compensated integral of a
square-integrable mark profile over the step `(a, b]` has second moment the step length times the
squared `L²(ν)` norm of the profile. -/
theorem integral_compensatedProfile_sq (N : PoissonRandomMeasure P ν) {f : E → ℝ}
    (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProfile N f a b ω ^ 2 ∂P = (b - a) * ∫ e, f e ^ 2 ∂ν := by
  simp_rw [sq]
  exact _root_.Prove2MeSourceProof.h_b99d59281a5160eb28e462a1 N hf hf ha hab
end LevyStochCalc.Poisson


