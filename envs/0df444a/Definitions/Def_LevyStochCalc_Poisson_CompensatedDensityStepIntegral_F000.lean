-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F000
-- name    : LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:47:54.397588+00:00
-- url     : https://prove2.me/theorems/09e3f492-8270-4326-ac81-5ec7b21d58be
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityStepIntegral
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityStepIntegral. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F004
import Definitions.Def_SourceProof_0186e3855af2ce949447917f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Step (finite-sum) predictable integrands

The compensated integral of a finite family of simple predictable integrands, its martingale
property and square-integrability on the natural filtration, together with the covariance
identities for compensated masses of disjoint and of nested space-time sets that underlie the
`L²` isometry.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Step (finite-sum) predictable integrands

The mark-discretised approximant is rank-`>1` in the mark, so it is a finite
`ℝ`-combination of `SimplePredictable` pieces rather than a single one. Its
compensated integral is the sum of the pieces' integrals, and (being a sum of the
per-piece martingales) it is again a martingale on the natural filtration. -/

/-- The compensated integral of a **finite family** of simple predictable
integrands: `∑ⱼ ∫ φⱼ dÑ`. -/
noncomputable def stepIntegral
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} {k : ℕ} (Φ : Fin k → SimplePredictable Ω E ν T) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ j, simpleIntegral N (Φ j) t ω
/-- The step integral vanishes at time `0` (each piece does). -/
lemma stepIntegral_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} {k : ℕ} (Φ : Fin k → SimplePredictable Ω E ν T) (ω : Ω) :
    stepIntegral N Φ 0 ω = 0 := by
  simp [stepIntegral, _root_.Prove2MeSourceProof.h_0186e3855af2ce949447917f]
end LevyStochCalc.Poisson.Compensated


