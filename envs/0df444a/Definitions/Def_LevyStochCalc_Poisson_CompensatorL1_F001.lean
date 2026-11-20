-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F001
-- name    : LevyStochCalc_Poisson_CompensatorL1_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:14:45.873366+00:00
-- url     : https://prove2.me/theorems/95e384fa-4c01-448c-8492-ba4c0e8f0238
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatorL1
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatorL1. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Compensator_F000
import Definitions.Def_LevyStochCalc_Poisson_Compensator_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From energy to the mean pathwise integral

The compensator identity turns the mean of the absolute integral against the random measure into
the mean against the reference intensity, and on a window of finite intensity the latter is
controlled by the energy through the comparison of `L¹` with `L²`. So an energy-null sequence of
predictable marked integrands has pathwise compensated integrals tending to zero in mean.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Bound

variable {A : Set E} {T : ℝ}

/-- On a probability space the mean size is at most the root mean square. -/
theorem lintegral_enorm_le_eLpNorm_two {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) :
    ∫⁻ ω, ‖f ω‖ₑ ∂P ≤ eLpNorm f 2 P := by
  have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := P) (f := f)
    (p := 1) (q := 2) (by norm_num) hf
  rwa [eLpNorm_one_eq_lintegral_enorm, measure_univ, ENNReal.one_rpow, mul_one] at hcmp
omit [IsProbabilityMeasure P] in
/-- The `L²` seminorm as the square root of the mean square. -/
theorem eLpNorm_two_eq_rpow (f : Ω → ℝ) :
    eLpNorm f 2 P = (∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P) ^ (2 : ℝ)⁻¹ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num
end Bound

section Pathwise

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {A : Set E} {T : ℝ}

end Pathwise

end LevyStochCalc.Poisson


