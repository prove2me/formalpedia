-- Prove2me | Definitions.Def_SourceProof_555e93e74cc0dd7d3e1f7b7a
-- name    : SourceProof_555e93e74cc0dd7d3e1f7b7a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T23:46:02.389206+00:00
-- url     : https://prove2.me/theorems/65903c53-62bb-44f0-a6af-bd1e85688cec
-- title:
--   LevyStochCalc source module: SourceProof_555e93e74cc0dd7d3e1f7b7a
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.compensated_inter_add_diff_ae` comes from the `LevyStochCalc.Poisson.CompensatedDensityStepIntegral` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F001

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


theorem _root_.Prove2MeSourceProof.h_555e93e74cc0dd7d3e1f7b7a
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B C : Set (ℝ × E)} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    (fun ω => N.compensated B ω)
      =ᵐ[P] (fun ω => N.compensated (B ∩ C) ω + N.compensated (B \ C) ω) := by
  filter_upwards [N.integer_valued hB hfin] with ω hω
  obtain ⟨n, hn⟩ := hω
  have hBfin : N.N ω B ≠ ⊤ := by rw [hn]; exact ENNReal.natCast_ne_top n
  have hint_ne : N.N ω (B ∩ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hBfin (measure_mono Set.inter_subset_left)
  have hdiff_ne : N.N ω (B \ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hBfin (measure_mono Set.sdiff_subset)
  have hrefint : LevyStochCalc.Poisson.referenceIntensity ν (B ∩ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have hrefdiff : LevyStochCalc.Poisson.referenceIntensity ν (B \ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.sdiff_subset)
  simp only [LevyStochCalc.Poisson.PoissonRandomMeasure.compensated]
  rw [show N.N ω B = N.N ω (B ∩ C) + N.N ω (B \ C) from
        (measure_inter_add_sdiff (μ := N.N ω) B hC).symm,
      show LevyStochCalc.Poisson.referenceIntensity ν B
          = LevyStochCalc.Poisson.referenceIntensity ν (B ∩ C)
            + LevyStochCalc.Poisson.referenceIntensity ν (B \ C) from
        (measure_inter_add_sdiff (μ := LevyStochCalc.Poisson.referenceIntensity ν) B hC).symm,
      ENNReal.toReal_add hint_ne hdiff_ne, ENNReal.toReal_add hrefint hrefdiff]
  ring
end LevyStochCalc.Poisson.Compensated


