-- Prove2me | Definitions.Def_SourceProof_99ba0164ebb17461a6598da8
-- name    : SourceProof_99ba0164ebb17461a6598da8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:31:42.731843+00:00
-- url     : https://prove2.me/theorems/62e30c30-1351-4647-a5ba-a8c7348bedf0
-- title:
--   LevyStochCalc source module: SourceProof_99ba0164ebb17461a6598da8
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.compensated_cross_covariance` comes from the `LevyStochCalc.Poisson.CompensatedDensityStepIntegral` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F002
import Definitions.Def_SourceProof_555e93e74cc0dd7d3e1f7b7a

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


theorem _root_.Prove2MeSourceProof.h_99ba0164ebb17461a6598da8
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hfin' : LevyStochCalc.Poisson.referenceIntensity ν B' ≠ ⊤) :
    ∫ ω, N.compensated B ω * N.compensated B' ω ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B')).toReal := by
  set C := B \ B' with hCdef
  set D := B' \ B with hDdef
  have hCmeas : MeasurableSet C := hB.diff hB'
  have hDmeas : MeasurableSet D := hB'.diff hB
  have hdisj : Disjoint C D := disjoint_sdiff_sdiff
  have hCf : LevyStochCalc.Poisson.referenceIntensity ν C ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.sdiff_subset)
  have hDf : LevyStochCalc.Poisson.referenceIntensity ν D ≠ ⊤ :=
    ne_top_of_le_ne_top hfin' (measure_mono Set.sdiff_subset)
  have hrefint : LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B') ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  -- a.e. `Ñ(B) − Ñ(B') = Ñ(C) − Ñ(D)`.
  have hsub_ae : (fun ω => N.compensated B ω - N.compensated B' ω)
      =ᵐ[P] (fun ω => N.compensated C ω - N.compensated D ω) := by
    filter_upwards [_root_.Prove2MeSourceProof.h_555e93e74cc0dd7d3e1f7b7a N hB hB' hfin,
      _root_.Prove2MeSourceProof.h_555e93e74cc0dd7d3e1f7b7a N hB' hB hfin'] with ω h1 h2
    rw [h1, h2, Set.inter_comm B' B]; ring
  have hsq_ae : (fun ω => (N.compensated B ω - N.compensated B' ω) ^ 2)
      =ᵐ[P] (fun ω => (N.compensated C ω - N.compensated D ω) ^ 2) :=
    hsub_ae.mono (fun ω h => by
      change (N.compensated B ω - N.compensated B' ω) ^ 2
        = (N.compensated C ω - N.compensated D ω) ^ 2
      rw [show N.compensated B ω - N.compensated B' ω
            = N.compensated C ω - N.compensated D ω from h])
  have hsq_eq : ∫ ω, (N.compensated B ω - N.compensated B' ω) ^ 2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν C).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν D).toReal :=
    (MeasureTheory.integral_congr_ae hsq_ae).trans
      (LevyStochCalc.Poisson.Compensated.compensated_diff_sq_disjoint N hCmeas hDmeas hCf hDf hdisj)
  have hexp := LevyStochCalc.Poisson.Compensated.compensated_diff_sq_expand N hB hB' hfin hfin'
  -- intensity inclusion–exclusion (in `toReal`).
  have hrefB : (LevyStochCalc.Poisson.referenceIntensity ν B).toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B')).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν C).toReal := by
    rw [show LevyStochCalc.Poisson.referenceIntensity ν B
          = LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B')
            + LevyStochCalc.Poisson.referenceIntensity ν C from
        (measure_inter_add_sdiff (μ := LevyStochCalc.Poisson.referenceIntensity ν) B hB').symm,
      ENNReal.toReal_add hrefint hCf]
  have hrefB' : (LevyStochCalc.Poisson.referenceIntensity ν B').toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B')).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν D).toReal := by
    rw [show LevyStochCalc.Poisson.referenceIntensity ν B'
          = LevyStochCalc.Poisson.referenceIntensity ν (B' ∩ B)
            + LevyStochCalc.Poisson.referenceIntensity ν D from
        (measure_inter_add_sdiff (μ := LevyStochCalc.Poisson.referenceIntensity ν) B' hB).symm,
      Set.inter_comm B' B, ENNReal.toReal_add hrefint hDf]
  rw [hexp] at hsq_eq
  linarith [hsq_eq, hrefB, hrefB']
end LevyStochCalc.Poisson.Compensated


