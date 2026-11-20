-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F002
-- name    : LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:51:54.108188+00:00
-- url     : https://prove2.me/theorems/dca15f73-aea4-4097-bad3-b7ab200285ba
-- title:
--   LevyStochCalc source module: LevyStochCalc.Poisson.CompensatedDensityStepIntegral
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Poisson.CompensatedDensityStepIntegral in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F001
import Definitions.Def_SourceProof_839c3c586f330ad57afd5326
import Definitions.Def_SourceProof_b329aafcf3facb3fc4e13667
import Definitions.Def_SourceProof_e0e24eaf49ef31dab57f4745

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

/-- **Polarisation expansion** of the squared difference: for measurable `B, B'`
with finite intensity, `E[(Ñ(B) − Ñ(B'))²] = ν̂(B).toReal − 2·E[Ñ(B)Ñ(B')] + ν̂(B').toReal`
(squares via `compensated_second_moment`, cross term left symbolic). -/
lemma compensated_diff_sq_expand
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hfin' : LevyStochCalc.Poisson.referenceIntensity ν B' ≠ ⊤) :
    ∫ ω, (N.compensated B ω - N.compensated B' ω) ^ 2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν B).toReal
        - 2 * (∫ ω, N.compensated B ω * N.compensated B' ω ∂P)
        + (LevyStochCalc.Poisson.referenceIntensity ν B').toReal := by
  have hBsq := _root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N hB hfin
  have hB'sq := _root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N hB' hfin'
  have hBB' := _root_.Prove2MeSourceProof.h_839c3c586f330ad57afd5326 N hB hB' hfin hfin'
  have h2 : MeasureTheory.Integrable
      (fun ω => 2 * (N.compensated B ω * N.compensated B' ω)) P := hBB'.const_mul 2
  have hmid : MeasureTheory.Integrable
      (fun ω => (N.compensated B ω) ^ 2 - 2 * (N.compensated B ω * N.compensated B' ω)) P :=
    hBsq.sub h2
  have hpt : (fun ω => (N.compensated B ω - N.compensated B' ω) ^ 2)
      = (fun ω => (N.compensated B ω) ^ 2
          - 2 * (N.compensated B ω * N.compensated B' ω) + (N.compensated B' ω) ^ 2) := by
    funext ω; ring
  rw [hpt, MeasureTheory.integral_add hmid hB'sq,
    MeasureTheory.integral_sub hBsq h2, MeasureTheory.integral_const_mul,
    _root_.Prove2MeSourceProof.h_b329aafcf3facb3fc4e13667 N hB hfin, _root_.Prove2MeSourceProof.h_b329aafcf3facb3fc4e13667 N hB' hfin']
end LevyStochCalc.Poisson.Compensated


