-- Prove2me | Definitions.Def_SourceProof_a6d10632af938cae1bb46b89
-- name    : SourceProof_a6d10632af938cae1bb46b89
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:11:44.620185+00:00
-- url     : https://prove2.me/theorems/fab50a01-0957-41ed-a8bc-37fa8e9ecc17
-- title:
--   LevyStochCalc source module: SourceProof_a6d10632af938cae1bb46b89
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.martingale_stepIntegral_compensated` comes from the `LevyStochCalc.Poisson.CompensatedDensityStepIntegral` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F000
import Definitions.Def_SourceProof_ccdcfef1e11a997eb9caf4a9

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


theorem _root_.Prove2MeSourceProof.h_a6d10632af938cae1bb46b89
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} {k : ℕ} (Φ : Fin k → SimplePredictable Ω E ν T)
    (h_adapt : ∀ j : Fin k, ∀ i : Fin (Φ j).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((Φ j).partition i.castSucc))
        ((Φ j).ξ i)) :
    MeasureTheory.Martingale (fun t : ℝ => stepIntegral N Φ t)
      ℱ P := by
  have hfun : (fun t : ℝ => LevyStochCalc.Poisson.Compensated.stepIntegral N Φ t)
      = ∑ j : Fin k, (fun t : ℝ => LevyStochCalc.Poisson.Compensated.simpleIntegral N (Φ j) t) := by
    funext t ω
    simp only [LevyStochCalc.Poisson.Compensated.stepIntegral, Finset.sum_apply]
  rw [hfun]
  have hmart : ∀ s : Finset (Fin k),
      MeasureTheory.Martingale (∑ j ∈ s, fun t : ℝ => LevyStochCalc.Poisson.Compensated.simpleIntegral N (Φ j) t)
        ℱ P := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simp only [Finset.sum_empty]
        exact MeasureTheory.martingale_zero ℝ _ P
    | insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact (_root_.Prove2MeSourceProof.h_ccdcfef1e11a997eb9caf4a9 N ℱ hℱ (Φ j) (h_adapt j)).add ih
  exact hmart Finset.univ
end LevyStochCalc.Poisson.Compensated


