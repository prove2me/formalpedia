-- Prove2me | Definitions.Def_LevyStochCalc_Driver_PredictableRepresentation_F000
-- name    : LevyStochCalc_Driver_PredictableRepresentation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:58:05.853793+00:00
-- url     : https://prove2.me/theorems/840155b5-4438-4e7a-8d99-5deb1bd324cc
-- title:
--   LevyStochCalc source module: LevyStochCalc.Driver.PredictableRepresentation
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Driver.PredictableRepresentation in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PredictableIntegrand_F000
import Definitions.Def_LevyStochCalc_Driver_JointPRPDegenerate_F001
import Definitions.Def_LevyStochCalc_Poisson_PredictableIntegrand_F000
import Definitions.Def_SourceProof_a18e40e475a8a5104c3fe504
import Definitions.Def_SourceProof_a8da103e0afd15e51015e74e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint representation with predictable integrands

Each integrand of a joint representation can be replaced by a predictable one with the same
integral, so a square-integrable weight of mean zero, measurable before the horizon, is a sum of
Itô integrals and a compensated integral of predictable integrands.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν]

namespace LevyDriver

open Brownian.Ito Brownian.Multidim.MultidimBrownianMotion Poisson.Compensated
open LevyStochCalc.Probability

/-- **The predictable representation property with predictable integrands.** -/
theorem exists_predictable_jointIntegral (D : LevyDriver.{u, v, w} P d ν) {T : ℝ} (hT : 0 < T)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin d, HorizonIntegrand P (Brownian.augFiltration D.filtration P) T)
      (K : MarkedHorizonIntegrand P ν (Brownian.augFiltration D.filtration P) T),
      (∀ i, Predictable (Brownian.augFiltration D.filtration P) (G i).toFun) ∧
        MarkedPredictable (Brownian.augFiltration D.filtration P) ν K.toFun ∧
        Z =ᵐ[P] jointIntegral (fun k => D.isBrownianFiltration_aug k)
          D.isPoissonFiltration_aug G K := by
  obtain ⟨G, K, hZ⟩ := exists_jointIntegral_augFiltration_of_mean_zero D hT hZ2 hZm hZ0
  choose G' hG'pred hG'int using fun i : Fin d => _root_.Prove2MeSourceProof.h_a18e40e475a8a5104c3fe504 (D.W.W i)
    (D.isBrownianFiltration_aug i) (fun _ ht => D.augFiltration_le_of_nonpos ht) hT (G i)
  obtain ⟨K', hK'pred, hK'int⟩ := _root_.Prove2MeSourceProof.h_a8da103e0afd15e51015e74e D.N
    D.isPoissonFiltration_aug hT K
  refine ⟨G', K', hG'pred, hK'pred, hZ.trans ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ i : Fin d,
      (G' i).integral (D.W.W i) (D.isBrownianFiltration_aug i) ω
        = (G i).integral (D.W.W i) (D.isBrownianFiltration_aug i) ω := ae_all_iff.mpr hG'int
  filter_upwards [hall, hK'int] with ω h1 h2
  change vectorIntegral D.W (fun k => D.isBrownianFiltration_aug k) G ω
      + K.integral D.N D.isPoissonFiltration_aug ω
    = vectorIntegral D.W (fun k => D.isBrownianFiltration_aug k) G' ω
      + K'.integral D.N D.isPoissonFiltration_aug ω
  rw [h2]
  exact congrArg (· + K.integral D.N D.isPoissonFiltration_aug ω)
    (Finset.sum_congr rfl fun i _ => (h1 i).symm)
end LevyDriver

end LevyStochCalc.Driver


