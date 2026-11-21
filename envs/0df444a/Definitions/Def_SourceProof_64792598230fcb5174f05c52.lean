-- Prove2me | Definitions.Def_SourceProof_64792598230fcb5174f05c52
-- name    : SourceProof_64792598230fcb5174f05c52
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:48:40.671393+00:00
-- url     : https://prove2.me/theorems/4eee1b41-9676-4372-965d-cc48dcc34933
-- title:
--   LevyStochCalc source module: SourceProof_64792598230fcb5174f05c52
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_augFiltration` comes from the `LevyStochCalc.Driver.JointPRP` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointComplement_F000
import Definitions.Def_LevyStochCalc_Driver_JointRange_F000
import Definitions.Def_SourceProof_2c7e12aa2978722bb6724897
import Definitions.Def_SourceProof_8f9f280f81d8e75768b9aa58
import Definitions.Def_SourceProof_e552f76f67c7e2f43cdc6a09

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The predictable representation property of a Lévy driver

Over the augmented joint filtration, a square-integrable weight of mean zero that is measurable
before the horizon is the sum of Itô integrals against the Brownian coordinates and a compensated
integral against the Poisson random measure: the joint range is closed, the orthogonal remainder
is a weight of the same kind orthogonal to both ranges, and such a weight vanishes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν]

namespace LevyDriver

open Brownian.Ito Brownian.Multidim.MultidimBrownianMotion Poisson.Compensated


theorem _root_.Prove2MeSourceProof.h_64792598230fcb5174f05c52 [Nonempty E] (D : LevyDriver.{u, v, w} P d ν)
    (hd : 0 < d) {T : ℝ} (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin d, HorizonIntegrand P (Brownian.augFiltration D.filtration P) T)
      (K : MarkedHorizonIntegrand P ν (Brownian.augFiltration D.filtration P) T),
      Z =ᵐ[P] jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K := by
  refine _root_.Prove2MeSourceProof.h_8f9f280f81d8e75768b9aa58 (fun k => D.isBrownianFiltration_aug k)
    D.isPoissonFiltration_aug (LevyStochCalc.Driver.LevyDriver.crossWitness D).aug hT ?_ hZ2 hZm hZ0
  intro r hr2 hrm hr0 hrB hrN
  have hperp : ∀ i : Fin d, LevyStochCalc.Brownian.Ito.PerpItoIntegrals (D.W.W i) (LevyStochCalc.Brownian.augFiltration D.filtration P)
      (D.isBrownianFiltration_aug i) fun ω => ((r ω : ℝ) : ℂ) := by
    intro i
    refine ⟨fun K hm hp hq t ht => ?_⟩
    have hreal := _root_.Prove2MeSourceProof.h_e552f76f67c7e2f43cdc6a09 (D.W.W i)
      (D.isBrownianFiltration_aug i) hT hr2 hrm (hrB i) K hm hp hq ht
    have hcast : (fun ω => ((r ω : ℝ) : ℂ) * ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (D.W.W i)
          (LevyStochCalc.Brownian.augFiltration D.filtration P) (D.isBrownianFiltration_aug i)
          K hm hp hq t ω : ℝ) : ℂ))
        = fun ω => ((r ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (D.W.W i)
          (LevyStochCalc.Brownian.augFiltration D.filtration P) (D.isBrownianFiltration_aug i)
          K hm hp hq t ω : ℝ) : ℂ) := by
      funext ω
      rw [Complex.ofReal_mul]
    rw [hcast, integral_complex_ofReal, hreal, Complex.ofReal_zero]
  exact _root_.Prove2MeSourceProof.h_2c7e12aa2978722bb6724897 D hd hT hr2 hrm hperp hrN hr0
end LevyDriver

end LevyStochCalc.Driver


