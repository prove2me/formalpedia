-- Prove2me | Definitions.Def_SourceProof_cc04f7a83f7e31f30eccd6e0
-- name    : SourceProof_cc04f7a83f7e31f30eccd6e0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:47:16.693176+00:00
-- url     : https://prove2.me/theorems/e3b3bdde-9df5-4f86-b076-1dceccafaf20
-- title:
--   LevyStochCalc source module: SourceProof_cc04f7a83f7e31f30eccd6e0
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.integral_mul_integral_eq_zero` comes from the `LevyStochCalc.Poisson.PerpBridge` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PerpBridge_F000
import Definitions.Def_SourceProof_ebffe457c2736bba9661d0fd

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The perp bridge for the compensated integral

A weight measurable before a horizon does not see the compensated integral beyond it: the
increment is a martingale increment, and conditioning on the horizon kills it. So orthogonality
to every admissible integrand over `[0, T]` extends to every admissible integrand over any
larger horizon. This is the marked counterpart of the Brownian perp bridge.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Congr

end Congr

section Clip

namespace MarkedHorizonIntegrand

end MarkedHorizonIntegrand

end Clip

section Bridge


theorem _root_.Prove2MeSourceProof.h_cc04f7a83f7e31f30eccd6e0 (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) {z : Ω → ℝ} (hz2 : MemLp z 2 P)
    (hzm : AEStronglyMeasurable[ℱ T] z P)
    (hperp : ∀ G : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, z ω * G.integral N hℱ ω ∂P = 0)
    {R : ℝ} (hTR : T ≤ R) (G : MarkedHorizonIntegrand P ν ℱ R) :
    ∫ ω, z ω * G.integral N hℱ ω ∂P = 0 := by
  set M := LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
    G.sq_int_global with hMdef
  have hMLp : ∀ u : ℝ, MemLp (M u) 2 P := fun u =>
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
      G.sq_int_global u
  have hclipzero : ∫ ω, z ω * M T ω ∂P = 0 := by
    have h := hperp (G.clip hTR)
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_clip N hℱ G hT hTR] with ω e
    rw [e]
  have hincr := _root_.Prove2MeSourceProof.h_ebffe457c2736bba9661d0fd N hℱ G.toFun G.measurable_uncurry G.progressive
    G.sq_int_global hz2 hzm hTR
  have hint1 : Integrable (fun ω => z ω * M T ω) P :=
    LevyStochCalc.Poisson.Compensated.integrable_mul_of_memLp_two hz2 (hMLp T)
  have hint2 : Integrable (fun ω => z ω * (M R ω - M T ω)) P :=
    LevyStochCalc.Poisson.Compensated.integrable_mul_of_memLp_two hz2 ((hMLp R).sub (hMLp T))
  have hrw : (fun ω => z ω * M R ω)
      = fun ω => z ω * M T ω + z ω * (M R ω - M T ω) := by funext ω; ring
  change ∫ ω, z ω * M R ω ∂P = 0
  rw [show (∫ ω, z ω * M R ω ∂P)
      = ∫ ω, (z ω * M T ω + z ω * (M R ω - M T ω)) ∂P from by rw [hrw],
    integral_add hint1 hint2, hclipzero, hincr, add_zero]
end Bridge

end LevyStochCalc.Poisson.Compensated


