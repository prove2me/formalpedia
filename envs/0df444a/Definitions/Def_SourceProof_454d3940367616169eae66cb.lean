-- Prove2me | Definitions.Def_SourceProof_454d3940367616169eae66cb
-- name    : SourceProof_454d3940367616169eae66cb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:26:41.637587+00:00
-- url     : https://prove2.me/theorems/3408be7f-0a22-4067-a3dc-7ad03f2e442f
-- title:
--   LevyStochCalc source module: SourceProof_454d3940367616169eae66cb
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mean_zero` comes from the `LevyStochCalc.Poisson.CompensatedRange` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The range of the compensated Poisson integral on a horizon

A marked integrand supported in `[0, T]`, jointly and progressively measurable and of finite
energy, is admissible for the compensated integral up to `T`. Such integrands are closed under
sums and scalar multiples, and the integral is additive and homogeneous on them, so their
integrals form a submodule of `L²`. The isometry of differences carries an energy-Cauchy sequence
of integrands to an `L²`-Cauchy sequence of integrals, so that submodule is closed.
-/

namespace LevyStochCalc.Poisson.Compensated

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Progressive

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Progressive

namespace MarkedHorizonIntegrand

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

section Integral

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)


theorem _root_.Prove2MeSourceProof.h_454d3940367616169eae66cb (hT : 0 ≤ T) (G : MarkedHorizonIntegrand P ν ℱ T) :
    ∫ ω, G.integral N hℱ ω ∂P = 0 := by
  obtain ⟨F, hF⟩ := LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral N ℱ hℱ G.toFun G.measurable_uncurry
    G.progressive G.sq_int_global
  haveI : SigmaFinite (P.trim (F.le 0)) := (isFiniteMeasure_trim (F.le 0)).toSigmaFinite
  have hcond := hF.2 0 T hT
  have hz : LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
      G.sq_int_global 0 =ᵐ[P] 0 :=
    (LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
      G.sq_int_global 0).trans
      (_root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
        G.sq_int_global le_rfl)
  calc ∫ ω, G.integral N hℱ ω ∂P
      = ∫ ω, condExp (F 0) P (fun x => LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ G.toFun
          G.measurable_uncurry G.progressive G.sq_int_global T x) ω ∂P :=
        (integral_condExp (F.le 0)).symm
    _ = ∫ ω, LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
          G.sq_int_global 0 ω ∂P := integral_congr_ae hcond
    _ = 0 := by rw [integral_congr_ae hz]; simp
end Integral

end MarkedHorizonIntegrand

section Range

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Range

section Representation

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Representation

end LevyStochCalc.Poisson.Compensated


