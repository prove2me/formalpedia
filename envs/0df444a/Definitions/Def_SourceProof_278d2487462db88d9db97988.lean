-- Prove2me | Definitions.Def_SourceProof_278d2487462db88d9db97988
-- name    : SourceProof_278d2487462db88d9db97988
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:15:47.779513+00:00
-- url     : https://prove2.me/theorems/95962b6b-c172-46db-b18c-966dfddfb182
-- title:
--   LevyStochCalc source module: SourceProof_278d2487462db88d9db97988
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.martingale_process` comes from the `LevyStochCalc.Poisson.CompensatedProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F001
import Definitions.Def_SourceProof_7f016bcc8755267478a0d8f9
import Definitions.Def_SourceProof_d924d3c21257fe582c3c4d51

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated-Poisson `L²` integral process

The process `t ↦ ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` is the `L²`-limit, at each time `t`, of the
compensated integrals of the master approximating sequence (`stageIntegral`). It is taken as
the `ℱ_t`-measurable representative of the `L²`-limit, so that it is adapted to the natural
filtration of the Poisson random measure; it is a square-integrable martingale, vanishes at
nonpositive times, and satisfies the Itô–Lévy isometry at every time.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

section Process

include hℱ in

theorem _root_.Prove2MeSourceProof.h_278d2487462db88d9db97988 :
    Martingale (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global) ℱ P := by
  refine _root_.Prove2MeSourceProof.h_7f016bcc8755267478a0d8f9
    (M := fun n t => LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t)
    (fun n => LevyStochCalc.Poisson.Compensated.martingale_stageIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global n)
    (fun n t => (LevyStochCalc.Poisson.Compensated.martingale_stageIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global n).integrable
      t)
    (LevyStochCalc.Poisson.Compensated.process_stronglyAdapted N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
    (fun t => (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).integrable (by norm_num))
    (fun t => ?_)
  refine LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_of_eLpNorm_two (fun n => ?_)
    (_root_.Prove2MeSourceProof.h_d924d3c21257fe582c3c4d51 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t)
  exact ((LevyStochCalc.Poisson.Compensated.memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t).sub
    (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t)).aestronglyMeasurable
end Process

section Isometry

end Isometry

end LevyStochCalc.Poisson.Compensated


