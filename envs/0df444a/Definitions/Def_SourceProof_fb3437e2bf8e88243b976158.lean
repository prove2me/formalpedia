-- Prove2me | Definitions.Def_SourceProof_fb3437e2bf8e88243b976158
-- name    : SourceProof_fb3437e2bf8e88243b976158
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:00:49.259599+00:00
-- url     : https://prove2.me/theorems/3f13f3b1-75c7-494a-af91-b19d0f5b96b3
-- title:
--   LevyStochCalc source module: SourceProof_fb3437e2bf8e88243b976158
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.martingale_rightCont_quadVar_process` comes from the `LevyStochCalc.Poisson.CompensatedProcessQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_43431ba791bbf2e5196768af
import Definitions.Def_SourceProof_5095b5211df9eef5b8388a53

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic-variation martingale of the compensated integral process

The compensated square `t ↦ F_t² − ∫_0^t ∫_E φ(u, e)² ν(de) du` of the `L²` integral process
`F` is a martingale on the filtration `ℱ` of the integral and on its right-continuation `ℱ₊`,
`ℱ₊ t = ⨅ s > t, ℱ s` (no null sets are added). The stage compensated squares are martingales
(`MarkStep.martingale_sq_sub_compensator`) and converge in `L¹` to the compensated square of the
process: the stage integrands converge to `φ` in `L²` of the product measure on
`Ω × [0, t] × E`, so their squares converge in `L¹`, and the `L¹(P)`-distance of the compensators
is dominated by the joint `L¹`-distance.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Compensator

variable (ν : Measure E) (φ : Ω → ℝ → E → ℝ)

end Compensator

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_fb3437e2bf8e88243b976158 :
    Martingale (fun t ω => (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2
      - compensator ν φ t ω) ℱ.rightCont P := by
  refine _root_.Prove2MeSourceProof.h_35156ff6984aa5b4b399bdef
    (_root_.Prove2MeSourceProof.h_43431ba791bbf2e5196768af N ℱ hℱ φ h_meas h_progMeas h_sq_int_global) fun s => ?_
  have hF2 : Tendsto (fun r => eLpNorm (fun ω =>
      (LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r ω) ^ 2
        - (LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s ω) ^ 2) 1 P) (𝓝[>] s) (𝓝 0) :=
    _root_.Prove2MeSourceProof.h_6be12e51c788a72f4de041a3 (l := 𝓝[>] s)
      (a := fun r => LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r)
      (b := LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s)
      (fun r => (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global
        r).aestronglyMeasurable.aemeasurable)
      (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s).aestronglyMeasurable.aemeasurable
      (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s).eLpNorm_ne_top
      (_root_.Prove2MeSourceProof.h_95e247e701da3178181c6103 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s)
  have hA := _root_.Prove2MeSourceProof.h_5095b5211df9eef5b8388a53 φ h_meas h_sq_int_global s
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hF2.add hA)
    (Eventually.of_forall fun r => bot_le) (Eventually.of_forall fun r => ?_)
  have hF2aesm : AEStronglyMeasurable (fun ω =>
      (LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r ω) ^ 2
        - (LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s ω) ^ 2) P :=
    (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global
      r).integrable_sq.aestronglyMeasurable.sub
      (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global
        s).integrable_sq.aestronglyMeasurable
  have hAaesm : AEStronglyMeasurable
      (fun ω => LevyStochCalc.Poisson.Compensated.compensator ν φ r ω - LevyStochCalc.Poisson.Compensated.compensator ν φ s ω) P :=
    (LevyStochCalc.Poisson.Compensated.integrable_compensator φ h_meas h_sq_int_global r).aestronglyMeasurable.sub
      (LevyStochCalc.Poisson.Compensated.integrable_compensator φ h_meas h_sq_int_global s).aestronglyMeasurable
  calc eLpNorm ((fun ω => (LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r ω) ^ 2
          - LevyStochCalc.Poisson.Compensated.compensator ν φ r ω)
        - fun ω => (LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s ω) ^ 2
          - LevyStochCalc.Poisson.Compensated.compensator ν φ s ω) 1 P
      = eLpNorm ((fun ω => (LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r ω) ^ 2
            - (LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s ω) ^ 2)
          - fun ω => LevyStochCalc.Poisson.Compensated.compensator ν φ r ω - LevyStochCalc.Poisson.Compensated.compensator ν φ s ω) 1 P := by
        refine eLpNorm_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [Pi.sub_apply]
        ring
    _ ≤ _ := eLpNorm_sub_le hF2aesm hAaesm le_rfl
end LevyStochCalc.Poisson.Compensated


