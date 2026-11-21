-- Prove2me | Definitions.Def_SourceProof_43431ba791bbf2e5196768af
-- name    : SourceProof_43431ba791bbf2e5196768af
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:57:27.113711+00:00
-- url     : https://prove2.me/theorems/686ee928-68b2-4e43-a95e-6f1ba1fccd1e
-- title:
--   LevyStochCalc source module: SourceProof_43431ba791bbf2e5196768af
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.martingale_quadVar_process` comes from the `LevyStochCalc.Poisson.CompensatedProcessQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcessQuadVar_F000
import Definitions.Def_SourceProof_6be12e51c788a72f4de041a3
import Definitions.Def_SourceProof_7f016bcc8755267478a0d8f9
import Definitions.Def_SourceProof_d924d3c21257fe582c3c4d51
import Definitions.Def_SourceProof_de8d25ca7f6416d3fea11e45

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

theorem _root_.Prove2MeSourceProof.h_43431ba791bbf2e5196768af :
    Martingale (fun t ω => (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2
      - compensator ν φ t ω) ℱ P := by
  refine _root_.Prove2MeSourceProof.h_7f016bcc8755267478a0d8f9
    (M := fun n t ω => (LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω) ^ 2
      - (LevyStochCalc.Poisson.Compensated.MarkStep.compensator (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2) t ω)
    (fun n => (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global
      n).2.martingale_sq_sub_compensator N hℱ
      (LevyStochCalc.Poisson.Compensated.master_adapted N ℱ φ h_meas h_progMeas h_sq_int_global n))
    (fun n t => ((LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global
      n).2.martingale_sq_sub_compensator N hℱ (LevyStochCalc.Poisson.Compensated.master_adapted N ℱ φ h_meas h_progMeas
        h_sq_int_global n)).integrable t)
    (fun t => ((LevyStochCalc.Poisson.Compensated.process_stronglyAdapted N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).pow 2).sub
      (LevyStochCalc.Poisson.Compensated.compensator_stronglyAdapted ℱ φ h_progMeas t))
    (fun t => (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).integrable_sq.sub
      (LevyStochCalc.Poisson.Compensated.integrable_compensator φ h_meas h_sq_int_global t))
    (fun t => ?_)
  have hX : Tendsto (fun n => eLpNorm (fun ω =>
      (LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω) ^ 2
        - (LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2) 1 P) atTop (𝓝 0) :=
    _root_.Prove2MeSourceProof.h_6be12e51c788a72f4de041a3
      (fun n => (LevyStochCalc.Poisson.Compensated.memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n
        t).aestronglyMeasurable.aemeasurable)
      (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).aestronglyMeasurable.aemeasurable
      (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).eLpNorm_ne_top
      (_root_.Prove2MeSourceProof.h_d924d3c21257fe582c3c4d51 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t)
  have hY := _root_.Prove2MeSourceProof.h_de8d25ca7f6416d3fea11e45 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hX.add hY)
    (Eventually.of_forall fun n => bot_le) (Eventually.of_forall fun n => ?_)
  have hXaesm : AEStronglyMeasurable (fun ω =>
      (LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω) ^ 2
        - (LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2) P :=
    (LevyStochCalc.Poisson.Compensated.memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n
      t).integrable_sq.aestronglyMeasurable.sub
      (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global
        t).integrable_sq.aestronglyMeasurable
  have hYaesm : AEStronglyMeasurable (fun ω =>
      (LevyStochCalc.Poisson.Compensated.MarkStep.compensator (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2) t ω
        - LevyStochCalc.Poisson.Compensated.compensator ν φ t ω) P :=
    ((LevyStochCalc.Poisson.Compensated.MarkStep.integrable_compensator (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2)
      t).aestronglyMeasurable.sub
      (LevyStochCalc.Poisson.Compensated.integrable_compensator φ h_meas h_sq_int_global t).aestronglyMeasurable
  calc eLpNorm ((fun ω => (LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω) ^ 2
          - (LevyStochCalc.Poisson.Compensated.MarkStep.compensator (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2) t ω)
        - fun ω => (LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2
          - LevyStochCalc.Poisson.Compensated.compensator ν φ t ω) 1 P
      = eLpNorm ((fun ω => (LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω) ^ 2
            - (LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2)
          - fun ω => (LevyStochCalc.Poisson.Compensated.MarkStep.compensator (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2) t ω
            - LevyStochCalc.Poisson.Compensated.compensator ν φ t ω) 1 P := by
        refine eLpNorm_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [Pi.sub_apply]
        ring
    _ ≤ _ := eLpNorm_sub_le hXaesm hYaesm le_rfl
end LevyStochCalc.Poisson.Compensated


