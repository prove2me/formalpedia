-- Prove2me | Definitions.Def_SourceProof_de8d25ca7f6416d3fea11e45
-- name    : SourceProof_de8d25ca7f6416d3fea11e45
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:55:03.03115+00:00
-- url     : https://prove2.me/theorems/32fc8530-3378-4e6e-a4d2-1dfc4e6a5ffa
-- title:
--   LevyStochCalc source module: SourceProof_de8d25ca7f6416d3fea11e45
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stage_compensator_tendsto_L1` comes from the `LevyStochCalc.Poisson.CompensatedProcessQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcessQuadVar_F001
import Definitions.Def_SourceProof_3a9a7b2f6ff6766d4054af50
import Definitions.Def_SourceProof_6be12e51c788a72f4de041a3

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

theorem _root_.Prove2MeSourceProof.h_de8d25ca7f6416d3fea11e45 (t : ℝ) :
    Tendsto (fun n => eLpNorm (fun ω =>
      (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.compensator t ω
        - compensator ν φ t ω) 1 P) atTop (𝓝 0) := by
  rcases le_or_gt t 0 with ht | ht
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    symm
    rw [show (fun ω => (LevyStochCalc.Poisson.Compensated.MarkStep.compensator (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2) t ω
        - LevyStochCalc.Poisson.Compensated.compensator ν φ t ω) = (0 : Ω → ℝ) from by
      funext ω
      rw [LevyStochCalc.Poisson.Compensated.MarkStep.compensator_of_nonpos _ ht, LevyStochCalc.Poisson.Compensated.compensator_of_nonpos ν φ ht]
      simp]
    exact eLpNorm_zero
  · have hgmem := LevyStochCalc.Poisson.Compensated.memLp_phi_horizon φ h_meas h_sq_int_global ht
    have hjoint : Tendsto (fun n => eLpNorm (fun p : Ω × ℝ × E =>
        (LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n p) ^ 2 - (φ p.1 p.2.1 p.2.2) ^ 2) 1
        (LevyStochCalc.Poisson.Compensated.horizonMeasure ν P t)) atTop (𝓝 0) :=
      _root_.Prove2MeSourceProof.h_6be12e51c788a72f4de041a3
        (fun n => (LevyStochCalc.Poisson.Compensated.measurable_stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n).aemeasurable)
        h_meas.aemeasurable hgmem.2.ne (_root_.Prove2MeSourceProof.h_3a9a7b2f6ff6766d4054af50 N ℱ φ h_meas h_progMeas
          h_sq_int_global t)
    have hmarg : ∀ n, eLpNorm (fun ω =>
        (LevyStochCalc.Poisson.Compensated.MarkStep.compensator (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2) t ω
          - LevyStochCalc.Poisson.Compensated.compensator ν φ t ω) 1 P
        ≤ eLpNorm (fun p : Ω × ℝ × E =>
          (LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n p) ^ 2 - (φ p.1 p.2.1 p.2.2) ^
            2) 1
          (LevyStochCalc.Poisson.Compensated.horizonMeasure ν P t) := by
      intro n
      have hGsq : Integrable (fun p : Ω × ℝ × E =>
          (LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n p) ^ 2) (LevyStochCalc.Poisson.Compensated.horizonMeasure ν P t) :=
        (LevyStochCalc.Poisson.Compensated.memLp_stageEval N ℱ hℱ φ h_meas h_progMeas h_sq_int_global n ht.le).integrable_sq
      have hgsq : Integrable (fun p : Ω × ℝ × E => (φ p.1 p.2.1 p.2.2) ^ 2)
          (LevyStochCalc.Poisson.Compensated.horizonMeasure ν P t) := hgmem.integrable_sq
      have hd : Integrable (fun p : Ω × ℝ × E =>
          (LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n p) ^ 2 - (φ p.1 p.2.1 p.2.2) ^ 2)
          (LevyStochCalc.Poisson.Compensated.horizonMeasure ν P t) := hGsq.sub hgsq
      rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm,
        lintegral_prod _ hd.aestronglyMeasurable.enorm]
      refine lintegral_mono_ae ?_
      filter_upwards [hGsq.prod_right_ae, hgsq.prod_right_ae] with ω hGω hgω
      have hcomb : (LevyStochCalc.Poisson.Compensated.MarkStep.compensator (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2) t ω
          - LevyStochCalc.Poisson.Compensated.compensator ν φ t ω
          = ∫ y, ((LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n (ω, y)) ^ 2
              - (φ ω y.1 y.2) ^ 2) ∂((volume.restrict (Set.Icc (0 : ℝ) t)).prod ν) := by
        rw [integral_sub hGω hgω, integral_prod _ hGω, integral_prod _ hgω]
        rfl
      rw [hcomb]
      exact enorm_integral_le_lintegral_enorm _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hjoint
      (Eventually.of_forall fun n => bot_le) (Eventually.of_forall hmarg)
end LevyStochCalc.Poisson.Compensated


