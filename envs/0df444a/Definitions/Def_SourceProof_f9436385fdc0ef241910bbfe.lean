-- Prove2me | Definitions.Def_SourceProof_f9436385fdc0ef241910bbfe
-- name    : SourceProof_f9436385fdc0ef241910bbfe
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:57:50.646284+00:00
-- url     : https://prove2.me/theorems/bb2ba1ee-4eef-4e2b-a0f0-d1b7a0925825
-- title:
--   LevyStochCalc source module: SourceProof_f9436385fdc0ef241910bbfe
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.process_sub_lintegral_sq` comes from the `LevyStochCalc.Poisson.CompensatedDiff` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDiff_F000
import Definitions.Def_SourceProof_3a9a7b2f6ff6766d4054af50
import Definitions.Def_SourceProof_711d7a58a27af1d1b25e8dc9
import Definitions.Def_SourceProof_d924d3c21257fe582c3c4d51

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The difference isometry of the compensated integral process

For two integrands `φ₁, φ₂`, the `L²` integral processes satisfy
`∫⁻ ‖F₁(t) − F₂(t)‖² = ∫⁻∫⁻_{[0,t]}∫⁻ ‖φ₁ − φ₂‖²`: the stage approximants of the two
integrands are refined to a common dyadic grid, where the difference isometry of mark-step
integrands holds at every time, and both sides pass to the limit in `L²`.
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
  (φ₁ φ₂ : Ω → ℝ → E → ℝ)
  (h_meas₁ : Measurable (fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2))
  (h_meas₂ : Measurable (fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2))
  (h_progMeas₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
  (h_progMeas₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
  (h_sq₁ : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (h_sq₂ : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_f9436385fdc0ef241910bbfe {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, (‖process N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω
        - process N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
          (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  have hI : Tendsto (fun n => eLpNorm
      ((fun ω => LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
        - LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω)
      - fun ω => LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω
        - LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω) 2 P) atTop (𝓝 0) := by
    have h₁ := _root_.Prove2MeSourceProof.h_d924d3c21257fe582c3c4d51 N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t
    have h₂ := _root_.Prove2MeSourceProof.h_d924d3c21257fe582c3c4d51 N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using h₁.add h₂) (Eventually.of_forall fun n => bot_le)
      (Eventually.of_forall fun n => ?_)
    calc eLpNorm ((fun ω => LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
            - LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω)
          - fun ω => LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω
            - LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω) 2 P
        = eLpNorm ((fun ω => LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
            - LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω)
          - fun ω => LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω
            - LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω) 2 P := by
          refine eLpNorm_congr_ae (Eventually.of_forall fun ω => ?_)
          simp only [Pi.sub_apply]
          ring
      _ ≤ _ := eLpNorm_sub_le
          ((LevyStochCalc.Poisson.Compensated.memLp_stageIntegral N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t).sub
            (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t)).aestronglyMeasurable
          ((LevyStochCalc.Poisson.Compensated.memLp_stageIntegral N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t).sub
            (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t)).aestronglyMeasurable (by
              norm_num)
  have hL := _root_.Prove2MeSourceProof.h_711d7a58a27af1d1b25e8dc9
    (gₙ := fun n ω => LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
      - LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω)
    (g := fun ω => LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω
      - LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω)
    (fun n => ((LevyStochCalc.Poisson.Compensated.memLp_stageIntegral N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t).sub
      (LevyStochCalc.Poisson.Compensated.memLp_stageIntegral N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t)).aestronglyMeasurable)
    ((LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t).sub
      (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t)).aestronglyMeasurable
    ((LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t).sub
      (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t)).eLpNorm_ne_top hI
  have hE : Tendsto (fun n => eLpNorm
      ((fun p => LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n p
        - LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n p)
      - fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 - φ₂ p.1 p.2.1 p.2.2) 2 (LevyStochCalc.Poisson.Compensated.horizonMeasure ν P t))
      atTop (𝓝 0) := by
    have h₁ := _root_.Prove2MeSourceProof.h_3a9a7b2f6ff6766d4054af50 N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t
    have h₂ := _root_.Prove2MeSourceProof.h_3a9a7b2f6ff6766d4054af50 N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using h₁.add h₂) (Eventually.of_forall fun n => bot_le)
      (Eventually.of_forall fun n => ?_)
    calc eLpNorm ((fun p => LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n p
            - LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n p)
          - fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 - φ₂ p.1 p.2.1 p.2.2) 2
          (LevyStochCalc.Poisson.Compensated.horizonMeasure ν P t)
        = eLpNorm ((LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n
            - fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
          - (LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n
            - fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)) 2 (LevyStochCalc.Poisson.Compensated.horizonMeasure ν P t) := by
          refine eLpNorm_congr_ae (Eventually.of_forall fun p => ?_)
          simp only [Pi.sub_apply]
          ring
      _ ≤ _ := eLpNorm_sub_le
          ((LevyStochCalc.Poisson.Compensated.measurable_stageEval N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).sub
            h_meas₁).aestronglyMeasurable
          ((LevyStochCalc.Poisson.Compensated.measurable_stageEval N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).sub
            h_meas₂).aestronglyMeasurable (by norm_num)
  have hR := _root_.Prove2MeSourceProof.h_711d7a58a27af1d1b25e8dc9
    (gₙ := fun n p => LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n p
      - LevyStochCalc.Poisson.Compensated.stageEval N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n p)
    (g := fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 - φ₂ p.1 p.2.1 p.2.2)
    (fun n => ((LevyStochCalc.Poisson.Compensated.measurable_stageEval N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).sub
      (LevyStochCalc.Poisson.Compensated.measurable_stageEval N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n)).aestronglyMeasurable)
    (h_meas₁.sub h_meas₂).aestronglyMeasurable
    ((LevyStochCalc.Poisson.Compensated.memLp_phi_horizon φ₁ h_meas₁ h_sq₁ ht).sub
      (LevyStochCalc.Poisson.Compensated.memLp_phi_horizon φ₂ h_meas₂ h_sq₂ ht)).eLpNorm_ne_top hE
  simp_rw [LevyStochCalc.Poisson.Compensated.stageIntegral_sub_lintegral_sq N ℱ hℱ φ₁ φ₂ h_meas₁ h_meas₂ h_progMeas₁ h_progMeas₂ h_sq₁
    h_sq₂ ht.le] at hL
  rw [tendsto_nhds_unique hL hR]
  exact LevyStochCalc.Poisson.Compensated.lintegral_horizonMeasure t (fun ω s e => (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2)
    ((ENNReal.continuous_coe.measurable.comp (h_meas₁.sub h_meas₂).nnnorm).pow_const 2)
end LevyStochCalc.Poisson.Compensated


