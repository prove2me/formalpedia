-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDiff_F000
-- name    : LevyStochCalc_Poisson_CompensatedDiff_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:55:48.520175+00:00
-- url     : https://prove2.me/theorems/c7a04dd5-42f3-43e9-a67d-458155d7c74b
-- title:
--   LevyStochCalc source module: LevyStochCalc.Poisson.CompensatedDiff
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Poisson.CompensatedDiff in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcessQuadVar_F001
import Definitions.Def_SourceProof_c4dfabd4f14ab7a2037da138

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
/-- The difference isometry of the stage approximants of two integrands at every time. -/
lemma stageIntegral_sub_lintegral_sq {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ∫⁻ ω, (‖stageIntegral N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
        - stageIntegral N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ p, (‖stageEval N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n p
          - stageEval N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n p‖₊ : ℝ≥0∞) ^ 2
          ∂(horizonMeasure ν P t) := by
  have hA₁ := master_adapted N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n
  have hA₂ := master_adapted N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n
  have h₁ := le_max_left (master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).1
    (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).1
  have h₂ := le_max_right (master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).1
    (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).1
  have hiso := ((master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.dyadicRefine
    h₁).lintegral_integral_sub_sq_at N hℱ
    ((master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.dyadicRefine h₂) (hA₁.dyadicRefine N h₁)
    (hA₂.dyadicRefine N h₂) ht
  have hm : Measurable (fun p : Ω × ℝ × E =>
      (‖(master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.eval p.2.1 p.2.2 p.1
        - (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp
      ((master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.eval_measurable.sub
        (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.eval_measurable).nnnorm).pow_const 2
  have hL : ∫⁻ ω, (‖stageIntegral N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
        - stageIntegral N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖((master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.dyadicRefine h₁).integral N t ω
        - ((master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.dyadicRefine h₂).integral N t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [(fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_c4dfabd4f14ab7a2037da138 p2mMethodArg0 p2mMethodArg1 (master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2) N hℱ h₁
      hA₁ t,
      (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_c4dfabd4f14ab7a2037da138 p2mMethodArg0 p2mMethodArg1 (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2) N hℱ h₂ hA₂ t]
      with ω hω₁ hω₂
    simp only [stageIntegral]
    rw [hω₁, hω₂]
  rw [hL, hiso]
  unfold stageEval
  rw [lintegral_horizonMeasure t (fun ω s e =>
    (‖(master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.eval s e ω
      - (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hm]
  refine lintegral_congr fun ω => ?_
  rw [← lintegral_swap_es (fun ω s e =>
    (‖(master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.eval s e ω
      - (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hm ω]
  refine lintegral_congr fun e => setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  rw [(master N ℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.eval_dyadicRefine h₁,
    (master N ℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.eval_dyadicRefine h₂]
end LevyStochCalc.Poisson.Compensated


