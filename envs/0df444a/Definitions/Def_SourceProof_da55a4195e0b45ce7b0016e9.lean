-- Prove2me | Definitions.Def_SourceProof_da55a4195e0b45ce7b0016e9
-- name    : SourceProof_da55a4195e0b45ce7b0016e9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:25:49.776961+00:00
-- url     : https://prove2.me/theorems/0e260913-e4e8-48dc-b76b-41213a03dbc7
-- title:
--   LevyStochCalc source module: SourceProof_da55a4195e0b45ce7b0016e9
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.integral_stochasticIntegral_mul_compensated_eq_zero` comes from the `LevyStochCalc.Driver.CrossOrthogonality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionApi_F002
import Definitions.Def_SourceProof_17d129a5f040a8f2ef70238f
import Definitions.Def_SourceProof_2554b195ead815ae5442020c
import Definitions.Def_SourceProof_c2c9076a38412c13902a9f97
import Definitions.Def_SourceProof_f13a945dd65a666877de115a

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Brownian and compensated ranges are orthogonal

Both integrals are `L²` limits of elementary ones — the Brownian integral of the master
approximants, the compensated integral of the mark-step stages — and the elementary pairings all
vanish, so the pairing of the limits vanishes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}


theorem _root_.Prove2MeSourceProof.h_da55a4195e0b45ce7b0016e9 (𝒲 : CrossWitness D ℱ) {i : Fin d}
    (hℱW : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
    (hℱN : Poisson.IsPoissonFiltration D.N ℱ)
    {H : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {φ : Ω → ℝ → E → ℝ} (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hφs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, Brownian.Ito.stochasticIntegral (D.W.W i) ℱ (hℱW i) H hHm hHp hHs t ω
      * Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs t ω ∂P = 0 := by
  have hu : MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W i) ℱ (hℱW i) H hHm hHp hHs t) 2 P :=
    (MeasureTheory.Lp.memLp _).ae_eq (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq (D.W.W i)
      ℱ (hℱW i) H hHm hHp hHs t).symm
  have hv : MemLp (LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs t) 2 P :=
    (LevyStochCalc.Poisson.Compensated.process_memLp D.N ℱ hℱN φ hφm hφp hφs t).ae_eq
      (LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process D.N ℱ hℱN φ hφm hφp hφs t).symm
  have hcv : Tendsto (fun n => eLpNorm (fun ω =>
      LevyStochCalc.Poisson.Compensated.stageIntegral D.N ℱ φ hφm hφp hφs n t ω
        - LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs t ω) 2 P)
      atTop (nhds 0) := by
    refine Tendsto.congr (fun n => ?_)
      (_root_.Prove2MeSourceProof.h_d924d3c21257fe582c3c4d51 D.N ℱ hℱN φ hφm hφp hφs t)
    refine eLpNorm_congr_ae ?_
    filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process D.N ℱ hℱN φ hφm hφp
      hφs t] with ω hω
    rw [hω]
  exact _root_.Prove2MeSourceProof.h_17d129a5f040a8f2ef70238f
    (un := fun n ω => LevyStochCalc.Brownian.Ito.simpleIntegral (D.W.W i)
      (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hHm hHp hHs n) t ω)
    (vn := fun n ω => LevyStochCalc.Poisson.Compensated.stageIntegral D.N ℱ φ hφm hφp hφs n t ω)
    hu hv (fun _ => _root_.Prove2MeSourceProof.h_f13a945dd65a666877de115a _ _ t)
    (fun n => LevyStochCalc.Poisson.Compensated.memLp_stageIntegral D.N ℱ φ hφm hφp hφs n t)
    (fun n => _root_.Prove2MeSourceProof.h_c2c9076a38412c13902a9f97 𝒲
      (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hHm hHp hHs n)
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H hHm hHp hHs n)
      (LevyStochCalc.Poisson.Compensated.master D.N ℱ φ hφm hφp hφs n).2
      (LevyStochCalc.Poisson.Compensated.master_adapted D.N ℱ φ hφm hφp hφs n) t t)
    (_root_.Prove2MeSourceProof.h_2554b195ead815ae5442020c (D.W.W i) ℱ (hℱW i) H hHm hHp hHs ht) hcv
end LevyDriver

end LevyStochCalc.Driver


