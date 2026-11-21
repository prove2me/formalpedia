-- Prove2me | Definitions.Def_SourceProof_a5a8473806f22ea94816f7db
-- name    : SourceProof_a5a8473806f22ea94816f7db
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:14:23.145038+00:00
-- url     : https://prove2.me/theorems/5bbdfd5d-d923-4b96-a3e8-69b2d88a5d52
-- title:
--   LevyStochCalc source module: SourceProof_a5a8473806f22ea94816f7db
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.tendsto_lintegral_restrictedStage_sub_pathwise` comes from the `LevyStochCalc.Poisson.PathwiseIdentity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PathwiseIdentity_F000
import Definitions.Def_SourceProof_6572ebe1e254a873e7002b18
import Definitions.Def_SourceProof_d5c50c508fc9a7910c8de4bf

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral of a predictable integrand is pathwise

The compensated integral is an `L²` limit of the integrals of mark-step approximants. For a
predictable integrand carried by a window of finite intensity the approximants can be taken
inside that window, where the reference intensity compensates the counts, so their pathwise forms
converge in mean to the pathwise form of the integrand while their integrals converge in `L²` to
the compensated integral. The two limits therefore agree.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Assembly

variable (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  {A : Set E} (hA : MeasurableSet A)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_a5a8473806f22ea94816f7db
    (hφpred : Probability.MarkedPredictable ℱ ν φ) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => ∫⁻ ω,
      ‖(restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n).integral N T ω
        - ((∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, φ ω q.1 q.2 ∂(N.N ω))
          - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, φ ω q.1 q.2 ∂(referenceIntensity ν))‖ₑ ∂P)
      atTop (𝓝 0) := by
  have hev : ∀ᶠ n : ℕ in atTop, T ≤ LevyStochCalc.Poisson.Compensated.stageHorizon n :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num)).eventually_ge_atTop T
  have hφen := LevyStochCalc.Poisson.Compensated.window_energy_ne_top φ h_meas h_sq (A := A) hT
  have hφint := _root_.Prove2MeSourceProof.h_6572ebe1e254a873e7002b18 N hℱ hA hAν T hφpred h_meas hφen
  have hbase : Tendsto (fun n => ∫⁻ ω,
      ‖(∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          LevyStochCalc.Poisson.Compensated.stageDefect N ℱ φ h_meas h_progMeas h_sq hA T n ω q.1 q.2 ∂(N.N ω))
        - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
            LevyStochCalc.Poisson.Compensated.stageDefect N ℱ φ h_meas h_progMeas h_sq hA T n ω q.1 q.2
            ∂(LevyStochCalc.Poisson.referenceIntensity ν)‖ₑ ∂P) atTop (𝓝 0) := by
    refine _root_.Prove2MeSourceProof.h_d5c50c508fc9a7910c8de4bf N hℱ hA hAν T
      (fun n => LevyStochCalc.Poisson.Compensated.markedPredictable_stageDefect N ℱ φ h_meas h_progMeas h_sq hA hφpred T n)
      (fun n => LevyStochCalc.Poisson.Compensated.measurable_stageDefect N ℱ φ h_meas h_progMeas h_sq hA T n) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (LevyStochCalc.Poisson.Compensated.tendsto_stageErr N ℱ φ h_meas h_progMeas h_sq)
      (Eventually.of_forall fun n => bot_le) ?_
    filter_upwards [hev] with n hn
    exact LevyStochCalc.Poisson.Compensated.window_energy_stageDefect_le N ℱ φ h_meas h_progMeas h_sq hA hsupp n hn
  refine hbase.congr' ?_
  filter_upwards [hev] with n hn
  refine lintegral_congr_ae ?_
  have hDint := _root_.Prove2MeSourceProof.h_6572ebe1e254a873e7002b18 N hℱ hA hAν T
    (LevyStochCalc.Poisson.Compensated.markedPredictable_stageDefect N ℱ φ h_meas h_progMeas h_sq hA hφpred T n)
    (LevyStochCalc.Poisson.Compensated.measurable_stageDefect N ℱ φ h_meas h_progMeas h_sq hA T n)
    (LevyStochCalc.Poisson.Compensated.window_energy_stageDefect_ne_top N ℱ φ h_meas h_progMeas h_sq hA hsupp n hn)
  filter_upwards [LevyStochCalc.Poisson.Compensated.ae_restrictedStage_integral_eq N ℱ φ h_meas h_progMeas h_sq hA n T,
    hφint, hDint] with ω hω hφω hDω
  have hsplit : ∀ μ : Measure (ℝ × E),
      IntegrableOn (fun q : ℝ × E =>
          LevyStochCalc.Poisson.Compensated.stageDefect N ℱ φ h_meas h_progMeas h_sq hA T n ω q.1 q.2)
        (Set.Ioc (0 : ℝ) T ×ˢ A) μ →
      IntegrableOn (fun q : ℝ × E => φ ω q.1 q.2) (Set.Ioc (0 : ℝ) T ×ˢ A) μ →
      (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, (Set.Iic T).indicator (fun _ => (1 : ℝ)) q.1
          * (LevyStochCalc.Poisson.Compensated.restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n).eval q.1 q.2 ω ∂μ)
        = (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
            LevyStochCalc.Poisson.Compensated.stageDefect N ℱ φ h_meas h_progMeas h_sq hA T n ω q.1 q.2 ∂μ)
          + ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, φ ω q.1 q.2 ∂μ := by
    intro μ hD hφ
    rw [← integral_add hD hφ]
    congr 1
    funext q
    simp only [LevyStochCalc.Poisson.Compensated.stageDefect]
    ring
  rw [hω, hsplit _ hDω.1 hφω.1, hsplit _ hDω.2 hφω.2]
  congr 1
  ring
end Assembly

end LevyStochCalc.Poisson.Compensated


