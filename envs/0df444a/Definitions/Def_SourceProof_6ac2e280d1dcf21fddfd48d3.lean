-- Prove2me | Definitions.Def_SourceProof_6ac2e280d1dcf21fddfd48d3
-- name    : SourceProof_6ac2e280d1dcf21fddfd48d3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:01:43.775187+00:00
-- url     : https://prove2.me/theorems/31fe8b17-d350-4a1d-947b-6de9d6a848de
-- title:
--   LevyStochCalc source module: SourceProof_6ac2e280d1dcf21fddfd48d3
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stageIntegral_sub_sq_le` comes from the `LevyStochCalc.Poisson.CompensatedApprox` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_410f74bc0d5bdc6969bf4ac5
import Definitions.Def_SourceProof_f05975f5c16ce82825064bca

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Approximation of a square-integrable integrand by mark-step integrands

For a jointly measurable, progressively measurable integrand `φ : Ω → ℝ → E → ℝ` that is
square integrable over `Ω × [0, T] × E`, and any dyadic level `L₀` and tolerance `ε`, there is
an adapted mark-step integrand on a dyadic grid of level at least `L₀` within `ε` of `φ` in
`L²(P ⊗ ds ⊗ ν)` on `[0, T]` (`exists_markStep_close`). The integrand is first clipped and
restricted to a mark set of finite measure (`truncate`), which reduces to the bounded,
finitely supported case treated by `exists_markEval_L2_tendsto`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Truncate

variable (φ : Ω → ℝ → E → ℝ) (M : ℝ) (S : Set E)

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end Truncate

section Close

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)

end Close

section Master

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Master

section Cauchy

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

theorem _root_.Prove2MeSourceProof.h_6ac2e280d1dcf21fddfd48d3 {n n' : ℕ} (h : n ≤ n') {t : ℝ} (ht : t ≤ stageHorizon n) :
    ∫⁻ ω, (‖stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω
        - stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n' t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * ((n : ℝ≥0∞) + 1)⁻¹ + 2 * ((n' : ℝ≥0∞) + 1)⁻¹ := by
  refine le_trans ?_ (_root_.Prove2MeSourceProof.h_f05975f5c16ce82825064bca N ℱ hℱ φ h_meas h_progMeas h_sq_int_global h)
  set M : ℝ → Ω → ℝ := fun u ω => LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n u ω
    - LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n' u ω with hMdef
  have hmart : Martingale M ℱ P :=
    (LevyStochCalc.Poisson.Compensated.martingale_stageIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global n).sub
      (LevyStochCalc.Poisson.Compensated.martingale_stageIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global n')
  have hL2 : ∀ u, MemLp (M u) 2 P := fun u =>
    (LevyStochCalc.Poisson.Compensated.memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n u).sub
      (LevyStochCalc.Poisson.Compensated.memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n' u)
  have key := _root_.Prove2MeSourceProof.h_410f74bc0d5bdc6969bf4ac5 hmart (hL2 t)
    (hL2 (LevyStochCalc.Poisson.Compensated.stageHorizon n)) ht
  have h0 : 0 ≤ ∫ ω, (M (LevyStochCalc.Poisson.Compensated.stageHorizon n) ω - M t ω) ^ 2 ∂P :=
    integral_nonneg fun ω => sq_nonneg _
  have hle : ∫ ω, (M t ω) ^ 2 ∂P ≤ ∫ ω, (M (LevyStochCalc.Poisson.Compensated.stageHorizon n) ω) ^ 2 ∂P := by linarith
  change ∫⁻ ω, (‖M t ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ ∫⁻ ω, (‖M (LevyStochCalc.Poisson.Compensated.stageHorizon n) ω‖₊ : ℝ≥0∞) ^ 2 ∂P
  rw [LevyStochCalc.Poisson.Compensated.lintegral_sq_eq_ofReal_integral (hL2 t),
    LevyStochCalc.Poisson.Compensated.lintegral_sq_eq_ofReal_integral (hL2 (LevyStochCalc.Poisson.Compensated.stageHorizon n))]
  exact ENNReal.ofReal_le_ofReal hle
end Cauchy

end LevyStochCalc.Poisson.Compensated


