-- Prove2me | Definitions.Def_SourceProof_1f982f95c243b7704e920390
-- name    : SourceProof_1f982f95c243b7704e920390
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:26:36.197815+00:00
-- url     : https://prove2.me/theorems/417f2a54-f377-4d71-93e4-e09749bc18fe
-- title:
--   LevyStochCalc source module: SourceProof_1f982f95c243b7704e920390
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.continuous_setIntegral_Icc_of_integrableOn` comes from the `LevyStochCalc.Ito.PicardOutputModification` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F002
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Càdlàg modifications of the Picard step

The `L²` stochastic integral is defined separately at each time, so the Picard step as first
written has no path regularity. Replacing each Brownian component by a càdlàg adapted
modification, and the drift by its almost surely continuous version, produces a process
indistinguishable from the step at every fixed time and càdlàg along almost every path; the
Bielecki norm is unchanged, and the result is a genuine self-map of the space of bounded
adapted càdlàg processes.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_1f982f95c243b7704e920390 {f : ℝ → ℝ}
    (h_int : ∀ b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) b) volume) :
    Continuous fun t => ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume := by
  classical
  set g : ℝ → ℝ := Set.indicator (Set.Ici (0 : ℝ)) f with hgdef
  have hgint : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
    intro a b
    have hsub : Set.Ici (0 : ℝ) ∩ Set.uIoc a b ⊆ Set.Icc (0 : ℝ) (max a b) := by
      rintro x ⟨hx0, hx⟩
      exact ⟨hx0, hx.2⟩
    rw [intervalIntegrable_iff, MeasureTheory.IntegrableOn,
      MeasureTheory.integrable_indicator_iff measurableSet_Ici,
      MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_restrict measurableSet_Ici]
    exact (h_int (max a b)).mono_set hsub
  have heq : (fun t => ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume)
      = fun t => ∫ s in (0 : ℝ)..(max t 0), g s ∂volume := by
    funext t
    rcases le_or_gt 0 t with ht | ht
    · rw [max_eq_left ht, intervalIntegral.integral_of_le ht,
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
      exact (Set.indicator_of_mem (Set.mem_Ici.mpr hx.1) f).symm
    · rw [max_eq_right ht.le, intervalIntegral.integral_same,
        Set.Icc_eq_empty (not_le.mpr ht), MeasureTheory.setIntegral_empty]
  rw [heq]
  exact (intervalIntegral.continuous_primitive hgint 0).comp
    (continuous_id.max continuous_const)
section Modification

variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (X : ℝ → Ω → (Fin n → ℝ))
variable (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
  Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
variable (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
  Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
variable (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (x₀ : Fin n → ℝ)
variable (h_γ_meas : ∀ i : Fin n,
  Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
variable (h_γ_progMeas : ∀ i : Fin n,
  Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
variable (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Modification

section SelfMap

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]

end SelfMap

end LevyStochCalc.Ito.Picard


