-- Prove2me | Definitions.Def_SourceProof_f512774c3d012a8b87c44ec5
-- name    : SourceProof_f512774c3d012a8b87c44ec5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:27:27.094773+00:00
-- url     : https://prove2.me/theorems/01fecb33-4ca3-4e8b-bf2c-ae3939478c0f
-- title:
--   LevyStochCalc source module: SourceProof_f512774c3d012a8b87c44ec5
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.ae_memLp_two_of_lintegral_sq` comes from the `LevyStochCalc.Ito.PicardOutputModification` module. The staged Lean declaration includes its source proof and dependency references.
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

theorem _root_.Prove2MeSourceProof.h_f512774c3d012a8b87c44ec5 {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f))
    (hfin : ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ b : ℝ,
      MeasureTheory.MemLp (f ω) 2 (volume.restrict (Set.Icc (0 : ℝ) b)) := by
  have hstep : ∀ n : ℕ, ∀ᵐ ω ∂P,
      ∫⁻ s in Set.Icc (0 : ℝ) ((n : ℝ) + 1), (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ := by
    intro n
    refine MeasureTheory.ae_lt_top ?_ (hfin ((n : ℝ) + 1) (by positivity)).ne
    exact (hf.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
  filter_upwards [MeasureTheory.ae_all_iff.mpr hstep] with ω hω b
  obtain ⟨n, hn⟩ := exists_nat_ge b
  have hsub : Set.Icc (0 : ℝ) b ⊆ Set.Icc (0 : ℝ) ((n : ℝ) + 1) :=
    Set.Icc_subset_Icc le_rfl (by linarith)
  have hslice : Measurable (f ω) := hf.comp (measurable_const.prodMk measurable_id)
  exact (LevyStochCalc.Ito.Picard.memLp_two_of_lintegral_sq_lt_top hslice (hω n)).mono_measure
    (MeasureTheory.Measure.restrict_mono hsub le_rfl)
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


