-- Prove2me | Definitions.Def_SourceProof_217f44132bf28379085aa30a
-- name    : SourceProof_217f44132bf28379085aa30a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:58:19.406476+00:00
-- url     : https://prove2.me/theorems/77dd9368-4b7c-499c-9421-15704a185bc7
-- title:
--   LevyStochCalc source module: SourceProof_217f44132bf28379085aa30a
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.ae_picardStep_zero` comes from the `LevyStochCalc.Ito.PicardOutputStepDiff` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputStepDiff_F000
import Definitions.Def_SourceProof_39285c9e8cb91346b858af97

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The contraction estimate for the Picard step

The Picard step is the sum of its drift, diffusion and jump components, so the three
per-component difference bounds combine, through `‖a + b + c‖² ≤ 3(‖a‖² + ‖b‖² + ‖c‖²)`,
into a single per-time second-moment bound for the difference of two steps by the energy of
the difference of the two frozen paths. Weighting that bound back into the Bielecki norm
gives a contraction factor that tends to `0` as the rate `β` grows.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

section Weighting


theorem _root_.Prove2MeSourceProof.h_217f44132bf28379085aa30a
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq 0 ω i = x₀ i := by
  have hdrift : ∀ (ω : Ω) (i : Fin n), LevyStochCalc.Ito.Picard.picardStep_drift coeffs X x₀ 0 ω i = x₀ i := by
    intro ω i
    have hzero : (∫ s in Set.Icc (0 : ℝ) 0, coeffs.μ s (X s ω) i ∂volume) = 0 :=
      MeasureTheory.setIntegral_measure_zero _ (by simp)
    change x₀ i + (∫ s in Set.Icc (0 : ℝ) 0, coeffs.μ s (X s ω) i ∂volume) = x₀ i
    rw [hzero, add_zero]
  have hσ : ∀ᵐ ω ∂P, ∀ p : Fin n × Fin d,
      LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W p.2) ℱ (hℱW p.2)
        (fun ω' s => coeffs.σ s (X s ω') p.1 p.2)
        (h_σ_meas p.1 p.2) (h_σ_progMeas p.1 p.2) (h_σ_sq p.1 p.2) 0 ω = 0 :=
    MeasureTheory.ae_all_iff.mpr fun p =>
      _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 (W.W p.2) ℱ
        (hℱW p.2) (fun ω' s => coeffs.σ s (X s ω') p.1 p.2)
        (h_σ_meas p.1 p.2) (h_σ_progMeas p.1 p.2) (h_σ_sq p.1 p.2) le_rfl
  have hγ : ∀ᵐ ω ∂P, ∀ i : Fin n,
      LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq 0 ω i = 0 := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱN
        (fun ω s e => coeffs.γ s (X s ω) e i) (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i) 0,
      _root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 N ℱ hℱN
        (fun ω s e => coeffs.γ s (X s ω) e i) (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i)
        le_rfl] with ω h1 h2
    change LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
      (fun ω' s e => coeffs.γ s (X s ω') e i) (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i) 0 ω = 0
    rw [h1, h2]
    rfl
  filter_upwards [hσ, hγ] with ω hσω hγω i
  rw [LevyStochCalc.Ito.Picard.picardStep_apply_eq W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
    h_γ_meas h_γ_progMeas h_γ_sq 0 ω i, hdrift ω i, hγω i, add_zero]
  have hdiff : LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq 0 ω i = 0 := by
    change (∑ j : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_σ_meas i j) (h_σ_progMeas i j) (h_σ_sq i j) 0 ω) = 0
    exact Finset.sum_eq_zero fun j _ => hσω (i, j)
  rw [hdiff, add_zero]
-- `picardStep` and the two stochastic-integral components unfold to `Finset` sums over `Fin d`
-- and to the `L²`-limit integrals; the statement below repeats those terms verbatim on both
-- sides, so unfolding them during unification only costs time. Sealed as in `Ito/Picard.lean`.
attribute [local irreducible] picardStep picardStep_diffusion picardStep_jump
attribute [local irreducible]
  LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
attribute [local irreducible] LevyStochCalc.Brownian.Ito.stochasticIntegral

end Weighting

end LevyStochCalc.Ito.Picard


