-- Prove2me | Definitions.Def_SourceProof_742da096f71ef6ee35a58972
-- name    : SourceProof_742da096f71ef6ee35a58972
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:35:09.625525+00:00
-- url     : https://prove2.me/theorems/db8f4110-ecc4-48ef-8071-6e5ab4ab8586
-- title:
--   LevyStochCalc source module: SourceProof_742da096f71ef6ee35a58972
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.multidimStochasticIntegral_rightCont_ae_eq` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsIntegrands` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F001
import Definitions.Def_LevyStochCalc_Probability_MarkedProgressiveSlice_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissibility of the mixed integrands of the Itô–Lévy formula

The mixed integrands of the Itô–Lévy formula along a jump diffusion — the derivatives of a `C²`
state function read at an auxiliary path, the coefficients read at the solution — are jointly
measurable, are progressively measurable for the right-continuous regularisation of the
filtration of the SDE data, and have finite energy on every bounded window; over that
regularisation the Brownian and the compensated jump integral agree almost surely with the ones
over the filtration itself, and the endpoint of a path together with its two stochastic
integrals is measurable componentwise.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Mixed

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}
  {u : ℝ → (Fin n → ℝ) → ℝ}


theorem _root_.Prove2MeSourceProof.h_742da096f71ef6ee35a58972 (S : SdeData X)
    (h𝒢W : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) S.ℱ.rightCont)
    (Z : ℝ → Ω → Fin d → ℝ)
    (hZm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hZp : ∀ j : Fin d, Probability.ProgressivelyMeasurable S.ℱ fun ω s => Z s ω j)
    (hZp' : ∀ j : Fin d,
      Probability.ProgressivelyMeasurable S.ℱ.rightCont fun ω s => Z s ω j)
    (hZq : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (T : ℝ) :
    MultidimBrownianMotion.stochasticIntegral W S.ℱ.rightCont h𝒢W Z hZm hZp' hZq T
      =ᵐ[P] MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian Z hZm hZp hZq T := by
  have hchan : ∀ j : Fin d,
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) S.ℱ (S.isBrownian j)
          (fun ω s => Z s ω j) (hZm j) (hZp j) (hZq j) T
        =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) S.ℱ.rightCont (h𝒢W j)
          (fun ω s => Z s ω j) (hZm j) (hZp' j) (hZq j) T :=
    fun j => _root_.Prove2MeSourceProof.h_bf1e37b50d3528bd4d7f3e39 (W.W j) S.ℱ S.ℱ.rightCont
      (S.isBrownian j) (h𝒢W j) (fun t => S.ℱ.le_rightCont t) _ (hZm j) (hZp j)
      (hZp' j) (hZq j) T
  filter_upwards [MeasureTheory.ae_all_iff.mpr hchan] with ω hω
  rw [LevyStochCalc.Ito.JumpFormula.multidimStochasticIntegral_eq_sum, LevyStochCalc.Ito.JumpFormula.multidimStochasticIntegral_eq_sum]
  exact Finset.sum_congr rfl fun j _ => (hω j).symm
end Mixed

end LevyStochCalc.Ito.JumpFormula


