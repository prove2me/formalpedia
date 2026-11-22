-- Prove2me | Definitions.Def_SourceProof_a6b2c2d1839ed980865a4dc9
-- name    : SourceProof_a6b2c2d1839ed980865a4dc9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T13:01:57.287907+00:00
-- url     : https://prove2.me/theorems/3dc18623-b810-40a1-811b-7c78ab65ad8d
-- title:
--   LevyStochCalc source module: SourceProof_a6b2c2d1839ed980865a4dc9
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.multidimIntegral_congr_ae` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionMain` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy formula at bounded derivatives, from the solution data

For regular Lipschitz coefficients and a filtration satisfying the usual conditions, a `C²` state
function with bounded time derivative, gradient and Hessian satisfies the Itô–Lévy formula along
a jump diffusion that solves the equation on every window, that carries SDE data and has left
limits at every sample point and every time, or that carries SDE data alone: its increment is the
drift integral, the Brownian integral of `(∇u)ᵀσ`, the compensated integral of `u(x + γ) − u(x)`
and the compensator-drift integral. Every admissibility input of the two stochastic integrals is
derived from the solution data and the coefficient regularity; `multidimIntegral_congr_ae`
transports the Brownian integral between vector integrands agreeing almost everywhere on a
window.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard LevyStochCalc.Ito.BigJump
  LevyStochCalc.Probability

universe u v

section Main

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (coeffs : JumpDiffusionCoeffs n d E)


theorem _root_.Prove2MeSourceProof.h_a6b2c2d1839ed980865a4dc9 (Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ))
    (hm₁ : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z₁ s ω i))
    (hp₁ : ∀ i : Fin d, ProgressivelyMeasurable ℱ fun ω s => Z₁ s ω i)
    (hq₁ : ∀ i : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z₂ s ω i))
    (hp₂ : ∀ i : Fin d, ProgressivelyMeasurable ℱ fun ω s => Z₂ s ω i)
    (hq₂ : ∀ i : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Z₁ s ω = Z₂ s ω) :
    ∀ᵐ ω ∂P, MultidimBrownianMotion.stochasticIntegral W ℱ hℱW Z₁ hm₁ hp₁ hq₁ T ω
      = MultidimBrownianMotion.stochasticIntegral W ℱ hℱW Z₂ hm₂ hp₂ hq₂ T ω := by
  have hcomp : ∀ i : Fin d, ∀ᵐ ω ∂P,
      LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hℱW i)
          (fun ω' s => Z₁ s ω' i) (hm₁ i) (hp₁ i) (hq₁ i) T ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hℱW i)
          (fun ω' s => Z₂ s ω' i) (hm₂ i) (hp₂ i) (hq₂ i) T ω := by
    intro i
    refine _root_.Prove2MeSourceProof.h_55e10c2bb5834f5a3716267c (W.W i) ℱ (hℱW i) _ _ _ _ _ _ _ _ hT ?_
    filter_upwards [h] with ω hω
    filter_upwards [hω] with s hs
    rw [hs]
  filter_upwards [MeasureTheory.ae_all_iff.mpr hcomp] with ω hω
  simp only [LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral]
  exact Finset.sum_congr rfl fun i _ => hω i
end Main

end LevyStochCalc.Ito.JumpFormula


