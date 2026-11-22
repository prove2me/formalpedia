-- Prove2me | Definitions.Def_SourceProof_b4aae2ffe9e61807e0ee721e
-- name    : SourceProof_b4aae2ffe9e61807e0ee721e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:42:54.192212+00:00
-- url     : https://prove2.me/theorems/98202c5e-b9fa-4b24-81c0-52c4550ea707
-- title:
--   LevyStochCalc source module: SourceProof_b4aae2ffe9e61807e0ee721e
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.tendsto_lintegral_sq_mixedDiffusionIntegral_sub` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsLimits` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Limit steps of the Itô–Lévy formula at bounded derivatives

Along a family of paths converging to the solution of a jump diffusion at almost every time of a
window, the four term families of the Itô–Lévy formula converge to their counterparts along the
solution: the Brownian integrals of the mixed diffusion integrands and the compensated integrals
of the cut mixed jump increments converge in `L²`, and the mixed drift and compensator-drift
integrals converge almost surely. The compensator-drift step rests on a form of dominated
convergence for a mark integral over a shrinking family of cuts in which the domination and the
pointwise convergence are asked at almost every time of the window only.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section DominatedAe

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

end DominatedAe

section Mixed

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}
  {u : ℝ → (Fin n → ℝ) → ℝ}

open LevyStochCalc.Ito.IntegralLimit in

theorem _root_.Prove2MeSourceProof.h_b4aae2ffe9e61807e0ee721e (S : SdeData X)
    (h𝒢W : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) S.ℱ.rightCont)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) {c : ℝ}
    (hc : ∀ s x i, |gradient u s x i| ≤ c) (hc0 : 0 ≤ c) (y : ℕ → ℝ → Ω → Fin n → ℝ)
    (hym : ∀ (k : ℕ) (j : Fin d), Measurable (Function.uncurry
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y k s ω) (X.X s ω) j))
    (hyp : ∀ (k : ℕ) (j : Fin d), Probability.ProgressivelyMeasurable S.ℱ.rightCont
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y k s ω) (X.X s ω) j)
    (hyq : ∀ (k : ℕ) (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖mixedDiffusionIntegrand u coeffs.σ s (y k s ω) (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hσm : ∀ j : Fin d, Measurable (Function.uncurry
      fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j))
    (hσp : ∀ j : Fin d, Probability.ProgressivelyMeasurable S.ℱ.rightCont
      fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)
    (hσq : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T)
    (hpath : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun k => y k s ω) atTop (𝓝 (X.X s ω))) (j : Fin d) :
    Tendsto (fun k => ∫⁻ ω,
      (‖stochasticIntegralBrownian (W.W j) S.ℱ.rightCont (h𝒢W j)
          (fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y k s ω) (X.X s ω) j)
          (hym k j) (hyp k j) (hyq k j) T ω
        - stochasticIntegralBrownian (W.W j) S.ℱ.rightCont (h𝒢W j)
          (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)
          (hσm j) (hσp j) (hσq j) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by
  refine LevyStochCalc.Ito.IntegralLimit.tendsto_lintegral_sq_stochasticIntegralBrownian_of_dominated
    (W.W j) S.ℱ.rightCont (h𝒢W j)
    (fun k ω s => LevyStochCalc.Ito.JumpFormula.mixedDiffusionIntegrand u coeffs.σ s (y k s ω) (X.X s ω) j)
    (fun ω s => LevyStochCalc.Ito.JumpFormula.diffusionIntegrand u coeffs.σ s (X.X s ω) j)
    (fun ω s => c * ∑ i, |coeffs.σ s (X.X s ω) i j|)
    (fun k => hym k j) (fun k => hyp k j) (fun k => hyq k j)
    (hσm j) (hσp j) (hσq j) ?_ hT ?_ ?_ ?_
  · change Measurable fun p : Ω × ℝ => c * ∑ i, |coeffs.σ p.2 (X.X p.2 p.1) i j|
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ => (S.σ_meas i j).abs)
  · filter_upwards [hpath] with ω hω
    filter_upwards [hω] with s hs
    change Tendsto (fun k => ∑ i, LevyStochCalc.Ito.JumpFormula.gradient u s (y k s ω) i * coeffs.σ s (X.X s ω) i j)
      atTop (𝓝 (∑ i, LevyStochCalc.Ito.JumpFormula.gradient u s (X.X s ω) i * coeffs.σ s (X.X s ω) i j))
    exact LevyStochCalc.Ito.JumpFormula.tendsto_sum_gradient_mul_of_tendsto hu s (fun i => coeffs.σ s (X.X s ω) i j) hs
  · intro k
    refine Eventually.of_forall fun ω => Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs]
    exact LevyStochCalc.Ito.JumpFormula.abs_mixedDiffusionIntegrand_le hc s _ _ j
  · refine LevyStochCalc.Ito.JumpFormula.lintegral_window_sq_le_of_abs_le (a := fun i ω s => coeffs.σ s (X.X s ω) i j)
      (c := c) (fun i => S.σ_meas i j) (fun ω s => ?_) T (fun i => S.σ_sq i j T hT)
    rw [abs_of_nonneg (mul_nonneg hc0 (Finset.sum_nonneg fun i _ => abs_nonneg _))]
end Mixed

end LevyStochCalc.Ito.JumpFormula


