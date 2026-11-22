-- Prove2me | Definitions.Def_SourceProof_1efeb911b0e934097fd018ef
-- name    : SourceProof_1efeb911b0e934097fd018ef
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:43:04.560839+00:00
-- url     : https://prove2.me/theorems/ce319155-4d93-4fd8-b926-a38d3407a8b5
-- title:
--   LevyStochCalc source module: SourceProof_1efeb911b0e934097fd018ef
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.tendsto_mixedDriftIntegral_of_tendsto` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsLimits` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F001
import Definitions.Def_SourceProof_190b24feee30508af1f5a5e6

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


theorem _root_.Prove2MeSourceProof.h_1efeb911b0e934097fd018ef (S : SdeData X)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) {c₀ c₁ c₂ : ℝ}
    (hc₀ : ∀ s x, |timeDeriv u s x| ≤ c₀) (hc₁ : ∀ s x i, |gradient u s x i| ≤ c₁)
    (hc₂ : ∀ s x i j, |hessian u s x i j| ≤ c₂) (hc₂0 : 0 ≤ c₂)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) (y : ℕ → ℝ → Ω → Fin n → ℝ)
    (hym : ∀ i, Measurable (Function.uncurry (y i)))
    (hpath : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun i => y i s ω) atTop (𝓝 (X.X s ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun i => ∫ s in Set.Icc (0 : ℝ) T,
        mixedDriftIntegrand u coeffs s (y i s ω) (X.X s ω)) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))) := by
  have hμint : ∀ᵐ ω ∂P, ∀ p : Fin n,
      IntegrableOn (fun s => coeffs.μ s (X.X s ω) p) (Set.Icc (0 : ℝ) T) :=
    MeasureTheory.ae_all_iff.mpr fun p =>
      LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top (hμm p) (hμq p T hT)
  have hσsq : ∀ᵐ ω ∂P, ∀ (p : Fin n) (j : Fin d),
      IntegrableOn (fun s => coeffs.σ s (X.X s ω) p j ^ 2) (Set.Icc (0 : ℝ) T) := by
    refine MeasureTheory.ae_all_iff.mpr fun p => MeasureTheory.ae_all_iff.mpr fun j => ?_
    filter_upwards [MeasureTheory.ae_lt_top (LevyStochCalc.Brownian.Ito.measurable_energyDensity (S.σ_meas p j) T)
      (S.σ_sq p j T hT).ne] with ω hω
    exact (LevyStochCalc.Ito.Picard.memLp_two_of_lintegral_sq_lt_top
      (Measurable.of_uncurry_left (S.σ_meas p j)) hω).integrable_sq
  filter_upwards [hpath, hμint, hσsq] with ω hω hμω hσω
  refine tendsto_integral_of_dominated_convergence
    (fun s => c₀ + c₁ * ∑ p, |coeffs.μ s (X.X s ω) p|
      + (1 / 2) * c₂ * ∑ p, ∑ q, ∑ j,
        (coeffs.σ s (X.X s ω) p j ^ 2 + coeffs.σ s (X.X s ω) q j ^ 2) / 2) ?_ ?_ ?_ ?_
  · intro i
    refine Measurable.aestronglyMeasurable ?_
    have hy : Measurable fun s => y i s ω := (hym i).of_uncurry_right
    change Measurable fun s => LevyStochCalc.Ito.JumpFormula.timeDeriv u s (y i s ω)
      + ((∑ p, coeffs.μ s (X.X s ω) p * LevyStochCalc.Ito.JumpFormula.gradient u s (y i s ω) p)
        + (1 / 2) * ∑ p, ∑ q, ∑ j, coeffs.σ s (X.X s ω) p j * coeffs.σ s (X.X s ω) q j
          * LevyStochCalc.Ito.JumpFormula.hessian u s (y i s ω) p q)
    refine Measurable.add ((LevyStochCalc.Ito.JumpFormula.continuous_timeDeriv hu).measurable.comp
      (measurable_id.prodMk hy)) (Measurable.add ?_ (measurable_const.mul ?_))
    · exact Finset.measurable_sum _ fun p _ => (Measurable.of_uncurry_left (hμm p)).mul
        ((LevyStochCalc.Ito.JumpFormula.continuous_gradient_uncurry hu p).measurable.comp (measurable_id.prodMk hy))
    · refine Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun q _ =>
        Finset.measurable_sum _ fun j _ => ?_
      exact ((Measurable.of_uncurry_left (S.σ_meas p j)).mul
        (Measurable.of_uncurry_left (S.σ_meas q j))).mul
        ((LevyStochCalc.Ito.JumpFormula.continuous_hessian hu p q).measurable.comp (measurable_id.prodMk hy))
  · refine Integrable.add (Integrable.add (integrable_const _) ?_) ?_
    · exact (integrable_finsetSum _ fun p _ => (hμω p).abs).const_mul _
    · refine Integrable.const_mul ?_ _
      refine integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
        integrable_finsetSum _ fun j _ => ?_
      exact ((hσω p j).add (hσω q j)).div_const 2
  · intro i
    refine Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs]
    exact _root_.Prove2MeSourceProof.h_190b24feee30508af1f5a5e6 coeffs hc₂0 hc₀ hc₁ hc₂ s _ _
  · filter_upwards [hω] with s hs
    exact LevyStochCalc.Ito.JumpFormula.tendsto_mixedDriftIntegrand_of_tendsto hu coeffs s _ hs
end Mixed

end LevyStochCalc.Ito.JumpFormula


