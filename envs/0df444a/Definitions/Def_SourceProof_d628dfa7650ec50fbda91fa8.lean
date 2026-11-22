-- Prove2me | Definitions.Def_SourceProof_d628dfa7650ec50fbda91fa8
-- name    : SourceProof_d628dfa7650ec50fbda91fa8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:53:14.897187+00:00
-- url     : https://prove2.me/theorems/71d2163c-7c5f-48db-a6a8-0a16276b84c6
-- title:
--   LevyStochCalc source module: SourceProof_d628dfa7650ec50fbda91fa8
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.tendsto_driftIntegral_mollifyJoint` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsC12Limits` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsC12Limits_F000
import Definitions.Def_SourceProof_190b24feee30508af1f5a5e6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy integrands along a joint mollification

For a `C^{1,2}` function `u` of time and state and a family of bumps on `ℝ × (Fin n → ℝ)` whose
outer radii tend to `0`, the drift, diffusion, jump and compensator-drift integrands of the joint
mollifications of `u` converge pointwise to those of `u`, the time derivative, the gradient and
the Hessian of the mollification converging to their counterparts for `u`. When the derivatives
of `u` are bounded, the same bounds hold for every mollification, so along a jump diffusion the
drift integral over a window and the compensator-drift integral over a window and the mark space
converge almost surely, by dominated convergence against a bound built from the coefficients of
the equation alone.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.tendsto_diffusionIntegrand_mollifyJoint`,
  `LevyStochCalc.Ito.JumpFormula.tendsto_sub_mollifyJoint`,
  `LevyStochCalc.Ito.JumpFormula.tendsto_driftIntegrand_mollifyJoint`,
  `LevyStochCalc.Ito.JumpFormula.tendsto_compensatorDriftIntegrand_mollifyJoint` — pointwise
  convergence of the four integrands of the Itô–Lévy formula along the mollifications.
* `LevyStochCalc.Ito.JumpFormula.tendsto_driftIntegral_mollifyJoint` — almost-sure convergence of
  the drift integral along the path of a jump diffusion.
* `LevyStochCalc.Ito.JumpFormula.tendsto_compensatorDriftIntegral_mollifyJoint` — almost-sure
  convergence of the compensator-drift integral along the path of a jump diffusion.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Pointwise

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {u : ℝ → (Fin n → ℝ) → ℝ} {ι : Type*}
  {l : Filter ι} {φ : ι → ContDiffBump (0 : ℝ × (Fin n → ℝ))}

end Pointwise

section Integrals

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}
  {u : ℝ → (Fin n → ℝ) → ℝ}


theorem _root_.Prove2MeSourceProof.h_d628dfa7650ec50fbda91fa8 (S : SdeData X) (hu : IsC12 u) {K₀ K₁ K₂ : ℝ}
    (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀) (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) (φ : ℕ → ContDiffBump (0 : ℝ × (Fin n → ℝ)))
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => ∫ s in Set.Icc (0 : ℝ) T,
        driftIntegrand (mollifyJoint u (φ k)) coeffs s (X.X s ω)) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))) := by
  have hK₀' : ∀ s x, |LevyStochCalc.Ito.JumpFormula.timeDeriv u s x| ≤ max K₀ 0 :=
    fun s x => (hK₀ s x).trans (le_max_left _ _)
  have hK₁' : ∀ s x i, |LevyStochCalc.Ito.JumpFormula.gradient u s x i| ≤ max K₁ 0 :=
    fun s x i => (hK₁ s x i).trans (le_max_left _ _)
  have hK₂' : ∀ s x i j, |LevyStochCalc.Ito.JumpFormula.hessian u s x i j| ≤ max K₂ 0 :=
    fun s x i j => (hK₂ s x i j).trans (le_max_left _ _)
  have hvC : ∀ k, ContDiff ℝ 2 (Function.uncurry (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k))) :=
    fun k => LevyStochCalc.Ito.JumpFormula.contDiff_uncurry_mollifyJoint (N := 2) hu.continuous (φ k)
  have hv0 : ∀ k, ∀ s x, |LevyStochCalc.Ito.JumpFormula.timeDeriv (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) s x| ≤ max K₀ 0 :=
    fun k => LevyStochCalc.Ito.JumpFormula.abs_timeDeriv_mollifyJoint_le hu (φ k) hK₀'
  have hv1 : ∀ k, ∀ s x i, |LevyStochCalc.Ito.JumpFormula.gradient (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) s x i| ≤ max K₁ 0 :=
    fun k => LevyStochCalc.Ito.JumpFormula.abs_gradient_mollifyJoint_le hu (φ k) hK₁'
  have hv2 : ∀ k, ∀ s x i j, |LevyStochCalc.Ito.JumpFormula.hessian (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) s x i j| ≤ max K₂ 0 :=
    fun k => LevyStochCalc.Ito.JumpFormula.abs_hessian_mollifyJoint_le hu (φ k) hK₂'
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
  filter_upwards [hμint, hσsq] with ω hμω hσω
  have hXs : Measurable fun s => X.X s ω := X.measurable_path.of_uncurry_right
  refine tendsto_integral_of_dominated_convergence
    (fun s => max K₀ 0 + max K₁ 0 * ∑ p, |coeffs.μ s (X.X s ω) p|
      + (1 / 2) * max K₂ 0 * ∑ p, ∑ q, ∑ j,
        (coeffs.σ s (X.X s ω) p j ^ 2 + coeffs.σ s (X.X s ω) q j ^ 2) / 2) ?_ ?_ ?_ ?_
  · intro k
    refine Measurable.aestronglyMeasurable ?_
    change Measurable fun s => LevyStochCalc.Ito.JumpFormula.timeDeriv (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) s (X.X s ω)
      + ((∑ p, coeffs.μ s (X.X s ω) p * LevyStochCalc.Ito.JumpFormula.gradient (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) s (X.X s ω) p)
        + (1 / 2) * ∑ p, ∑ q, ∑ j, coeffs.σ s (X.X s ω) p j * coeffs.σ s (X.X s ω) q j
          * LevyStochCalc.Ito.JumpFormula.hessian (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) s (X.X s ω) p q)
    refine Measurable.add ((LevyStochCalc.Ito.JumpFormula.continuous_timeDeriv (hvC k)).measurable.comp
      (measurable_id.prodMk hXs)) (Measurable.add ?_ (measurable_const.mul ?_))
    · exact Finset.measurable_sum _ fun p _ => (Measurable.of_uncurry_left (hμm p)).mul
        ((LevyStochCalc.Ito.JumpFormula.continuous_gradient_uncurry (hvC k) p).measurable.comp (measurable_id.prodMk hXs))
    · refine Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun q _ =>
        Finset.measurable_sum _ fun j _ => ?_
      exact ((Measurable.of_uncurry_left (S.σ_meas p j)).mul
        (Measurable.of_uncurry_left (S.σ_meas q j))).mul
        ((LevyStochCalc.Ito.JumpFormula.continuous_hessian (hvC k) p q).measurable.comp (measurable_id.prodMk hXs))
  · refine Integrable.add (Integrable.add (integrable_const _) ?_) ?_
    · exact (integrable_finsetSum _ fun p _ => (hμω p).abs).const_mul _
    · refine Integrable.const_mul ?_ _
      refine integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
        integrable_finsetSum _ fun j _ => ?_
      exact ((hσω p j).add (hσω q j)).div_const 2
  · intro k
    refine Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs]
    exact _root_.Prove2MeSourceProof.h_190b24feee30508af1f5a5e6 coeffs (le_max_right K₂ 0) (hv0 k) (hv1 k) (hv2 k) s _ _
  · exact Eventually.of_forall fun s =>
      LevyStochCalc.Ito.JumpFormula.tendsto_driftIntegrand_mollifyJoint hφ hu coeffs s (X.X s ω)
end Integrals

end LevyStochCalc.Ito.JumpFormula


