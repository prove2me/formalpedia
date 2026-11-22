-- Prove2me | Definitions.Def_SourceProof_480386ee1a4adafe3cb7c0b7
-- name    : SourceProof_480386ee1a4adafe3cb7c0b7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:52:14.812039+00:00
-- url     : https://prove2.me/theorems/bc555c1c-035e-43e8-b9f4-8ec13152496f
-- title:
--   LevyStochCalc source module: SourceProof_480386ee1a4adafe3cb7c0b7
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.tendsto_compensatorDriftIntegral_mollifyJoint` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsC12Limits` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsC12Limits_F000

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


theorem _root_.Prove2MeSourceProof.h_480386ee1a4adafe3cb7c0b7 (S : SdeData X) (hu : IsC12 u) {K₂ : ℝ}
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂) (T : ℝ) (hT : 0 < T)
    (φ : ℕ → ContDiffBump (0 : ℝ × (Fin n → ℝ)))
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
        compensatorDriftIntegrand (mollifyJoint u (φ k)) coeffs.γ s (X.X s ω) e ∂ν) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e,
        compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν)) := by
  have hK₂' : ∀ s x i j, |LevyStochCalc.Ito.JumpFormula.hessian u s x i j| ≤ max K₂ 0 :=
    fun s x i j => (hK₂ s x i j).trans (le_max_left _ _)
  have hvC : ∀ k, ContDiff ℝ 2 (Function.uncurry (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k))) :=
    fun k => LevyStochCalc.Ito.JumpFormula.contDiff_uncurry_mollifyJoint (N := 2) hu.continuous (φ k)
  have hv2 : ∀ k, ∀ s x i j, |LevyStochCalc.Ito.JumpFormula.hessian (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) s x i j| ≤ max K₂ 0 :=
    fun k => LevyStochCalc.Ito.JumpFormula.abs_hessian_mollifyJoint_le hu (φ k) hK₂'
  have hγint : ∀ᵐ ω ∂P, ∀ i : Fin n, Integrable
      (fun p : ℝ × E => coeffs.γ p.1 (X.X p.1 ω) p.2 i ^ 2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    filter_upwards [MeasureTheory.ae_lt_top (LevyStochCalc.Poisson.Compensated.measurable_markEnergy
      (f := fun ω s e => (‖LevyStochCalc.Ito.SmallJump.pathJumpCoeff coeffs X.X i ω s e‖₊ : ℝ≥0∞) ^ 2)
      (((S.γ_meas i).nnnorm.coe_nnreal_ennreal).pow_const 2) T) (S.γ_sq i T hT).ne]
      with ω hω
    have hm : Measurable fun p : ℝ × E => coeffs.γ p.1 (X.X p.1 ω) p.2 i :=
      (S.γ_meas i).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
    have hfin : ∫⁻ p, (‖coeffs.γ p.1 (X.X p.1 ω) p.2 i‖₊ : ℝ≥0∞) ^ 2
        ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) < ⊤ := by
      rw [lintegral_prod _ ((hm.nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable)]
      exact hω
    exact (LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top hm.aestronglyMeasurable hfin).integrable_sq
  filter_upwards [hγint] with ω hγω
  have hγm : Measurable fun p : ℝ × E => coeffs.γ p.1 (X.X p.1 ω) p.2 :=
    measurable_pi_lambda _ fun i =>
      (S.γ_meas i).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  have hmeas : ∀ k : ℕ, AEStronglyMeasurable (fun p : ℝ × E =>
      LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) coeffs.γ p.1 (X.X p.1 ω) p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) := by
    intro k
    refine Measurable.aestronglyMeasurable ?_
    have hX : Measurable fun p : ℝ × E => X.X p.1 ω :=
      X.measurable_path.of_uncurry_right.comp measurable_fst
    have hv : Measurable fun q : ℝ × (Fin n → ℝ) => LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k) q.1 q.2 :=
      (hvC k).continuous.measurable
    change Measurable fun p : ℝ × E =>
      LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k) p.1 (X.X p.1 ω + coeffs.γ p.1 (X.X p.1 ω) p.2)
        - LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k) p.1 (X.X p.1 ω)
        - ∑ i, coeffs.γ p.1 (X.X p.1 ω) p.2 i * LevyStochCalc.Ito.JumpFormula.gradient (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) p.1
            (X.X p.1 ω) i
    refine Measurable.sub (Measurable.sub ?_ ?_) ?_
    · exact hv.comp (measurable_fst.prodMk (hX.add hγm))
    · exact hv.comp (measurable_fst.prodMk hX)
    · exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hγm).mul
        ((LevyStochCalc.Ito.JumpFormula.continuous_gradient_uncurry (hvC k) i).measurable.comp (measurable_fst.prodMk hX))
  have hmain := _root_.Prove2MeSourceProof.h_670dd632abdc3697b3edb67d (ν := ν) (T := T)
    (A := fun _ : ℕ => (∅ : Set E))
    (fs := fun k s e =>
      LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand (LevyStochCalc.Ito.JumpFormula.mollifyJoint u (φ k)) coeffs.γ s (X.X s ω) e)
    (f := fun s e => LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e)
    (g := fun s e => (n : ℝ) ^ 2 * max K₂ 0 * ((n : ℝ) * ∑ i, coeffs.γ s (X.X s ω) e i ^ 2))
    (fun _ => MeasurableSet.empty)
    (Eventually.of_forall fun e => Eventually.of_forall fun _ => Set.notMem_empty e)
    hmeas ((((integrable_finsetSum _ fun i _ => hγω i).const_mul _).const_mul _))
    (fun k _s _hs e => LevyStochCalc.Ito.JumpFormula.abs_mixedCompensatorDriftIntegrand_le (hvC k) (hv2 k)
      (le_max_right K₂ 0) _ _ _ e)
    (fun s _hs e => LevyStochCalc.Ito.JumpFormula.tendsto_compensatorDriftIntegrand_mollifyJoint hφ hu coeffs.γ s
      (X.X s ω) e)
  simpa only [Set.compl_empty, Measure.restrict_univ] using hmain
end Integrals

end LevyStochCalc.Ito.JumpFormula


