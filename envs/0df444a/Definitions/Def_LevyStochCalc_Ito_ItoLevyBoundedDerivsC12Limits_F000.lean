-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsC12Limits_F000
-- name    : LevyStochCalc_Ito_ItoLevyBoundedDerivsC12Limits_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:47:54.574332+00:00
-- url     : https://prove2.me/theorems/720c40f2-1894-48ae-bd7a-6e1fd24eb332
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoLevyBoundedDerivsC12Limits
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoLevyBoundedDerivsC12Limits. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_C12MollifyJoint_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionIntegrands_F000

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

/-- Along a family of bumps whose outer radii tend to `0` the row product `(∇u)ᵀσ` of the joint
mollification of a `C^{1,2}` function converges to the row product of that function. -/
theorem tendsto_diffusionIntegrand_mollifyJoint (hφ : Tendsto (fun k => (φ k).rOut) l (𝓝 0))
    (hu : IsC12 u) (σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)) (s : ℝ) (x : Fin n → ℝ)
    (j : Fin d) :
    Tendsto (fun k => diffusionIntegrand (mollifyJoint u (φ k)) σ s x j) l
      (𝓝 (diffusionIntegrand u σ s x j)) := by
  simp only [diffusionIntegrand]
  exact tendsto_finsetSum _ fun i _ => (tendsto_gradient_mollifyJoint hφ hu s x i).mul_const _
/-- Along a family of bumps whose outer radii tend to `0` an increment of the joint mollification
of a `C^{1,2}` function converges to the corresponding increment of that function. -/
theorem tendsto_sub_mollifyJoint (hφ : Tendsto (fun k => (φ k).rOut) l (𝓝 0)) (hu : IsC12 u)
    (s : ℝ) (y x : Fin n → ℝ) :
    Tendsto (fun k => mollifyJoint u (φ k) s y - mollifyJoint u (φ k) s x) l
      (𝓝 (u s y - u s x)) :=
  (tendsto_mollifyJoint hφ hu.continuous s y).sub (tendsto_mollifyJoint hφ hu.continuous s x)
omit [MeasurableSpace E] in
/-- Along a family of bumps whose outer radii tend to `0` the drift integrand `∂_t u + 𝓛u` of the
joint mollification of a `C^{1,2}` function converges to the drift integrand of that function. -/
theorem tendsto_driftIntegrand_mollifyJoint (hφ : Tendsto (fun k => (φ k).rOut) l (𝓝 0))
    (hu : IsC12 u) (coeffs : JumpDiffusionCoeffs n d E) (s : ℝ) (x : Fin n → ℝ) :
    Tendsto (fun k => driftIntegrand (mollifyJoint u (φ k)) coeffs s x) l
      (𝓝 (driftIntegrand u coeffs s x)) := by
  simp only [driftIntegrand, levyGenerator]
  refine (tendsto_timeDeriv_mollifyJoint hφ hu s x).add (Tendsto.add ?_ ?_)
  · exact tendsto_finsetSum _ fun i _ => (tendsto_gradient_mollifyJoint hφ hu s x i).const_mul _
  · exact Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun p _ =>
      tendsto_finsetSum _ fun m _ => (tendsto_hessian_mollifyJoint hφ hu s x i p).const_mul _)
omit [MeasurableSpace E] in
/-- Along a family of bumps whose outer radii tend to `0` the compensator-drift integrand of the
joint mollification of a `C^{1,2}` function converges to that of the function. -/
theorem tendsto_compensatorDriftIntegrand_mollifyJoint
    (hφ : Tendsto (fun k => (φ k).rOut) l (𝓝 0)) (hu : IsC12 u)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (s : ℝ) (x : Fin n → ℝ) (e : E) :
    Tendsto (fun k => compensatorDriftIntegrand (mollifyJoint u (φ k)) γ s x e) l
      (𝓝 (compensatorDriftIntegrand u γ s x e)) := by
  simp only [compensatorDriftIntegrand]
  refine ((tendsto_mollifyJoint hφ hu.continuous s (x + γ s x e)).sub
    (tendsto_mollifyJoint hφ hu.continuous s x)).sub ?_
  exact tendsto_finsetSum _ fun i _ => (tendsto_gradient_mollifyJoint hφ hu s x i).const_mul _
end Pointwise

section Integrals

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}
  {u : ℝ → (Fin n → ℝ) → ℝ}

end Integrals

end LevyStochCalc.Ito.JumpFormula


