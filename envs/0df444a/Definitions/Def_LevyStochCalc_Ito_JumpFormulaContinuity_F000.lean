-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaContinuity_F000
-- name    : LevyStochCalc_Ito_JumpFormulaContinuity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:46:17.043492+00:00
-- url     : https://prove2.me/theorems/bf4b0288-f4d0-4bd3-b84a-92e6de94e1bc
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaContinuity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaContinuity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaLimit_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaLimit_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Continuity of the derivative integrands of the Itô–Lévy formula

The drift integrand `∂_t u + 𝓛u` of the Itô–Lévy formula is assembled from the time derivative,
the gradient and the Hessian of the state function `u`, and the diffusion integrand `(∇u)ᵀσ` from
the gradient. Each of these partial derivatives is the derivative of a parametrised function —
`t ↦ u t x` for the time derivative, `y ↦ u s y` for the gradient and, once more, for the
Hessian — and for `u` twice continuously differentiable jointly in time and state it is a
continuous function of the pair `(s, x)`: the chain rule for parametrised derivatives passes the
joint smoothness of `u` to `(s, x) ↦ D(u s)(x)` and then to the derivative of that map in the
state. The drift and diffusion integrands are therefore jointly continuous as soon as the drift
and diffusion coefficients are, and at a fixed time the derivative integrands transport
convergence of states with no hypothesis on the coefficients.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.continuous_timeDeriv`,
  `LevyStochCalc.Ito.JumpFormula.continuous_gradient_uncurry`,
  `LevyStochCalc.Ito.JumpFormula.continuous_hessian` — the time derivative, the coordinates of
  the gradient and the entries of the Hessian of a `C²` function of time and state are jointly
  continuous in time and state.
* `LevyStochCalc.Ito.JumpFormula.continuous_levyGenerator`,
  `LevyStochCalc.Ito.JumpFormula.continuous_driftIntegrand`,
  `LevyStochCalc.Ito.JumpFormula.continuous_diffusionIntegrand` — the Lévy generator, the drift
  integrand and the diffusion integrand are jointly continuous for jointly continuous drift and
  diffusion coefficients.
* `LevyStochCalc.Ito.JumpFormula.tendsto_timeDeriv_of_tendsto`,
  `LevyStochCalc.Ito.JumpFormula.tendsto_gradient_of_tendsto`,
  `LevyStochCalc.Ito.JumpFormula.tendsto_hessian_of_tendsto`,
  `LevyStochCalc.Ito.JumpFormula.tendsto_sum_gradient_mul_of_tendsto` — at a fixed time, the
  derivative integrands transport convergence of states.
* `LevyStochCalc.Ito.JumpFormula.tendsto_driftIntegrand_of_tendsto`,
  `LevyStochCalc.Ito.JumpFormula.tendsto_diffusionIntegrand_of_tendsto` — at a fixed time at
  which the coefficients are continuous in the state, so do the drift and diffusion integrands.
-/

open Filter Topology
open LevyStochCalc.Ito.Setting

namespace LevyStochCalc.Ito.JumpFormula

universe v

section Joint

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

/-- The time derivative of a `C²` function of time and state is jointly continuous in time and
state. -/
theorem continuous_timeDeriv (hu : ContDiff ℝ 2 (Function.uncurry u)) :
    Continuous fun p : ℝ × (Fin n → ℝ) => timeDeriv u p.1 p.2 := by
  have hf : ContDiff ℝ 2 (Function.uncurry fun (p : ℝ × (Fin n → ℝ)) (t : ℝ) => u t p.2) :=
    hu.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
  exact (Continuous.fderiv hf continuous_fst one_le_two).clm_apply continuous_const
/-- Each coordinate of the gradient of a `C²` function of time and state is jointly continuous
in time and state. -/
theorem continuous_gradient_uncurry (hu : ContDiff ℝ 2 (Function.uncurry u)) (i : Fin n) :
    Continuous fun p : ℝ × (Fin n → ℝ) => gradient u p.1 p.2 i := by
  have hf : ContDiff ℝ 2 (Function.uncurry fun (p : ℝ × (Fin n → ℝ)) (y : Fin n → ℝ) =>
      u p.1 y) :=
    hu.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact (Continuous.fderiv hf continuous_snd one_le_two).clm_apply continuous_const
/-- Each entry of the Hessian of a `C²` function of time and state is jointly continuous in
time and state. -/
theorem continuous_hessian (hu : ContDiff ℝ 2 (Function.uncurry u)) (i j : Fin n) :
    Continuous fun p : ℝ × (Fin n → ℝ) => hessian u p.1 p.2 i j := by
  have hf : ContDiff ℝ 2 (Function.uncurry
      fun (q : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ)) (y : Fin n → ℝ) => u q.1.1 y) :=
    hu.comp ((contDiff_fst.comp (contDiff_fst.comp contDiff_fst)).prodMk contDiff_snd)
  have h1 : ContDiff ℝ 1 (Function.uncurry fun (p : ℝ × (Fin n → ℝ)) (y : Fin n → ℝ) =>
      fderiv ℝ (u p.1) y (Pi.single i 1)) :=
    ContDiff.fderiv_apply hf contDiff_snd contDiff_const one_add_one_eq_two.le
  exact (Continuous.fderiv h1 continuous_snd le_rfl).clm_apply continuous_const
/-- The Lévy generator `μᵀ∇u + ½ Tr(σσᵀ∇²u)` of a `C²` function of time and state is jointly
continuous in time and state for jointly continuous drift and diffusion coefficients. -/
theorem continuous_levyGenerator {d : ℕ} (hu : ContDiff ℝ 2 (Function.uncurry u))
    {μ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)} {σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)}
    (hμ : Continuous (Function.uncurry μ)) (hσ : Continuous (Function.uncurry σ)) :
    Continuous fun p : ℝ × (Fin n → ℝ) => levyGenerator u μ σ p.1 p.2 := by
  have hμ' : ∀ i, Continuous fun p : ℝ × (Fin n → ℝ) => μ p.1 p.2 i := fun i =>
    (continuous_apply i).comp hμ
  have hσ' : ∀ i k, Continuous fun p : ℝ × (Fin n → ℝ) => σ p.1 p.2 i k := fun i k =>
    (continuous_apply k).comp ((continuous_apply i).comp hσ)
  unfold levyGenerator
  refine (continuous_finsetSum _ fun i _ => (hμ' i).mul (continuous_gradient_uncurry hu i)).add
    (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun k _ => ?_))
  exact ((hσ' i k).mul (hσ' j k)).mul (continuous_hessian hu i j)
/-- The drift integrand `∂_t u + 𝓛u` of a `C²` function of time and state is jointly continuous
in time and state for jointly continuous drift and diffusion coefficients. -/
theorem continuous_driftIntegrand {d : ℕ} {E : Type v} (hu : ContDiff ℝ 2 (Function.uncurry u))
    {coeffs : JumpDiffusionCoeffs n d E} (hμ : Continuous (Function.uncurry coeffs.μ))
    (hσ : Continuous (Function.uncurry coeffs.σ)) :
    Continuous fun p : ℝ × (Fin n → ℝ) => driftIntegrand u coeffs p.1 p.2 :=
  (continuous_timeDeriv hu).add (continuous_levyGenerator hu hμ hσ)
/-- The diffusion integrand `(∇u)ᵀσ` of a `C²` function of time and state is jointly continuous
in time and state for a jointly continuous diffusion coefficient. -/
theorem continuous_diffusionIntegrand {d : ℕ} (hu : ContDiff ℝ 2 (Function.uncurry u))
    {σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)} (hσ : Continuous (Function.uncurry σ)) :
    Continuous fun p : ℝ × (Fin n → ℝ) => diffusionIntegrand u σ p.1 p.2 :=
  continuous_pi fun j => continuous_finsetSum _ fun i _ =>
    (continuous_gradient_uncurry hu i).mul
      ((continuous_apply j).comp ((continuous_apply i).comp hσ))
end Joint

section FixedTime

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ} {z : ℕ → Fin n → ℝ} {w : Fin n → ℝ}

/-- At a fixed time, the time derivative of a `C²` function of time and state transports
convergence of states. -/
theorem tendsto_timeDeriv_of_tendsto (hu : ContDiff ℝ 2 (Function.uncurry u)) (s : ℝ)
    (h : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun m => timeDeriv u s (z m)) atTop (𝓝 (timeDeriv u s w)) :=
  (((continuous_timeDeriv hu).comp (Continuous.prodMk_right s)).tendsto w).comp h
/-- At a fixed time, each coordinate of the gradient of a `C²` function of time and state
transports convergence of states. -/
theorem tendsto_gradient_apply_of_tendsto (hu : ContDiff ℝ 2 (Function.uncurry u)) (s : ℝ)
    (i : Fin n) (h : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun m => gradient u s (z m) i) atTop (𝓝 (gradient u s w i)) :=
  ((continuous_gradient hu s i).tendsto w).comp h
/-- At a fixed time, the gradient of a `C²` function of time and state transports convergence
of states. -/
theorem tendsto_gradient_of_tendsto (hu : ContDiff ℝ 2 (Function.uncurry u)) (s : ℝ)
    (h : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun m => gradient u s (z m)) atTop (𝓝 (gradient u s w)) :=
  tendsto_pi_nhds.mpr fun i => tendsto_gradient_apply_of_tendsto hu s i h
/-- At a fixed time, each entry of the Hessian of a `C²` function of time and state transports
convergence of states. -/
theorem tendsto_hessian_of_tendsto (hu : ContDiff ℝ 2 (Function.uncurry u)) (s : ℝ)
    (i j : Fin n) (h : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun m => hessian u s (z m) i j) atTop (𝓝 (hessian u s w i j)) :=
  (((continuous_hessian hu i j).comp (Continuous.prodMk_right s)).tendsto w).comp h
/-- At a fixed time, the pairing of the gradient of a `C²` function of time and state with a
fixed vector transports convergence of states. -/
theorem tendsto_sum_gradient_mul_of_tendsto (hu : ContDiff ℝ 2 (Function.uncurry u)) (s : ℝ)
    (c : Fin n → ℝ) (h : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun m => ∑ i, gradient u s (z m) i * c i) atTop
      (𝓝 (∑ i, gradient u s w i * c i)) :=
  tendsto_finsetSum _ fun i _ =>
    (tendsto_gradient_apply_of_tendsto hu s i h).mul tendsto_const_nhds
/-- At a fixed time at which the drift and diffusion coefficients are continuous in the state,
the drift integrand `∂_t u + 𝓛u` of a `C²` function of time and state transports convergence of
states. -/
theorem tendsto_driftIntegrand_of_tendsto {d : ℕ} {E : Type v}
    (hu : ContDiff ℝ 2 (Function.uncurry u)) {coeffs : JumpDiffusionCoeffs n d E} (s : ℝ)
    (hμ : Continuous fun y : Fin n → ℝ => coeffs.μ s y)
    (hσ : Continuous fun y : Fin n → ℝ => coeffs.σ s y) (h : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun m => driftIntegrand u coeffs s (z m)) atTop
      (𝓝 (driftIntegrand u coeffs s w)) := by
  have hc : Continuous fun y : Fin n → ℝ => driftIntegrand u coeffs s y :=
    (continuous_driftIntegrand hu
      (coeffs := ⟨fun _ y => coeffs.μ s y, fun _ y => coeffs.σ s y, coeffs.γ⟩)
      (hμ.comp continuous_snd) (hσ.comp continuous_snd)).comp (Continuous.prodMk_right s)
  exact (hc.tendsto w).comp h
/-- At a fixed time at which the diffusion coefficient is continuous in the state, the diffusion
integrand `(∇u)ᵀσ` of a `C²` function of time and state transports convergence of states. -/
theorem tendsto_diffusionIntegrand_of_tendsto {d : ℕ} (hu : ContDiff ℝ 2 (Function.uncurry u))
    {σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)} (s : ℝ)
    (hσ : Continuous fun y : Fin n → ℝ => σ s y) (h : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun m => diffusionIntegrand u σ s (z m)) atTop
      (𝓝 (diffusionIntegrand u σ s w)) := by
  have hc : Continuous fun y : Fin n → ℝ => diffusionIntegrand u σ s y :=
    (continuous_diffusionIntegrand hu (σ := fun _ y => σ s y)
      (hσ.comp continuous_snd)).comp (Continuous.prodMk_right s)
  exact (hc.tendsto w).comp h
end FixedTime

end LevyStochCalc.Ito.JumpFormula


