-- Prove2me | Definitions.Def_LevyStochCalc_Ito_C12Mollify_F001
-- name    : LevyStochCalc_Ito_C12Mollify_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:58:07.093588+00:00
-- url     : https://prove2.me/theorems/966fde80-1ef9-4590-97c3-e11a3b9a2fc5
-- title:
--   Source declarations: LevyStochCalc.Ito.C12Mollify
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.C12Mollify. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_C12Mollify_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Mollification in time of a function of time and state

For a function `u : ℝ → (Fin n → ℝ) → ℝ` of time and state and a smooth compactly supported bump
`ρ` on `ℝ`, the time mollification `mollifyTime u ρ t x = ∫ r, ρ(r) u(t - r, x) dr` averages `u`
over a window of time of width the outer radius of `ρ`, leaving the state argument untouched. At
a fixed state it is the convolution of the normalised bump with the time section `r ↦ u(r, x)`,
so it inherits the smoothness of the bump in the time variable; it is jointly continuous in time
and state whenever `u` is; and along a family of bumps whose outer radii tend to `0` it converges
to `u` pointwise.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.mollifyTime_apply_eq_convolution` — the time mollification at a
  fixed state is a convolution.
* `LevyStochCalc.Ito.JumpFormula.contDiff_time_mollifyTime` — at a fixed state the time
  mollification is `C^N` in time for every `N`.
* `LevyStochCalc.Ito.JumpFormula.continuous_uncurry_mollifyTime` — the time mollification of a
  jointly continuous function is jointly continuous.
* `LevyStochCalc.Ito.JumpFormula.tendsto_mollifyTime` — pointwise convergence of the time
  mollification along a family of bumps whose outer radii tend to `0`.
* `LevyStochCalc.Ito.JumpFormula.timeDeriv_mollifyTime`,
  `LevyStochCalc.Ito.JumpFormula.gradient_mollifyTime`,
  `LevyStochCalc.Ito.JumpFormula.hessian_mollifyTime` — the time derivative, the gradient and the
  Hessian of the time mollification of a `C^{1,2}` function are the time mollifications of the
  time derivative, the gradient and the Hessian of that function.
-/

open MeasureTheory Filter Topology
open scoped Convolution

namespace LevyStochCalc.Ito.JumpFormula

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

/-- Along a family of bumps whose outer radii tend to `0` the time mollification of a jointly
continuous function converges to that function pointwise. -/
theorem tendsto_mollifyTime {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (hu : Continuous (Function.uncurry u)) (t : ℝ)
    (x : Fin n → ℝ) : Tendsto (fun i => mollifyTime u (φ i) t x) l (𝓝 (u t x)) := by
  simp only [mollifyTime_apply_eq_convolution]
  exact ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hφ
    (continuous_time_section hu x) t
/-- The integrand of the time mollification is continuous in the integration variable. -/
theorem continuous_mollifyTime_integrand (hu : Continuous (Function.uncurry u))
    (ρ : ContDiffBump (0 : ℝ)) (t : ℝ) (x : Fin n → ℝ) :
    Continuous fun r : ℝ => ρ.normed volume r * u (t - r) x :=
  (ρ.contDiff_normed (n := 0)).continuous.mul
    (hu.comp ((continuous_const.sub continuous_id).prodMk continuous_const))
/-- The integrand of the time mollification has compact support. -/
theorem hasCompactSupport_mollifyTime_integrand (ρ : ContDiffBump (0 : ℝ)) (t : ℝ)
    (x : Fin n → ℝ) : HasCompactSupport fun r : ℝ => ρ.normed volume r * u (t - r) x :=
  ρ.hasCompactSupport_normed.mul_right
/-- The integrand of the time mollification is integrable. -/
theorem integrable_mollifyTime_integrand (hu : Continuous (Function.uncurry u))
    (ρ : ContDiffBump (0 : ℝ)) (t : ℝ) (x : Fin n → ℝ) :
    Integrable (fun r : ℝ => ρ.normed volume r * u (t - r) x) volume :=
  (continuous_mollifyTime_integrand hu ρ t x).integrable_of_hasCompactSupport
    (hasCompactSupport_mollifyTime_integrand ρ t x)
/-- On a bounded interval of times the integrand of the time mollification is dominated by a
multiple of the normalised bump. -/
theorem exists_bound_mollifyTime (hu : Continuous (Function.uncurry u))
    (ρ : ContDiffBump (0 : ℝ)) (t₀ : ℝ) (x : Fin n → ℝ) :
    ∃ M : ℝ, ∀ t ∈ Set.Ioo (t₀ - 1) (t₀ + 1), ∀ r : ℝ,
      ‖ρ.normed volume r * u (t - r) x‖ ≤ ρ.normed volume r * M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := t₀ - 1 - ρ.rOut) (b := t₀ + 1 + ρ.rOut)
    (α := ℝ)).exists_bound_of_continuousOn (continuous_time_section hu x).continuousOn
  refine ⟨M, fun t ht r => ?_⟩
  rcases eq_or_lt_of_le (ρ.nonneg_normed r) with hr | hr
  · rw [← hr]
    simp
  · have hrb : |r| < ρ.rOut := by
      have hmem : r ∈ Metric.ball (0 : ℝ) ρ.rOut := by
        rw [← ρ.support_normed_eq (μ := volume)]
        exact hr.ne'
      simpa [Real.dist_eq] using hmem
    have hle : |u (t - r) x| ≤ M := by
      obtain ⟨hl, hr'⟩ := Set.mem_Ioo.mp ht
      obtain ⟨hr1, hr2⟩ := abs_lt.mp hrb
      simpa using hM (t - r) (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
    have hnorm : ‖ρ.normed volume r * u (t - r) x‖ = ρ.normed volume r * |u (t - r) x| := by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg_normed r)]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hle (ρ.nonneg_normed r)
/-- The time mollification of a `C^{1,2}` function is differentiable in time, with derivative the
time mollification of the time derivative. -/
theorem hasDerivAt_time_mollifyTime (hu : IsC12 u) (ρ : ContDiffBump (0 : ℝ)) (t₀ : ℝ)
    (x : Fin n → ℝ) :
    HasDerivAt (fun t => mollifyTime u ρ t x) (mollifyTime (timeDeriv u) ρ t₀ x) t₀ := by
  have hdu : Continuous (Function.uncurry (timeDeriv u)) := hu.continuous_timeDeriv
  obtain ⟨M, hM⟩ := exists_bound_mollifyTime hdu ρ t₀ x
  have hs : Set.Ioo (t₀ - 1) (t₀ + 1) ∈ 𝓝 t₀ :=
    isOpen_Ioo.mem_nhds (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
  have hdiff : ∀ᵐ r : ℝ, ∀ t ∈ Set.Ioo (t₀ - 1) (t₀ + 1),
      HasDerivAt (fun τ : ℝ => ρ.normed volume r * u (τ - r) x)
        (ρ.normed volume r * timeDeriv u (t - r) x) t := by
    refine Eventually.of_forall fun r t _ => ?_
    have h1 : HasDerivAt (fun τ : ℝ => u (τ - r) x) (timeDeriv u (t - r) x) t := by
      have h2 := (hu.hasTimeDeriv (t - r) x).comp t ((hasDerivAt_id t).sub_const r)
      simpa [Function.comp_def] using h2
    exact h1.const_mul (ρ.normed volume r)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t r : ℝ => ρ.normed volume r * u (t - r) x)
    (F' := fun t r : ℝ => ρ.normed volume r * timeDeriv u (t - r) x)
    (bound := fun r : ℝ => ρ.normed volume r * M) hs
    (Eventually.of_forall fun t =>
      (continuous_mollifyTime_integrand hu.continuous ρ t x).aestronglyMeasurable)
    (integrable_mollifyTime_integrand hu.continuous ρ t₀ x)
    (continuous_mollifyTime_integrand hdu ρ t₀ x).aestronglyMeasurable
    (Eventually.of_forall fun r t ht => hM t ht r) (ρ.integrable_normed.mul_const M) hdiff
  exact hmain.2
/-- The time derivative of the time mollification of a `C^{1,2}` function is the time
mollification of its time derivative. -/
theorem timeDeriv_mollifyTime (hu : IsC12 u) (ρ : ContDiffBump (0 : ℝ)) (t : ℝ)
    (x : Fin n → ℝ) :
    timeDeriv (mollifyTime u ρ) t x = mollifyTime (timeDeriv u) ρ t x :=
  (hasDerivAt_time_mollifyTime hu ρ t x).deriv
/-- The state derivative of a function of time and state, as a continuous linear functional, is
the coordinate pairing with its gradient. -/
theorem fderiv_state_eq_sum_gradient (s : ℝ) (z : Fin n → ℝ) :
    fderiv ℝ (u s) z
      = ∑ i : Fin n, gradient u s z i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) := by
  ext v
  rw [fderiv_apply_eq_sum_gradient]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
/-- The state derivative of a `C^{1,2}` function is jointly continuous in time and state. -/
theorem continuous_fderiv_state (hu : IsC12 u) :
    Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (u p.1) p.2 := by
  have h : (fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (u p.1) p.2)
      = fun p : ℝ × (Fin n → ℝ) => ∑ i : Fin n, gradient u p.1 p.2 i •
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) :=
    funext fun p => fderiv_state_eq_sum_gradient p.1 p.2
  rw [h]
  exact continuous_finsetSum _ fun i _ => (hu.continuous_gradient i).smul continuous_const
/-- The state-derivative integrand of the time mollification is continuous in the integration
variable. -/
theorem continuous_mollifyTime_fderiv_integrand (hu : IsC12 u) (ρ : ContDiffBump (0 : ℝ)) (t : ℝ)
    (z : Fin n → ℝ) : Continuous fun r : ℝ => ρ.normed volume r • fderiv ℝ (u (t - r)) z :=
  (ρ.contDiff_normed (n := 0)).continuous.smul
    ((continuous_fderiv_state hu).comp
      ((continuous_const.sub continuous_id).prodMk continuous_const))
/-- The state-derivative integrand of the time mollification is integrable. -/
theorem integrable_mollifyTime_fderiv_integrand (hu : IsC12 u) (ρ : ContDiffBump (0 : ℝ)) (t : ℝ)
    (z : Fin n → ℝ) :
    Integrable (fun r : ℝ => ρ.normed volume r • fderiv ℝ (u (t - r)) z) volume :=
  (continuous_mollifyTime_fderiv_integrand hu ρ t z).integrable_of_hasCompactSupport
    ρ.hasCompactSupport_normed.smul_right
/-- A continuous function of time and state, evaluated at times shifted by the support of a bump
and at states in a ball, is dominated by a multiple of the normalised bump. -/
theorem exists_bound_bump_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ContDiffBump (0 : ℝ)) {g : ℝ × (Fin n → ℝ) → F} (hg : Continuous g) (t : ℝ)
    (x : Fin n → ℝ) :
    ∃ M : ℝ, ∀ r : ℝ, ∀ z ∈ Metric.ball x 1,
      ‖ρ.normed volume r • g (t - r, z)‖ ≤ ρ.normed volume r * M := by
  have hKc : IsCompact (Set.Icc (t - ρ.rOut) (t + ρ.rOut) ×ˢ Metric.closedBall x 1) :=
    isCompact_Icc.prod (isCompact_closedBall x 1)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨M, fun r z hz => ?_⟩
  rcases eq_or_lt_of_le (ρ.nonneg_normed r) with hr | hr
  · rw [← hr]
    simp
  · have hrb : |r| < ρ.rOut := by
      have hmem : r ∈ Metric.ball (0 : ℝ) ρ.rOut := by
        rw [← ρ.support_normed_eq (μ := volume)]
        exact hr.ne'
      simpa [Real.dist_eq] using hmem
    have hmem : (t - r, z) ∈ Set.Icc (t - ρ.rOut) (t + ρ.rOut) ×ˢ Metric.closedBall x 1 := by
      obtain ⟨hr1, hr2⟩ := abs_lt.mp hrb
      exact ⟨Set.mem_Icc.mpr ⟨by linarith, by linarith⟩, Metric.ball_subset_closedBall hz⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg_normed r)]
    exact mul_le_mul_of_nonneg_left (hM _ hmem) (ρ.nonneg_normed r)
/-- The time mollification of a `C^{1,2}` function is differentiable in the state, with state
derivative the integral of the time-mollified state derivatives. -/
theorem hasFDerivAt_state_mollifyTime (hu : IsC12 u) (ρ : ContDiffBump (0 : ℝ)) (t : ℝ)
    (x : Fin n → ℝ) :
    HasFDerivAt (mollifyTime u ρ t)
      (∫ r : ℝ, ρ.normed volume r • fderiv ℝ (u (t - r)) x) x := by
  obtain ⟨M, hM⟩ := exists_bound_bump_smul ρ (continuous_fderiv_state hu) t x
  have hbound : ∀ᵐ r : ℝ, ∀ z ∈ Metric.ball x 1,
      ‖ρ.normed volume r • fderiv ℝ (u (t - r)) z‖ ≤ ρ.normed volume r * M :=
    Eventually.of_forall fun r z hz => hM r z hz
  have hdiff : ∀ᵐ r : ℝ, ∀ z ∈ Metric.ball x 1,
      HasFDerivAt (fun y : Fin n → ℝ => ρ.normed volume r * u (t - r) y)
        (ρ.normed volume r • fderiv ℝ (u (t - r)) z) z := by
    refine Eventually.of_forall fun r z _ => ?_
    exact (((hu.contDiff_section (t - r)).differentiable (by norm_num) z).hasFDerivAt).const_mul _
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z : Fin n → ℝ => fun r : ℝ => ρ.normed volume r * u (t - r) z)
    (F' := fun z : Fin n → ℝ => fun r : ℝ => ρ.normed volume r • fderiv ℝ (u (t - r)) z)
    (bound := fun r : ℝ => ρ.normed volume r * M) (Metric.ball_mem_nhds x one_pos)
    (Eventually.of_forall fun z =>
      (continuous_mollifyTime_integrand hu.continuous ρ t z).aestronglyMeasurable)
    (integrable_mollifyTime_integrand hu.continuous ρ t x)
    (continuous_mollifyTime_fderiv_integrand hu ρ t x).aestronglyMeasurable hbound
    (ρ.integrable_normed.mul_const M) hdiff
/-- The gradient of the time mollification of a `C^{1,2}` function is the time mollification of
its gradient. -/
theorem gradient_mollifyTime (hu : IsC12 u) (ρ : ContDiffBump (0 : ℝ)) (t : ℝ) (x : Fin n → ℝ)
    (i : Fin n) :
    gradient (mollifyTime u ρ) t x i = mollifyTime (fun s y => gradient u s y i) ρ t x := by
  simp only [gradient, (hasFDerivAt_state_mollifyTime hu ρ t x).fderiv]
  rw [ContinuousLinearMap.integral_apply (integrable_mollifyTime_fderiv_integrand hu ρ t x)]
  simp only [mollifyTime, smul_apply, smul_eq_mul]
/-- The state derivative of a gradient coordinate, as a continuous linear functional, is the
coordinate pairing with the corresponding row of the Hessian. -/
theorem fderiv_gradient_eq_sum_hessian (s : ℝ) (z : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (fun y : Fin n → ℝ => gradient u s y i) z
      = ∑ j : Fin n, hessian u s z i j • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) := by
  ext v
  rw [clm_apply_pi_real]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _
/-- The state derivative of a gradient coordinate of a `C^{1,2}` function is jointly continuous
in time and state. -/
theorem continuous_fderiv_gradient (hu : IsC12 u) (i : Fin n) :
    Continuous fun p : ℝ × (Fin n → ℝ) =>
      fderiv ℝ (fun y : Fin n → ℝ => gradient u p.1 y i) p.2 := by
  have h : (fun p : ℝ × (Fin n → ℝ) =>
        fderiv ℝ (fun y : Fin n → ℝ => gradient u p.1 y i) p.2)
      = fun p : ℝ × (Fin n → ℝ) => ∑ j : Fin n, hessian u p.1 p.2 i j •
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) :=
    funext fun p => fderiv_gradient_eq_sum_hessian p.1 p.2 i
  rw [h]
  exact continuous_finsetSum _ fun j _ => (hu.continuous_hessian i j).smul continuous_const
/-- A gradient coordinate of a `C^{1,2}` function is differentiable in the state. -/
theorem differentiable_gradient_state (hu : IsC12 u) (s : ℝ) (i : Fin n) :
    Differentiable ℝ fun y : Fin n → ℝ => gradient u s y i :=
  (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1 : Fin n → ℝ)).differentiable.comp
    (((hu.contDiff_section s).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))
/-- The second-derivative integrand of the time mollification is continuous in the integration
variable. -/
theorem continuous_mollifyTime_hessian_integrand (hu : IsC12 u) (ρ : ContDiffBump (0 : ℝ))
    (t : ℝ) (z : Fin n → ℝ) (i : Fin n) : Continuous fun r : ℝ =>
      ρ.normed volume r • fderiv ℝ (fun y : Fin n → ℝ => gradient u (t - r) y i) z :=
  (ρ.contDiff_normed (n := 0)).continuous.smul
    ((continuous_fderiv_gradient hu i).comp
      ((continuous_const.sub continuous_id).prodMk continuous_const))
/-- The second-derivative integrand of the time mollification is integrable. -/
theorem integrable_mollifyTime_hessian_integrand (hu : IsC12 u) (ρ : ContDiffBump (0 : ℝ))
    (t : ℝ) (z : Fin n → ℝ) (i : Fin n) : Integrable (fun r : ℝ =>
      ρ.normed volume r • fderiv ℝ (fun y : Fin n → ℝ => gradient u (t - r) y i) z) volume :=
  (continuous_mollifyTime_hessian_integrand hu ρ t z i).integrable_of_hasCompactSupport
    ρ.hasCompactSupport_normed.smul_right
/-- The time mollification of a gradient coordinate of a `C^{1,2}` function is differentiable in
the state, with state derivative the integral of the time-mollified second derivatives. -/
theorem hasFDerivAt_state_mollifyTime_gradient (hu : IsC12 u) (ρ : ContDiffBump (0 : ℝ)) (t : ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    HasFDerivAt (mollifyTime (fun s y => gradient u s y i) ρ t)
      (∫ r : ℝ, ρ.normed volume r • fderiv ℝ (fun y : Fin n → ℝ => gradient u (t - r) y i) x)
      x := by
  have hg : Continuous (Function.uncurry fun s (y : Fin n → ℝ) => gradient u s y i) :=
    hu.continuous_gradient i
  obtain ⟨M, hM⟩ := exists_bound_bump_smul ρ (continuous_fderiv_gradient hu i) t x
  have hbound : ∀ᵐ r : ℝ, ∀ z ∈ Metric.ball x 1,
      ‖ρ.normed volume r • fderiv ℝ (fun y : Fin n → ℝ => gradient u (t - r) y i) z‖
        ≤ ρ.normed volume r * M :=
    Eventually.of_forall fun r z hz => hM r z hz
  have hdiff : ∀ᵐ r : ℝ, ∀ z ∈ Metric.ball x 1,
      HasFDerivAt (fun y : Fin n → ℝ => ρ.normed volume r * gradient u (t - r) y i)
        (ρ.normed volume r • fderiv ℝ (fun y : Fin n → ℝ => gradient u (t - r) y i) z) z := by
    refine Eventually.of_forall fun r z _ => ?_
    exact ((differentiable_gradient_state hu (t - r) i z).hasFDerivAt).const_mul _
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z : Fin n → ℝ => fun r : ℝ => ρ.normed volume r * gradient u (t - r) z i)
    (F' := fun z : Fin n → ℝ => fun r : ℝ =>
      ρ.normed volume r • fderiv ℝ (fun y : Fin n → ℝ => gradient u (t - r) y i) z)
    (bound := fun r : ℝ => ρ.normed volume r * M) (Metric.ball_mem_nhds x one_pos)
    (Eventually.of_forall fun z =>
      (continuous_mollifyTime_integrand hg ρ t z).aestronglyMeasurable)
    (integrable_mollifyTime_integrand hg ρ t x)
    (continuous_mollifyTime_hessian_integrand hu ρ t x i).aestronglyMeasurable hbound
    (ρ.integrable_normed.mul_const M) hdiff
/-- The Hessian of the time mollification of a `C^{1,2}` function is the time mollification of
its Hessian. -/
theorem hessian_mollifyTime (hu : IsC12 u) (ρ : ContDiffBump (0 : ℝ)) (t : ℝ) (x : Fin n → ℝ)
    (i j : Fin n) :
    hessian (mollifyTime u ρ) t x i j = mollifyTime (fun s y => hessian u s y i j) ρ t x := by
  have hfun : (fun y : Fin n → ℝ => fderiv ℝ (mollifyTime u ρ t) y (Pi.single i 1))
      = mollifyTime (fun s z => gradient u s z i) ρ t :=
    funext fun y => gradient_mollifyTime hu ρ t y i
  simp only [hessian, hfun, (hasFDerivAt_state_mollifyTime_gradient hu ρ t x i).fderiv]
  rw [ContinuousLinearMap.integral_apply (integrable_mollifyTime_hessian_integrand hu ρ t x i)]
  simp only [mollifyTime, smul_apply, smul_eq_mul, gradient]
end LevyStochCalc.Ito.JumpFormula


